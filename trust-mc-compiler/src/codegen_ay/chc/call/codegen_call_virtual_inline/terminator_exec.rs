// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Terminator routing for the inline body walker.
//! Part of #3913: extracted from walker.rs terminator match.

use ay_bindings::{Expr, Sort};
use rustc_public::CrateDef;
use rustc_public::mir::mono::Instance;
use rustc_public::mir::{LocalDecl, Operand, TerminatorKind};
use rustc_public::rustc_internal;
use rustc_public::ty::{AdtKind, RigidTy, TyKind};
use tracing::debug;

use super::nested_call_fallback::{
    build_nested_call_fallback_expr, is_pointer_destination,
    try_build_valid_collection_backing_fallback,
};

use super::super::ChcCtx;
use super::super::codegen_types::CodegenTypes;
use super::super::inline_body::{
    extract_inline_assert_guard, extract_inline_assume_guard, strip_inline_assert_fallback,
    strip_inline_assume_pruned,
};
use super::super::inline_shared::inline_operand_to_expr;
use super::super::stubs_option_helpers::{OptionHelpers, option_value_sort};
use super::super::ty_signedness;
use super::execution_state::InlineExecutionState;
use super::kani_inline::try_handle_kani_call_inline;
use super::loop_replay::InlineWalkCtx;
use super::nested_call::try_inline_nested_call;
use super::pointer_wrapper::resolve_inline_writeback_target_place;
use super::projected_assign::{apply_inline_projected_assign, try_inline_memory_store};
use super::slice_index_inline::{nested_call_fallback_sort, try_execute_inline_slice_index_call};
use super::switchint::translate_switchint_ite;
use super::vtable_prop::{attach_spawn_task_slot_vtable, propagate_vtable_through_call};
use super::{InlineReturn, MAX_INLINE_DEPTH, virtual_panic_fallback};
use crate::kani_middle::attributes::{self, KaniAttributes};
use crate::kani_middle::kani_functions::{KaniFunction, KaniHook, try_get_kani_function};
use std::collections::HashSet;

/// Loop-control signal returned by `execute_inline_terminator`.
pub(super) enum TerminatorStep {
    /// Continue walking at the given basic block index.
    ContinueAt(usize),
    /// The walk reached a Return or SwitchInt and produced a result.
    Return(Option<InlineReturn>),
}

/// Execute one MIR terminator inside an inline body walk.
pub(super) fn execute_inline_terminator<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    walk_ctx: &InlineWalkCtx<'_>,
    state: &mut InlineExecutionState,
    current_bb: usize,
    switchint_depth: usize,
    inline_depth: usize,
) -> TerminatorStep {
    let block = &walk_ctx.body.blocks[current_bb];
    match &block.terminator.kind {
        TerminatorKind::Return => TerminatorStep::Return(state.finish_return(ctx, walk_ctx)),
        TerminatorKind::Goto { target } => TerminatorStep::ContinueAt(*target),
        TerminatorKind::Assert { cond, expected, target, msg, .. } => {
            // Coroutine resume wrappers encode the "resumed after panicking"
            // path as `assert(false) -> [success: same_bb]`. Treat that as a
            // diverging panic path instead of replaying a synthetic self-loop.
            if *target == current_bb {
                debug!(
                    bb_idx = walk_ctx.bb_idx,
                    current_bb,
                    expected,
                    ?cond,
                    "virtual body: self-target Assert -> panic fallback"
                );
                return TerminatorStep::Return(virtual_panic_fallback(ctx, walk_ctx));
            }
            execute_inline_assert(ctx, walk_ctx, state, cond, *expected, *target, msg)
        }
        TerminatorKind::Call { func, args, destination, target: Some(target_bb), .. } => {
            execute_inline_call(
                ctx,
                walk_ctx,
                state,
                func,
                args,
                destination,
                *target_bb,
                current_bb,
                inline_depth,
            )
        }
        TerminatorKind::Call { func, target: None, .. } => {
            execute_diverging_call(ctx, walk_ctx, func, current_bb)
        }
        TerminatorKind::SwitchInt { discr, targets } => {
            TerminatorStep::Return(translate_switchint_ite(
                ctx,
                walk_ctx,
                discr,
                targets,
                std::mem::take(&mut state.local_exprs),
                std::mem::take(&mut state.inline_vtable_ids),
                std::mem::take(&mut state.inline_alloc_ids),
                std::mem::take(&mut state.modified_locals),
                std::mem::take(&mut state.assume_guards),
                std::mem::take(&mut state.assert_guards),
                std::mem::take(&mut state.deferred_checks),
                current_bb,
                switchint_depth,
                inline_depth,
            ))
        }
        TerminatorKind::Drop { place, target, .. } => {
            match super::inline_drop::try_handle_inline_drop(
                ctx,
                walk_ctx,
                &state.local_exprs,
                &state.inline_vtable_ids,
                &state.inline_alloc_ids,
                place,
                inline_depth,
            ) {
                Some(success_guard) => {
                    if !matches!(success_guard.value(), ay_bindings::ExprValue::BoolConst(true)) {
                        // Side-channel + value channel (see execute_inline_assert).
                        // MemorySafety/None matches how the ITE lane surfaces
                        // this guard today (emit_error_rule_for_condition).
                        state.record_deferred_check(
                            trust_mc_core::violation::PropertyKind::MemorySafety,
                            None,
                            success_guard.clone(),
                        );
                        state.record_assert_guard(success_guard);
                    }
                    TerminatorStep::ContinueAt(*target)
                }
                None => TerminatorStep::Return(None),
            }
        }
        // Part of #3889: Unreachable is a dead branch (e.g., otherwise arm of
        // a SwitchInt on a 2-variant enum discriminant). Return None to signal
        // the SwitchInt merger that this branch is dead and should be skipped.
        TerminatorKind::Unreachable => {
            debug!(bb_idx = walk_ctx.bb_idx, current_bb, "virtual body: Unreachable (dead branch)");
            TerminatorStep::Return(None)
        }
        _ => {
            debug!(bb_idx = walk_ctx.bb_idx, ?current_bb, "virtual body: unsupported terminator");
            TerminatorStep::Return(None)
        }
    }
}

/// Handle Assert terminators.
fn execute_inline_assert<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    walk_ctx: &InlineWalkCtx<'_>,
    state: &mut InlineExecutionState,
    cond: &rustc_public::mir::Operand,
    expected: bool,
    target: usize,
    msg: &rustc_public::mir::AssertMessage,
) -> TerminatorStep {
    let resolver = walk_ctx.resolver;
    match inline_operand_to_expr(ctx, cond, &state.local_exprs, &resolver, walk_ctx.locals) {
        Some(cond_expr) => {
            let bool_cond = if cond_expr.sort().is_bool() {
                cond_expr
            } else if let Some(w) = cond_expr.sort().bitvec_width() {
                cond_expr.eq(Expr::bitvec_const(0u64, w)).not()
            } else {
                return TerminatorStep::Return(None);
            };
            let guard = if expected { bool_cond } else { bool_cond.not() };
            // Assert-guard SIDE-CHANNEL: carry the check to the host with
            // Kani-parity kind/description, independent of the return-value
            // ITE (which unit/discarded destinations drop).
            let (kind, message) =
                crate::codegen_ay::chc::expr::codegen_expr_assert::mir_assert_kind_and_message(msg);
            state.record_deferred_check(kind, message, guard.clone());
            state.record_assert_guard(guard);
            TerminatorStep::ContinueAt(target)
        }
        None => {
            // Part of #4014: When an Assert condition references a local that
            // was silently skipped (e.g., CheckedAdd result on a deref through
            // a static-mut pointer with width mismatch), assume the assertion
            // passes and continue rather than bailing the entire inline walk.
            // This is sound because:
            // - MIR assertions are safety checks (overflow, null, bounds)
            // - Bailing loses ALL return-value information → unconstrained fallback
            // - Assuming pass preserves the return-value computation
            // - The outer CHC encoding independently verifies correctness
            debug!(
                bb_idx = walk_ctx.bb_idx,
                "virtual body: Assert condition untranslatable, assuming pass (#4014)"
            );
            TerminatorStep::ContinueAt(target)
        }
    }
}

/// Handle Call terminators with a target (non-diverging calls).
fn execute_inline_call<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    walk_ctx: &InlineWalkCtx<'_>,
    state: &mut InlineExecutionState,
    func: &rustc_public::mir::Operand,
    args: &[rustc_public::mir::Operand],
    destination: &rustc_public::mir::Place,
    target_bb: usize,
    current_bb: usize,
    inline_depth: usize,
) -> TerminatorStep {
    let resolver = walk_ctx.resolver;
    if let Some(kani_result) = try_handle_kani_call_inline(
        ctx,
        func,
        args,
        walk_ctx.body,
        walk_ctx.locals,
        destination.local,
        &mut state.local_exprs,
        &resolver,
        &mut state.assume_guards,
        &mut state.assert_guards,
        &mut state.deferred_checks,
        current_bb,
    ) {
        if apply_inline_writeback(ctx, walk_ctx, state, destination, kani_result) {
            return TerminatorStep::ContinueAt(target_bb);
        }
        debug!(
            bb_idx = walk_ctx.bb_idx,
            local = destination.local,
            "virtual body: call destination write-back cannot be tracked"
        );
        return TerminatorStep::Return(None);
    }

    // Part of #4023: Try atomic operation dispatch (fetch_add, load, store, etc.).
    // Handles atomic calls inside inlined Drop bodies that use AtomicUsize for
    // side-effect counting. Without this, the atomic counter is never updated and
    // assertions on the counter fail with CTREX(Genuine).
    if let Some(atomic_result) = super::atomic_inline::try_handle_atomic_call_inline(
        ctx,
        func,
        args,
        walk_ctx.locals,
        &state.local_exprs,
        &resolver,
    ) {
        if apply_inline_writeback(ctx, walk_ctx, state, destination, atomic_result) {
            return TerminatorStep::ContinueAt(target_bb);
        }
        debug!(
            bb_idx = walk_ctx.bb_idx,
            local = destination.local,
            "virtual body: atomic call destination write-back cannot be tracked"
        );
        return TerminatorStep::Return(None);
    }

    if let Some(step) = try_execute_inline_slice_index_call(
        ctx,
        walk_ctx,
        state,
        func,
        args,
        destination,
        target_bb,
        current_bb,
    ) {
        return step;
    }

    if let Some(mut result) = try_inline_nested_call(
        ctx,
        func,
        args,
        walk_ctx.body,
        &state.local_exprs,
        &walk_ctx.resolver,
        &state.inline_vtable_ids,
        &state.inline_alloc_ids,
        destination,
        inline_depth,
    ) {
        let callee_path = resolve_inline_callee_path(ctx, func, walk_ctx.locals);
        attach_spawn_task_slot_vtable(
            ctx,
            callee_path.as_deref(),
            destination,
            walk_ctx.body,
            &mut result,
        );
        if let Some(guard) = extract_inline_assert_guard(&result.value) {
            state.record_assert_guard(guard);
        }
        // Assert-guard SIDE-CHANNEL: absorb the nested walk's accumulated
        // checks into this walk segment (weakened by the current outer assume
        // conjunction). This is the propagation lane that survives even when
        // the value-channel ITE above is dropped by the destination shape.
        state.absorb_nested_deferred_checks(std::mem::take(&mut result.deferred_checks));
        if let Some(guard) = extract_inline_assume_guard(&result.value) {
            state.assume_guards.push(guard);
        }
        let writeback_value =
            strip_inline_assert_fallback(&result.value).unwrap_or_else(|| result.value.clone());
        let writeback_value =
            strip_inline_assume_pruned(&writeback_value).unwrap_or(writeback_value);
        let writeback_alloc_id = result.alloc_id;
        let projected_dest = !destination.projection.is_empty();
        if !apply_inline_writeback_with_alloc_id(
            ctx,
            walk_ctx,
            state,
            destination,
            writeback_value.clone(),
            writeback_alloc_id,
        ) {
            debug!(
                bb_idx = walk_ctx.bb_idx,
                local = destination.local,
                "virtual body: nested call destination write-back cannot be tracked"
            );
            return TerminatorStep::Return(None);
        }
        if !projected_dest {
            // Part of #4163: Seed subslice_len when callee is slice_from_raw_parts.
            if let Some(ref path) = callee_path {
                // Raw-alloc route: a NESTED `slice::from_raw_parts` (inside an
                // inlined callee body) forms a reference — a read of all `len`
                // elements — but the call-site uninit-formation check is only
                // emitted for harness-level calls (`codegen_call_fn_inline`).
                // Fail-close here so a PROOF cannot rest on the missing check.
                if ctx.uninit_checks
                    && crate::codegen_ay::chc::call::codegen_call_kani_model_mem_init::is_slice_from_raw_parts_ref_former(path)
                {
                    ctx.record_sound_fallback_reason("nested_from_raw_parts_uninit_unchecked");
                }
                let is_slice_from_raw = path.contains("slice_from_raw_parts")
                    || (path.contains("from_raw_parts") && path.contains("ptr"));
                if is_slice_from_raw && args.len() >= 2 {
                    if let Some(len_expr) = inline_operand_to_expr(
                        ctx,
                        &args[1],
                        &state.local_exprs,
                        &walk_ctx.resolver,
                        walk_ctx.locals,
                    ) {
                        ctx.ref_resolution.subslice_len.insert(destination.local, len_expr);
                        debug!(
                            dest = destination.local,
                            %path,
                            "nested call: seeded subslice_len from slice_from_raw_parts"
                        );
                    }
                }
            }
            propagate_vtable_through_call(
                args,
                destination.local,
                &writeback_value,
                &mut state.inline_vtable_ids,
            );
            if let Some(vtable) = result.vtable {
                state.inline_vtable_ids.insert(destination.local, vtable);
            }
        }
        for (&callee_arg_local, update_expr) in &result.alias_updates {
            let arg_idx = match callee_arg_local.checked_sub(1) {
                Some(idx) => idx,
                None => continue,
            };
            let Some(
                rustc_public::mir::Operand::Copy(place) | rustc_public::mir::Operand::Move(place),
            ) = args.get(arg_idx)
            else {
                continue;
            };
            let update_expr =
                strip_inline_assert_fallback(update_expr).unwrap_or_else(|| update_expr.clone());
            let update_expr = strip_inline_assume_pruned(&update_expr).unwrap_or(update_expr);
            if !apply_inline_writeback(ctx, walk_ctx, state, place, update_expr) {
                debug!(
                    bb_idx = walk_ctx.bb_idx,
                    callee_arg_local,
                    local = place.local,
                    projection = ?place.projection,
                    "virtual body: nested call alias update write-back cannot be tracked"
                );
                // P2 S3 Stage A (honesty-only): under a register_contract
                // frame, this silently-dropped alias update is
                // contract-visible state the ensures/check closure will read
                // — a counterexample built on the stale value is fabricated
                // and would report as Genuine. Book a DEMOTING fallback so
                // the verdict is an honest UNDETERMINED instead. Outside
                // contract frames, behavior is unchanged.
                if ctx.register_contract_walk_depth > 0 {
                    ctx.record_fallback();
                }
            }
        }
        return TerminatorStep::ContinueAt(target_bb);
    }

    let callee_path = resolve_inline_callee_path(ctx, func, walk_ctx.locals);
    if let Some((dest_ty, dest_sort)) =
        resolve_inline_destination_ty_and_sort(ctx, walk_ctx, destination)
    {
        if let Some(constructor) = detect_nonzero_constructor_path(callee_path.as_deref())
            && let Some(arg) = args.first()
            && let Some(payload) = inline_operand_to_expr(
                ctx,
                arg,
                &state.local_exprs,
                &walk_ctx.resolver,
                walk_ctx.locals,
            )
            && let Some(rebuilt) =
                inline_nonzero_constructor_writeback(ctx, constructor, payload, dest_ty, &dest_sort)
        {
            if apply_inline_writeback(ctx, walk_ctx, state, destination, rebuilt) {
                return TerminatorStep::ContinueAt(target_bb);
            }
        }

        // Part of #3903: sound over-approximation — unconstrained result.
        debug!(
            current_bb,
            ?callee_path,
            local = destination.local,
            "walker: nested call fallback to fresh symbolic var"
        );
        let gap_reason = callee_path
            .as_deref()
            .map_or("inline_nested_call_fallback_symbolic".to_string(), |cp| {
                format!("inline_nested_call_fallback_symbolic@{cp}")
            });
        ctx.record_aggregate_gap(&gap_reason);
        // Fail-close (contract-check havoc): when this fallback fires because
        // MAX_INLINE_DEPTH is exhausted, the callee's entire body — including
        // any kani::assert / contract-ensures check inside it — is replaced by
        // one unconstrained fresh var. The lost check guards would have ridden
        // the return-value ITE, which unit destinations discard, so a violated
        // postcondition can silently prove. `record_aggregate_gap` alone is a
        // non-demoting SOUND_APPROXIMATION category; additionally book a
        // DEMOTING fallback whenever the havocked callee (transitively)
        // contains check sites, so the driver demotes any resulting PROOF.
        // Scoped to the depth-exhaustion lane only: at
        // `inline_depth >= MAX_INLINE_DEPTH` the walker refuses every body
        // (walker.rs prepare_inline_walk depth guard on inline_depth + 1).
        if inline_depth >= MAX_INLINE_DEPTH
            && nested_fallback_callee_contains_check_sites(ctx, func, walk_ctx.locals)
        {
            debug!(
                current_bb,
                ?callee_path,
                inline_depth,
                "walker: depth-exhausted nested-call havoc drops check sites -> demoting fallback"
            );
            ctx.record_fallback();
        }
        // Part of #3945/#4050: prefer payload/pointee sorts for fallback.
        let effective_sort = nested_call_fallback_sort(
            ctx,
            walk_ctx,
            destination,
            callee_path.as_deref(),
            dest_sort,
        );
        // Over-approximated collection constructors (`<[T]>::into_vec`,
        // `bounded_any`, …) return a Vec whose backing IS a valid heap
        // allocation. Give it a valid, 8-aligned provenance so a later
        // `Vec::drop` dealloc-validity check does not fail spuriously — SOUND
        // because it is gated on provably-allocating constructors and a Vec
        // from raw/unsafe parts keeps its arbitrary pointer.
        let is_pointer_dest = is_pointer_destination(ctx, walk_ctx, destination);
        let fallback_var =
            try_build_valid_collection_backing_fallback(ctx, &effective_sort, callee_path.as_deref())
                .unwrap_or_else(|| {
                    build_nested_call_fallback_expr(effective_sort, is_pointer_dest)
                });
        if apply_inline_writeback(ctx, walk_ctx, state, destination, fallback_var) {
            return TerminatorStep::ContinueAt(target_bb);
        }
        debug!(
            current_bb,
            local = destination.local,
            "walker: nested call fallback write-back failed, bailing"
        );
        return TerminatorStep::Return(None);
    }

    let callee_path = resolve_inline_callee_path(ctx, func, walk_ctx.locals);
    debug!(current_bb, ?callee_path, "walker bail: nested call inlining failed");
    TerminatorStep::Return(None)
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum NonZeroConstructor {
    New,
    NewUnchecked,
}

fn detect_nonzero_constructor_path(callee_path: Option<&str>) -> Option<NonZeroConstructor> {
    let path = callee_path?;
    if !(path.contains("NonZero") || path.contains("nonzero")) {
        return None;
    }
    match path.rsplit("::").next()? {
        "new" => Some(NonZeroConstructor::New),
        "new_unchecked" => Some(NonZeroConstructor::NewUnchecked),
        _ => None,
    }
}

fn expr_is_nonzero(value: &Expr) -> Option<Expr> {
    if let Some(width) = value.sort().bitvec_width() {
        Some(value.clone().ne(Expr::bitvec_const(0u64, width)))
    } else if value.sort().is_int() {
        Some(value.clone().ne(Expr::int_const(0)))
    } else {
        None
    }
}

fn option_payload_signedness(ty: rustc_public::ty::Ty) -> bool {
    if let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind()
        && def.kind() == AdtKind::Enum
    {
        for variant in def.variants() {
            if let Some(field) = variant.fields().first() {
                return ty_signedness(field.ty_with_args(&args)).unwrap_or(false);
            }
        }
    }
    ty_signedness(ty).unwrap_or(false)
}

fn coerce_nonzero_payload_to_sort<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    payload: Expr,
    target_sort: &Sort,
    signed: bool,
) -> Option<Expr> {
    if payload.sort() == target_sort {
        return Some(payload);
    }
    if payload.sort().is_bitvec() && target_sort.is_datatype() {
        let rebuilt =
            crate::codegen_ay::types::unflatten_bitvec_to_datatype(&payload, target_sort)?;
        ctx.declare_datatype_sort_if_needed(target_sort);
        return Some(rebuilt);
    }
    ctx.coerce_value_to_sort(payload, target_sort, signed)
}

fn resolve_inline_destination_ty_and_sort<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    walk_ctx: &InlineWalkCtx<'_>,
    destination: &rustc_public::mir::Place,
) -> Option<(rustc_public::ty::Ty, Sort)> {
    let ty = ctx
        .resolve_inline_local_ty(walk_ctx.body, destination.local)
        .or_else(|| destination.ty(walk_ctx.locals).ok().map(|ty| ctx.resolve_body_ty(ty)))?;
    let sort = ChcCtx::translate_ty(ty)?;
    Some((ty, sort))
}

fn inline_nonzero_constructor_writeback<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    constructor: NonZeroConstructor,
    payload: Expr,
    dest_ty: rustc_public::ty::Ty,
    dest_sort: &Sort,
) -> Option<Expr> {
    if constructor == NonZeroConstructor::NewUnchecked {
        if dest_sort.is_datatype() {
            let rebuilt =
                crate::codegen_ay::types::unflatten_bitvec_to_datatype(&payload, dest_sort)?;
            ctx.declare_datatype_sort_if_needed(dest_sort);
            return Some(rebuilt);
        }
        return ctx.coerce_value_to_sort(payload, dest_sort, ty_signedness(dest_ty)?);
    }

    if !dest_sort.is_datatype() {
        return None;
    }
    let is_some = expr_is_nonzero(&payload)?;
    let payload_sort = option_value_sort(dest_sort)?;
    let payload = coerce_nonzero_payload_to_sort(
        ctx,
        payload,
        &payload_sort,
        option_payload_signedness(dest_ty),
    )?;
    let some_expr = ctx.make_some_expr_for_option(payload, dest_sort)?;
    let none_expr = ctx.make_none_expr_for_option(dest_sort)?;
    ctx.declare_datatype_sort_if_needed(dest_sort);
    Some(Expr::ite(is_some, some_expr, none_expr))
}

pub(super) fn apply_inline_writeback<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    walk_ctx: &InlineWalkCtx<'_>,
    state: &mut InlineExecutionState,
    place: &rustc_public::mir::Place,
    value: Expr,
) -> bool {
    apply_inline_writeback_with_alloc_id(ctx, walk_ctx, state, place, value, None)
}

fn apply_inline_writeback_with_alloc_id<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    walk_ctx: &InlineWalkCtx<'_>,
    state: &mut InlineExecutionState,
    place: &rustc_public::mir::Place,
    mut value: Expr,
    alloc_id: Option<u32>,
) -> bool {
    if place.projection.is_empty()
        && value.sort().is_bitvec()
        && let Some(dest_sort) = ctx
            .resolve_inline_local_ty(walk_ctx.body, place.local)
            .and_then(ChcCtx::translate_ty)
            .or_else(|| {
                place
                    .ty(walk_ctx.locals)
                    .ok()
                    .and_then(|ty| ChcCtx::translate_ty(ctx.resolve_body_ty(ty)))
            })
        && dest_sort.is_datatype()
        && let Some(rebuilt) =
            crate::codegen_ay::types::unflatten_bitvec_to_datatype(&value, &dest_sort)
    {
        ctx.declare_datatype_sort_if_needed(&dest_sort);
        value = rebuilt;
    }

    let retarget_place = resolve_inline_writeback_target_place(ctx, walk_ctx, place, &value)
        .unwrap_or_else(|| place.clone());

    if let Some(updated) = apply_inline_projected_assign(
        ctx,
        walk_ctx.locals,
        &state.local_exprs,
        &retarget_place,
        value.clone(),
    ) {
        if retarget_place.projection.is_empty() {
            state.write_local_with_alloc_id(retarget_place.local, updated, alloc_id);
        } else {
            state.write_local(retarget_place.local, updated);
        }
        return true;
    }
    try_inline_memory_store(ctx, walk_ctx.locals, &state.local_exprs, &retarget_place, value, None)
}

/// Handle diverging Call terminators (no target).
fn execute_diverging_call<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    walk_ctx: &InlineWalkCtx<'_>,
    func: &rustc_public::mir::Operand,
    current_bb: usize,
) -> TerminatorStep {
    let Some(path) = resolve_inline_callee_path(ctx, func, walk_ctx.locals) else {
        return TerminatorStep::Return(None);
    };
    if ChcCtx::is_formatting_path(&path) {
        debug!(bb_idx = walk_ctx.bb_idx, ?current_bb, %path, "diverging: panic/formatting fallback");
        return TerminatorStep::Return(virtual_panic_fallback(ctx, walk_ctx));
    }
    debug!(bb_idx = walk_ctx.bb_idx, ?current_bb, %path, "diverging: unsupported call");
    TerminatorStep::Return(None)
}

pub(super) fn resolve_inline_callee_path(
    ctx: &ChcCtx<'_, '_>,
    func: &Operand,
    locals: &[LocalDecl],
) -> Option<String> {
    let func_ty = func.ty(locals).ok()?;
    let (fn_def, fn_args) = match func_ty.kind() {
        TyKind::RigidTy(RigidTy::FnDef(def, args)) => (def, args),
        _ => return None,
    };

    let instance_opt = Instance::resolve(fn_def, &fn_args).ok();
    let def_id =
        instance_opt.as_ref().map_or_else(|| fn_def.def_id(), |instance| instance.def.def_id());
    let internal_def_id = rustc_internal::internal(ctx.tcx, def_id);
    Some(ctx.tcx.def_path_str(internal_def_id))
}

/// Bounded recursion depth for the check-site scan below. The `visited` set
/// already caps total work (each monomorphic instance is scanned once); the
/// depth bound only guards against degenerate deep call chains.
const CHECK_SITE_SCAN_MAX_DEPTH: usize = 6;

/// Fail-close helper for the depth-exhaustion nested-call havoc (contract
/// postcondition false-Safe): does the callee that is about to be replaced by
/// a fresh symbolic var (transitively) contain check sites?
///
/// Contract check sites are:
/// - contract machinery closures — `{closure#..}` chains whose enclosing
///   function item carries kani contract instrumentation attributes
///   (the ensures/requires check expansion lives in those closures);
/// - calls to kani assert/check hooks (by `kanitool::fn_marker` or by
///   `kani::` path).
///
/// Deliberately excluded are ordinary MIR `Assert` terminators and core/std
/// panic machinery: they are pervasive in standard-library value plumbing and
/// over-demoted zero-length/ZST array shapes. Body-less or unresolved leaves
/// likewise do not count as contract machinery; the generic assert-guard
/// side-channel owns those broader gaps.
fn nested_fallback_callee_contains_check_sites(
    ctx: &ChcCtx<'_, '_>,
    func: &Operand,
    locals: &[LocalDecl],
) -> bool {
    // NARROW scope (see body_contains_check_sites): only contract machinery
    // and direct kani assert/check hooks count. Unresolvable callees are NOT
    // fail-closed — contract closures always resolve in practice (they were
    // walked at shallower depths of the same chain), and fail-closing here
    // demoted canonical std shapes.
    let Ok(raw_func_ty) = func.ty(locals) else {
        return false;
    };
    let func_ty = ctx.resolve_body_ty(raw_func_ty);
    let (fn_def, fn_args) = match func_ty.kind() {
        TyKind::RigidTy(RigidTy::FnDef(def, args)) => (def, args),
        _ => match raw_func_ty.kind() {
            TyKind::RigidTy(RigidTy::FnDef(def, args)) => (def, args),
            _ => return false,
        },
    };
    let mut visited = HashSet::new();
    if let Ok(instance) = Instance::resolve(fn_def, &fn_args) {
        return instance_contains_check_sites(ctx, instance, &mut visited, 0);
    }
    // Deep inline chains cannot always bind generic args (`resolve_body_ty`
    // normalizes against the outer instance only), so `Instance::resolve` can
    // fail for perfectly ordinary std machinery (e.g. the array-iter
    // `partial_drop` with an unbound `T`). Inspect the polymorphic FnDef.
    if is_contract_machinery_def(ctx, fn_def.def_id()) {
        return true;
    }
    // Polymorphic FnDef fallback: `Instance::resolve` failed above, so there
    // is no monomorphic instance to key the transform-pipeline cache with —
    // the transformed-body route (`walker_transformed_body`) is structurally
    // unavailable here. Scanning the RAW polymorphic body is acceptable for
    // this demotion decision: raw bodies retain ALL contract closures
    // (including ones the transform would clear), so a raw scan can only
    // over-detect check sites (over-demote), never under-detect.
    match fn_def.body() {
        Some(body) => body_contains_check_sites(ctx, &body, &mut visited, 0),
        None => false,
    }
}

/// Resolve a call operand to a monomorphic instance, mirroring
/// `nested_call::resolve_inline_callee` (body-ty normalization with a raw
/// FnDef fallback, Part of #4161).
fn resolve_check_scan_instance(
    ctx: &ChcCtx<'_, '_>,
    func: &Operand,
    locals: &[LocalDecl],
) -> Option<Instance> {
    let raw_func_ty = func.ty(locals).ok()?;
    let func_ty = ctx.resolve_body_ty(raw_func_ty);
    let (fn_def, fn_args) = match func_ty.kind() {
        TyKind::RigidTy(RigidTy::FnDef(def, args)) => (def, args),
        _ => match raw_func_ty.kind() {
            TyKind::RigidTy(RigidTy::FnDef(def, args)) => (def, args),
            _ => return None,
        },
    };
    Instance::resolve(fn_def, &fn_args).ok()
}

/// Recursive worker for `nested_fallback_callee_contains_check_sites`.
///
/// Body-less callees (including the havocked root and transitive intrinsic or
/// extern leaves) do not carry contract machinery; marker/path signals are
/// inspected at each call site before recursion.
fn instance_contains_check_sites(
    ctx: &ChcCtx<'_, '_>,
    instance: Instance,
    visited: &mut HashSet<String>,
    depth: usize,
) -> bool {
    if depth > CHECK_SITE_SCAN_MAX_DEPTH {
        return false;
    }
    if !visited.insert(instance.mangled_name()) {
        return false;
    }
    // (a) Contract machinery closure: the ensures/requires expansion lives in
    // closures nested under the contracted fn. Detect it structurally so the
    // demotion holds even when the kani::assert call sits one closure deeper.
    if is_contract_machinery_def(ctx, instance.def.def_id()) {
        return true;
    }
    // Scan the TRANSFORMED body when available (the walk lane now walks
    // transformed bodies, so the demotion decision must see the same shapes),
    // falling back to the raw body when the transform fails — a raw scan can
    // only over-detect (unused contract closures are still populated there),
    // never under-detect, so the fallback keeps the demotion decision at least
    // as strong as before.
    let Some(body) = crate::kani_middle::transform::walker_transformed_body(ctx.tcx, instance)
        .or_else(|| instance.body())
    else {
        // Body-less leaves (intrinsics, extern fns) carry no contract
        // machinery. Losing a PLAIN assert inside an unretrievable body is
        // the pre-existing generic deep-inline gap (guard side-channel work),
        // not this demotion's scope — fail-closing here demoted canonical
        // std shapes (zero-len/ZST array compares).
        return false;
    };
    body_contains_check_sites(ctx, &body, visited, depth)
}

/// Scan one MIR body for CONTRACT check sites: direct kani assert/check hook
/// calls and (transitively) contract-machinery callees. Deliberately NARROW —
/// plain `Assert` terminators (overflow/bounds) and core panicking paths are
/// pervasive in std machinery and over-fired the demotion on ordinary value
/// shapes (zero-len/ZST array compares); losing those at inline depth is the
/// pre-existing generic gap tracked for the assert-guard side-channel, while
/// THIS demotion exists to keep contract requires/ensures checks from being
/// silently swallowed (the assert-postconditions false Safe).
fn body_contains_check_sites(
    ctx: &ChcCtx<'_, '_>,
    body: &rustc_public::mir::Body,
    visited: &mut HashSet<String>,
    depth: usize,
) -> bool {
    for block in &body.blocks {
        if let TerminatorKind::Call { func: callee_op, .. } = &block.terminator.kind {
            if call_is_check_machinery(ctx, callee_op, body.locals()) {
                return true;
            }
            if let Some(callee) = resolve_check_scan_instance(ctx, callee_op, body.locals())
                && instance_contains_check_sites(ctx, callee, visited, depth + 1)
            {
                return true;
            }
        }
    }
    false
}

/// Is this closure (chain) generated under a function that carries kani
/// contract instrumentation attributes (`kanitool::checked_with` et al.)?
fn is_contract_machinery_def(ctx: &ChcCtx<'_, '_>, def_id: rustc_public::DefId) -> bool {
    let mut internal_def_id = rustc_internal::internal(ctx.tcx, def_id);
    if !ctx.tcx.is_closure_like(internal_def_id) {
        return false;
    }
    while ctx.tcx.is_closure_like(internal_def_id) {
        let Some(parent) = ctx.tcx.opt_parent(internal_def_id) else {
            return false;
        };
        internal_def_id = parent;
    }
    KaniAttributes::for_item(ctx.tcx, internal_def_id).has_contract()
}

/// Does this call operand target kani assert/check machinery, identified by a
/// marker or an unmarked `kani::` path?
fn call_is_check_machinery(ctx: &ChcCtx<'_, '_>, func: &Operand, locals: &[LocalDecl]) -> bool {
    let Ok(raw_func_ty) = func.ty(locals) else {
        return false;
    };
    let func_ty = ctx.resolve_body_ty(raw_func_ty);
    let (fn_def, fn_args) = match func_ty.kind() {
        TyKind::RigidTy(RigidTy::FnDef(def, args)) => (def, args),
        _ => match raw_func_ty.kind() {
            TyKind::RigidTy(RigidTy::FnDef(def, args)) => (def, args),
            _ => return false,
        },
    };
    let instance = Instance::resolve(fn_def, &fn_args).ok();
    let fn_marker = instance
        .as_ref()
        .and_then(|inst| attributes::fn_marker(inst.def))
        .or_else(|| attributes::fn_marker(fn_def));
    if let Some(fn_marker) = fn_marker
        && matches!(
            try_get_kani_function(&fn_marker),
            Some(KaniFunction::Hook(KaniHook::Assert | KaniHook::Check))
        )
    {
        return true;
    }
    // Unmarked kani::assert/check entry points by path. Core/std panicking
    // paths are deliberately NOT matched (see body_contains_check_sites —
    // they over-fire on ordinary std machinery).
    let def_id =
        instance.as_ref().map_or_else(|| fn_def.def_id(), |instance| instance.def.def_id());
    let internal_def_id = rustc_internal::internal(ctx.tcx, def_id);
    let path = ctx.tcx.def_path_str(internal_def_id);
    let tail = path.rsplit("::").next().unwrap_or(&path);
    path.contains("kani::") && matches!(tail, "assert" | "check")
}
