// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Terminator routing for the inline body walker.
//! Part of #3913: extracted from walker.rs terminator match.

use crate::callee_body::CalleeBody;
use crate::codegen_ay::shared::mono_ty;
#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
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
use super::slice_index_inline::{nested_call_fallback_sort, try_execute_inline_slice_index_call};
use super::switchint::translate_switchint_ite;
use super::vtable_prop::{attach_spawn_task_slot_vtable, propagate_vtable_through_call};
use super::{InlineReturn, MAX_INLINE_DEPTH, virtual_panic_fallback};
use crate::kani_middle::attributes::{self, KaniAttributes};
use crate::kani_middle::kani_functions::{KaniFunction, KaniHook, try_get_kani_function};
use std::collections::{HashMap, HashSet};

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
    // The walked terminator's memory writes form their own heap view group.
    ctx.heap_state.view_ledger.next_terminator();
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
                return TerminatorStep::Return(diverged_path_return(ctx, walk_ctx, state));
            }
            execute_inline_assert(ctx, walk_ctx, state, cond, *expected, *target, msg)
        }
        TerminatorKind::Call { func, args, destination, target: Some(target_bb), .. } => {
            let fresh_native_dyn = if destination.projection.is_empty() {
                ctx.begin_native_dyn_return(walk_ctx.locals, destination.local)
            } else {
                ctx.native_dyn_carrier_write(walk_ctx.locals, destination);
                false
            };
            if !super::statement_exec::place_writes_through_deref(destination) {
                ctx.note_inline_mut_ref_assignment(walk_ctx.body, destination.local, None);
            }
            if destination.projection.is_empty()
                && super::super::inline_walk_guard::local_is_reference(
                    ctx,
                    walk_ctx.locals,
                    destination.local,
                )
            {
                // The returned term has no positive referent-value tag at this
                // boundary. Never reuse an earlier assignment's authority.
                ctx.forget_inline_walk_referent_local(destination.local);
            }
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
                fresh_native_dyn,
            )
        }
        TerminatorKind::Call { func, args, target: None, .. } => {
            execute_diverging_call(ctx, walk_ctx, state, func, args, current_bb)
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
                std::mem::take(&mut state.memory_written_args),
                current_bb,
                switchint_depth,
                inline_depth,
            ))
        }
        TerminatorKind::Drop { place, target, .. } => {
            // Entries a walked drop body parks for this drop (see
            // `ChcCtx::inline_drop_deferred_checks`): exactly those added past
            // this mark, so a nested drop inside the drop body keeps its own.
            let drop_checks_mark = ctx.inline_drop_deferred_checks.len();
            let drop_outcome = super::inline_drop::try_handle_inline_drop(
                ctx,
                walk_ctx,
                &state.local_exprs,
                &state.inline_vtable_ids,
                &state.inline_alloc_ids,
                place,
                inline_depth,
            );
            let drop_checks = ctx
                .inline_drop_deferred_checks
                .split_off(drop_checks_mark.min(ctx.inline_drop_deferred_checks.len()));
            match drop_outcome {
                Some(success_guard) => {
                    state.absorb_nested_deferred_checks(drop_checks);
                    if !matches!(success_guard.value(), ay_bindings::ExprValue::BoolConst(true)) {
                        // Side-channel + value channel (see execute_inline_assert).
                        // MemorySafety/None matches how the ITE lane surfaces
                        // this guard today (emit_error_rule_for_condition).
                        state.record_deferred_check(
                            trust_mc_core::violation::PropertyKind::MemorySafety,
                            None,
                            success_guard.clone(),
                            ctx.heap_state.write_mark(),
                        );
                        state.record_assert_guard(success_guard);
                    }
                    TerminatorStep::ContinueAt(*target)
                }
                None => TerminatorStep::Return(None),
            }
        }
        // An `Unreachable` the walk REACHES is Kani's "unreachable code"
        // failure on this path, exactly: `core::intrinsics::unreachable()`
        // lowers to it. The path fails (`false` under its condition, which
        // `record_deferred_check` and the SwitchInt merges add) and ends as a
        // panic's does. The dead `otherwise` arm of an exhaustive enum `match`
        // (#3889) is filtered before the walk (`switchint.rs`
        // `is_unreachable_block`) and kept dead here. This used to return
        // `None` as "a dead
        // branch", which the enclosing arm turned into a blessed havoc, and
        // the failure was gone (walker_unreachable_terminator_dual.rs).
        TerminatorKind::Unreachable => {
            // No encodable value reaches the `otherwise` of an exhaustive
            // `match` on a data-carrying enum
            // (`obligation_free_walk::enum_exhaustive_unreachable_blocks`):
            // a dead branch, as before. A fieldless enum's is not exempt.
            if crate::codegen_ay::obligation_free_walk::enum_exhaustive_unreachable_blocks(
                walk_ctx.body,
            )
            .contains(&current_bb)
            {
                debug!(
                    bb_idx = walk_ctx.bb_idx,
                    current_bb, "virtual body: Unreachable (dead enum arm)"
                );
                return TerminatorStep::Return(None);
            }
            debug!(
                bb_idx = walk_ctx.bb_idx,
                current_bb, "virtual body: Unreachable reached — failing check"
            );
            state.record_deferred_check(
                trust_mc_core::violation::PropertyKind::Unreachable,
                Some(UNREACHABLE_CODE_MESSAGE.to_string()),
                Expr::bool_const(false),
                ctx.heap_state.write_mark(),
            );
            TerminatorStep::Return(diverged_path_return(ctx, walk_ctx, state))
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
            state.record_deferred_check(kind, message, guard.clone(), ctx.heap_state.write_mark());
            state.record_assert_guard(guard);
            TerminatorStep::ContinueAt(target)
        }
        None => {
            // Part of #4014: an Assert condition that reads a local the walk
            // silently skipped (e.g. a CheckedAdd result on a deref through a
            // static-mut pointer with width mismatch, or an array element read
            // at a symbolic index) keeps walking, so the return value is not
            // lost with the whole walk.
            //
            // Mechanism E (docs/chc-walker-missed-bugs-2026-09-23.md): this arm
            // used to ASSUME the assertion passes, which drops exactly the
            // failing behaviour; "the outer encoding verifies it independently"
            // is false for a walked body, whose checks exist only here. The
            // obligation is real and its condition unknown, so it is recorded
            // as failing wherever it is reached, never certified
            // (`uncertified_check.rs`), with the Assert's own kind and message.
            let (kind, message) =
                crate::codegen_ay::chc::expr::codegen_expr_assert::mir_assert_kind_and_message(msg);
            debug!(
                bb_idx = walk_ctx.bb_idx,
                ?message,
                "virtual body: Assert condition untranslatable — uncertified reach check"
            );
            let check = super::uncertified_check::uncertified_reach_check(
                ctx,
                super::uncertified_check::WALKER_UNTRANSLATABLE_ASSERT,
            );
            state.record_deferred_check(kind, message, check, ctx.heap_state.write_mark());
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
    fresh_native_dyn: bool,
) -> TerminatorStep {
    let resolver = walk_ctx.resolver;
    // A pure-call summary cannot erase undefined reads in a user's prefix.
    // Inspect the resolved callee's own namespace before any such summary;
    // keep executing its real body/effects after booking this refusal.
    #[cfg(all(trust_toolchain, version("1.101")))]
    if let Ok(ty) = func.ty(walk_ctx.locals)
        && let TyKind::RigidTy(RigidTy::FnDef(def, substs)) = ty.kind()
        && def.krate().is_local
        && let Ok(instance) = Instance::resolve(def, &substs)
        && !matches!(instance.kind, rustc_public::mir::mono::InstanceKind::Virtual { .. })
        && instance.callee_body().is_some_and(|body| {
            crate::codegen_ay::shared::native_maybe_memory::body_has_native_maybe_memory(
                ctx.tcx, &body,
            )
        })
    {
        ctx.record_sound_fallback_reason("native_maybe_callee_without_initializedness_provenance");
    }
    // A nested raw walk has no initialized-payload/custody certificate and
    // must not replay the native unsafe transmute's unchecked precondition.
    #[cfg(all(trust_toolchain, version("1.101")))]
    if let Ok(ty) = func.ty(walk_ctx.locals)
        && let TyKind::RigidTy(RigidTy::FnDef(def, substs)) = ty.kind()
        && let Ok(instance) = Instance::resolve(def, &substs)
        && (crate::codegen_ay::native_init_boundary(ctx.tcx, &instance).is_some()
            || crate::codegen_ay::native_maybe_unsafe_accessor(ctx.tcx, &instance)
            || crate::codegen_ay::native_maybe_uninit_write(ctx.tcx, &instance).is_some_and(
                |native| {
                    args.first().is_some_and(|receiver| {
                        crate::codegen_ay::native_maybe_write_box_receiver(
                            ctx.tcx,
                            &walk_ctx.body.blocks,
                            walk_ctx.locals,
                            receiver,
                            native.maybe,
                        )
                    })
                },
            ))
    {
        ctx.record_sound_fallback_reason("native_initialized_handoff_nested_custody_unmodeled");
        return TerminatorStep::Return(None);
    }
    // The call's result replaces the destination's slice metadata; a handler
    // below that knows the result's length records it afresh
    // (`statement_metadata::clear_inline_subslice_metadata_for_write`).
    if destination.projection.is_empty() {
        super::statement_metadata::clear_inline_subslice_metadata_for_write(
            ctx,
            None,
            destination.local,
        );
    }
    // Design 5 (loop_contract_scan.rs): a loop contract in a WALKED body runs
    // with its invariant unchecked (the raw register body is `{ true }`).
    if ctx.loop_contracts
        && super::loop_contract_scan::is_loop_contract_register_call(ctx, func, walk_ctx.locals)
    {
        debug!(current_bb, "walker: loop contract in a walked body — fail closed");
        super::loop_contract_scan::book(ctx, super::loop_contract_scan::WALKED_LOOP_CONTRACT);
    }
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

    // `<Vec<T> as kani::BoundedArbitrary>::bounded_any::<N>`: the
    // native model (nested_bounded_any.rs), not the library body.
    if destination.projection.is_empty()
        && let Some((value, any_passes)) = super::nested_bounded_any::try_inline_bounded_any_call(
            ctx,
            func,
            walk_ctx.locals,
            walk_ctx.locals[destination.local].ty,
        )
    {
        super::kani_inline::push_inline_any_loop_unwinding_check(
            ctx,
            any_passes,
            &state.assume_guards,
            &mut state.deferred_checks,
        );
        if apply_inline_writeback(ctx, walk_ctx, state, destination, value) {
            return TerminatorStep::ContinueAt(target_bb);
        }
        debug!(
            bb_idx = walk_ctx.bb_idx,
            local = destination.local,
            "virtual body: bounded_any destination write-back cannot be tracked"
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

    // Callees the walker models itself (`leaf_models.rs`): the vtable reads
    // and the deallocator, reached on every walked `dyn` and `Box` shape,
    // used to take the havoc below and, being `unsafe` and foreign, its
    // demoting `nested_call_dropped_obligation`; the `Layout` getters read the
    // packed layout the walked getter body cannot project.
    if let Some(step) = super::leaf_models::try_execute_leaf_model(
        ctx,
        walk_ctx,
        state,
        func,
        args,
        destination,
        target_bb,
    ) {
        return step;
    }

    // F2 (inline_walk_guard.rs): whether a walk this call makes returns an
    // address-bound local, which the destination then holds.
    let saved_native_dyn = ctx.inline_walk_returned_native_dyn.take();
    let saved_returned_address = std::mem::replace(&mut ctx.inline_walk_returned_address, false);
    let saved_returned_carrying = std::mem::replace(&mut ctx.inline_walk_returned_carrying, false);
    let nested_result = try_inline_nested_call(
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
    );
    let nested_native_dyn =
        std::mem::replace(&mut ctx.inline_walk_returned_native_dyn, saved_native_dyn);
    let nested_returned_address =
        std::mem::replace(&mut ctx.inline_walk_returned_address, saved_returned_address);
    let nested_returned_carrying =
        std::mem::replace(&mut ctx.inline_walk_returned_carrying, saved_returned_carrying);
    if let Some(mut result) = nested_result {
        if destination.projection.is_empty() {
            if let Some(origin) = ctx.finish_native_dyn_return(
                walk_ctx.body,
                destination.local,
                fresh_native_dyn,
                nested_native_dyn,
            ) {
                state.inline_vtable_ids.insert(destination.local, origin.vtable_expr());
            }
        }
        let dest_is_reference = destination.projection.is_empty()
            && super::super::inline_walk_guard::local_is_reference(
                ctx,
                walk_ctx.locals,
                destination.local,
            );
        let dest_is_address_slot = destination.projection.is_empty()
            && super::super::inline_walk_guard::local_is_pointer_or_reference(
                ctx,
                walk_ctx.locals,
                destination.local,
            );
        if nested_returned_address && dest_is_address_slot {
            ctx.tag_inline_walk_address_local(destination.local);
        }
        // F2 residual: an aggregate the callee returned with an address in a
        // field (`fn mk(r: &u8) -> Wr { Wr { r, k: 1 } }`), or an address
        // written into a field of the destination's local.
        if (nested_returned_carrying || nested_returned_address)
            && !dest_is_reference
            && !super::statement_exec::place_writes_through_deref(destination)
        {
            ctx.mark_inline_walk_address_carrying(destination.local);
        }
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
            if let Some(
                rustc_public::mir::Operand::Copy(place) | rustc_public::mir::Operand::Move(place),
            ) = callee_arg_local.checked_sub(1).and_then(|i| args.get(i))
            {
                ctx.native_dyn_carrier_write(walk_ctx.locals, place);
            }
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
                if ctx.register_contract_walk_depth > 0 || ctx.in_modifies_frame_extent() {
                    ctx.record_fallback();
                }
                // Lost-write record (docs/chc-hole-fix-designs-2026-09-24.md
                // section 2): the dropped update is a lost write for every
                // later reader, not only inside a contract or frame.
                ctx.record_sound_fallback_reason(
                    super::super::inline_walk_guard::WALKER_NESTED_ALIAS_WRITEBACK_DROPPED,
                );
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

        // Layout intrinsics are COMPILE-TIME CONSTANTS — never havoc them.
        //
        // `mem::size_of`, `align_of`, `size_of_val`, `vtable_size`/`vtable_align`
        // already have a correct translator (`translate_mem_intrinsic_call`,
        // reached from the statement-level path via `codegen_call_mem_intrinsic`).
        // The inline walker never consulted it, so inside an inlined body a
        // `size_of::<T>()` became a fresh unconstrained symbol and the solver
        // was free to pick any value for it — which manufactures counterexamples
        // against correct code.
        //
        // Measured 2026-08-23 over the 42 `oracle=success, observed=fail` rows
        // in this cluster: `size_of` 7 rows, `align_of` 3, `size_of_val` 3,
        // `vtable_size` 3, `vtable_align` 2 — the largest single family.
        //
        // Not new modelling, just reusing the existing model on the path that
        // skipped it. `translate_mem_intrinsic_call` returns None for every
        // non-layout stub (`_ => return None`) and fails closed on unknown
        // types, so this can only ever REPLACE a havoc with a known constant.
        // The sort guard keeps it conservative: if the translated constant does
        // not match the destination sort we fall through to the old fallback
        // rather than force a coercion the walker cannot verify.
        // `func` is an operand of the INLINED body, so it must be resolved
        // against `walk_ctx.locals`, not `ctx.body` (#chc-inline-operand-locals).
        if let Some(stub) = ctx.detect_stub_with_locals(func, walk_ctx.locals)
            && let Some(result) = ctx.translate_mem_intrinsic_call(stub, func)
            && result.sort() == &dest_sort
        {
            debug!(
                current_bb,
                ?callee_path,
                ?stub,
                "walker: layout intrinsic folded to a constant instead of havoc"
            );
            if apply_inline_writeback(ctx, walk_ctx, state, destination, result) {
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
        // A nested callee that can WRITE THROUGH A POINTER ARGUMENT is not
        // over-approximated by havocking its RESULT: the write it would have made
        // to the caller's memory is dropped, and the model keeps the stale value.
        // `r.fill(0)` inlines to `std::intrinsics::write_bytes(ptr, 0, len)`,
        // whose whole effect is that write, so `let r: &mut [u8; 2] = &mut a;
        // r.fill(0); assert!(a[1] == 2)` verified SUCCESSFUL — a missed bug
        // (negative/ref_index_ops.rs, main 31793ccc3). `record_aggregate_gap` is a
        // SOUND_APPROXIMATION category that leaves a proof clean, so it cannot
        // carry this; a fail-closed reason can.
        // A callee whose body (transitively) writes nothing cannot drop a
        // write, whatever pointer it is handed (`ptr::add`, whose raw-pointer
        // argument used to fail closed here: `uncertified_check::callee_is_write_free`).
        if nested_callee_may_write_through_a_pointer_arg(ctx, args, walk_ctx.locals)
            && !super::uncertified_check::callee_is_write_free(ctx, func, walk_ctx.locals)
        {
            debug!(
                current_bb,
                ?callee_path,
                "walker: havocked nested call can write through a pointer argument — fail closed"
            );
            ctx.record_sound_fallback_reason("inline_nested_call_writes_through_pointer");
        }
        // Design 3 (call/fn_ptr_targets.rs): an INDIRECT call, through a fn
        // pointer or to a `dyn` method, whose target the walker did not
        // resolve. Its body, and so its obligations and writes, are unknown;
        // the `nested_call_overapprox` blessing below argues only about the
        // return value. A lone fn-pointer target over the inline budget, or a
        // pointer read from a static with no target reified in the host, used
        // to be havocked here clean (walker_fn_ptr_target_dual.rs
        // `bug_single_target_too_large`, `bug_static_nodecoy`).
        if nested_callee_is_indirect(ctx, func, walk_ctx.locals) {
            debug!(current_bb, "walker: havocked indirect call — fail closed");
            ctx.record_sound_fallback_reason(super::super::fn_ptr_targets::INDIRECT_CALL_HAVOCKED);
        }
        // Design 5 (loop_contract_scan.rs): the havoc drops every loop contract
        // the callee reaches, and with it the invariant checks Kani makes.
        if ctx.loop_contracts
            && super::loop_contract_scan::havocked_callee_reaches_loop_contract(
                ctx,
                func,
                walk_ctx.locals,
            )
        {
            debug!(current_bb, ?callee_path, "walker: havocked callee reaches a loop contract");
            super::loop_contract_scan::book(ctx, super::loop_contract_scan::HAVOCKED_LOOP_CONTRACT);
        }
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
        // The fresh value is booked first, with its identity (Rule E: the
        // builders mint it on this token). See the TAINT note below for why it
        // is a sound value havoc of the return only.
        let fallback_name = super::super::chc_fresh_name("__nested_call_overapprox");
        let booked = ctx.record_sound_fallback_reason_identified(
            "nested_call_overapprox",
            Some(&fallback_name),
        );
        let fallback_var = try_build_valid_collection_backing_fallback(
            ctx,
            booked,
            &fallback_name,
            &effective_sort,
            callee_path.as_deref(),
        )
        .unwrap_or_else(|| {
            build_nested_call_fallback_expr(
                booked,
                fallback_name.clone(),
                effective_sort,
                is_pointer_dest,
            )
        });

        // TAINT (Task #78): this call could not be inlined — missing stdlib MIR,
        // an unhandled stub — so its result is a fresh, unconstrained symbol.
        // Only the depth-exhaustion branch above recorded anything, which left
        // the ordinary case invisible: the harness carried no approximation at
        // all, `classify_ctrex` fell through to its `Genuine` default, and a
        // counterexample built on an invented return value was reported as a
        // real bug in correct code. Live instance:
        // `bounded_any::<String, 4>().len() <= 4` — the function's own contract
        // — FAILED with `[AY:CTREX_CAT:Genuine]`. (A failing `HashMap::get` is
        // mislabelled the same way but does NOT come through here: the CHC lane
        // models hashbrown as raw memory rather than stubbing it, so there is no
        // over-approximated CALL result to tag. See the findings note.)
        //
        // Recorded as a SOUND approximation, not a demoting fallback: the var
        // is a fresh `declare-var`, universally quantified over its rule, so it
        // admits every value the real call could return and cannot mint a false
        // proof. That keeps clean proofs clean while making a counterexample
        // that depends on the invented value `OverApproximation` — i.e.
        // `[AY:CTREX_NOT_CERTIFIED]`, which is exactly what this case is.
        {
            // Name the callee we gave up on. `record_sound_fallback_reason_identified`
            // records the freed VAR (`__nested_call_overapprox_N`), which says a
            // call was over-approximated but not WHICH — and this is the largest
            // non-parity cluster in the corpus, so "somewhere" is not a triage
            // key. `note_gap_reason` touches no counter, so classification is
            // unaffected; the string surfaces as
            // `[AY:AGGREGATE_GAP_REASON:<fn>:nested_call_overapprox@<callee>=N]`.
            // Recorded UNCONDITIONALLY. An earlier cut only recorded when
            // `callee_path` resolved, and on the rows actually in this cluster
            // it does not — so every record was dropped and the marker never
            // appeared. "The callee could not be resolved" is itself the
            // finding: it separates "we know which call and have not modelled
            // it" from "we cannot even name the call", and those need different
            // fixes.
            let callee_label = callee_path.as_deref().unwrap_or("<unresolved-callee>");
            ctx.note_gap_reason(&format!("nested_call_overapprox@{callee_label}"));
            // Rule D, site B (design trust-mc-reds-final §4.1): the havoc
            // keeps the RETURN VALUE only. The `nested_call_overapprox`
            // blessing argues that a fresh universally-quantified destination
            // "can only add behaviours, never remove one" — true of the value,
            // and silent about the callee's OBLIGATIONS: dropping one removes
            // exactly the failing behaviour (an `assert!(a == 43)` inside
            // `kani::block_on` reported `[AY:PROOF_QUALIFIERS:clean]
            // SUCCESSFUL`; `walker_get_unchecked_dual.rs` and the core
            // `unchecked_*` wrappers lost their UB preconditions the same way).
            //
            // So the havoc is a sound value havoc only for a callee PROVEN
            // inert: the obligation-free walk saw every body it reaches and
            // found no obligation site. Anything else — an obligation sighted,
            // a body-less or foreign callee, an indirect or virtual one, the
            // walk's budget — books the lost effect fail-closed. This is the
            // policy change Rule D makes: "could not tell" is no longer
            // blessed. Its precision cost is counted by the dual gates.
            //
            // The merge of fix/chc-walker-fail-closed keeps this predicate over
            // the branch's finer reading of a callee in another crate (an
            // `unsafe` one unless proved obligation-free, a safe one only where
            // it can fail for its caller, and the contained-foreign and
            // `memchr` exemptions). That reading argued a safe function cannot
            // reach a UB check for any argument; it can once unsafe code has
            // broken an invariant of its argument (`set_len` past the
            // capacity, then `Vec::len`'s `assert_unchecked`), which Kani
            // checks.
            //
            // Under a declared unwind bound with unwinding assertions on, a
            // loop an inert callee reaches is an obligation too, Kani's
            // unwinding assertion, which the havoc drops with the loop's
            // passes (`nested_callee_may_fail_unwinding_assertion`, below).
            if !nested_callee_is_certified_inert(ctx, func, walk_ctx.locals) {
                debug!(?callee_path, "walker: havocked callee is not certified inert");
                super::super::inline_walk_guard::record_lost_obligation(
                    ctx,
                    super::super::inline_walk_guard::LostEffect::NestedCallFallback,
                );
            } else if nested_callee_may_fail_unwinding_assertion(ctx, func, walk_ctx.locals) {
                // Kani's unwinding assertion is the inert callee's only
                // obligation here, and the havoc drops it with the loop's
                // passes: the lost effect is booked. (The branch's trip-count
                // check `B < U ∨ t` for `memchr`, `raw_eq` and `compare_bytes`
                // is not reachable under Rule D: none of them is inert.)
                debug!(
                    ?callee_path,
                    "walker: havocked inert callee may loop under a declared bound"
                );
                super::super::inline_walk_guard::record_lost_obligation(
                    ctx,
                    super::super::inline_walk_guard::LostEffect::NestedCallFallback,
                );
            }
            // Say it on stderr too, once per distinct callee.
            //
            // The recorded reason above is the durable channel, but it rides
            // `aggregate_encoding_gap`, which is currently never serialized into
            // kani-metadata (a pre-existing gap), so nothing downstream can read
            // it yet. This mirrors `first_report_of_missing_stdlib_mir` in the
            // inline pass and makes the cluster triagable from a plain run in
            // the meantime. Once-per-callee because the walker reaches the same
            // call from every harness and every pass.
            if first_report_of_overapproximated_callee(callee_label) {
                tracing::warn!(
                    "Nested call over-approximated (result is a fresh unconstrained \
                     symbol): {callee_label} — a counterexample that depends on it is \
                     not a real bug"
                );
            }
            // `nested_call_overapprox` was booked with the fresh value's
            // identity before it was minted (above). Both builders mint exactly
            // that name: the thin-pointer arm wraps it, the collection-backing
            // fallback reads its fields, so the identity covers every use.
        }
        // FC-06: the havoc above keeps only the return value. Inside a
        // modifies frame, the callee's writes through its arguments are
        // dropped with it, so no frame check can see them: fail closed.
        if ctx.in_modifies_frame_extent()
            && crate::codegen_ay::chc::modifies_frame_net::call_args_may_write(
                ctx,
                args,
                walk_ctx.locals,
            )
        {
            let callee_label = callee_path.as_deref().unwrap_or("<unresolved-callee>");
            ctx.modifies_frame_fail_closed(&format!(
                "nested call havoc drops writes: {callee_label}"
            ));
        }

        let validity = havocked_result_validity(
            ctx,
            walk_ctx,
            &state.local_exprs,
            func,
            args,
            destination,
            &fallback_var,
        );
        if apply_inline_writeback(ctx, walk_ctx, state, destination, fallback_var) {
            if let Some(validity) = validity {
                state.assume_guards.push(validity);
            }
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
                return mono_ty::field_ty(field, &args).and_then(ty_signedness).unwrap_or(false);
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
    // As for a projected statement assign (`statement_exec.rs`): a write
    // through a deref, however it is applied below, noted after the functional
    // lane's own read of the base (F1 must not see it as a read after a write).
    let writes_through_deref = super::statement_exec::place_writes_through_deref(place)
        || super::statement_exec::place_writes_through_deref(&retarget_place);
    let effects_before = ctx.heap_state.effect_mark();

    // A whole local takes the value; a projected place goes through the
    // statement path's lanes, which also apply a write through a non-argument
    // pointer local to its referent or record it lost (M1, referent_write.rs).
    let lane = if retarget_place.projection.is_empty() {
        state.write_local_with_alloc_id(retarget_place.local, value, alloc_id);
        Some(super::statement_exec::ProjectedAssignLane::Rebound)
    } else {
        super::statement_exec::write_inline_projected_value(
            ctx,
            walk_ctx,
            state,
            &retarget_place,
            value,
            None,
            0,
        )
    };
    if writes_through_deref {
        ctx.heap_state.note_write();
    }
    // The F1 exemption's record and F3 (inline_walk_guard.rs), as for a
    // projected statement assign.
    if let Some(lane) = lane {
        super::statement_exec::note_projected_write_effects(
            ctx,
            walk_ctx,
            state,
            &retarget_place,
            lane,
            effects_before,
        );
    }
    lane.is_some()
}

/// Kani's description of reaching `unreachable_unchecked` (its body is the
/// `unreachable` intrinsic, a `TerminatorKind::Unreachable`).
pub(super) const UNREACHABLE_CODE_MESSAGE: &str = "unreachable code";

/// A diverging callee whose only behaviour is undefined: reaching it IS the
/// failure (Mechanism D, docs/chc-walker-missed-bugs-2026-09-23.md).
///
/// `core::hint::unreachable_unchecked` checks its precondition under
/// `check_language_ub()` (false in Kani and here) and then runs the
/// `unreachable` intrinsic, which Kani reports as "unreachable code". The
/// intrinsic's own paths are listed defensively only: `LowerIntrinsics`
/// rewrites a call of it into a `TerminatorKind::Unreachable`, which the
/// walker handles as a terminator (`execute_inline_terminator`, and
/// `switchint.rs` `unreachable_arm_is_obligation`).
pub(super) fn is_ub_unreachable_callee(path: &str) -> bool {
    let base = path.split("::<").next().unwrap_or(path);
    matches!(
        base,
        "core::hint::unreachable_unchecked"
            | "std::hint::unreachable_unchecked"
            | "core::intrinsics::unreachable"
            | "std::intrinsics::unreachable"
    )
}

/// Kani's description of a panic whose message is not a constant
/// (`codegen_panic` in Kani's goto backend).
const KANI_RUNTIME_PANIC_MESSAGE: &str =
    "This is a placeholder message; Kani doesn't support message formatted at runtime";

/// Is `func` Kani's panic entry: the `PanicHook` (`kani::panic`, what
/// trust-mc's `library/std` lowers `panic!`, `unreachable!`, `todo!` and
/// `unimplemented!` to) or the `PanicStub` model (Kani's rewrite of
/// `core::panicking::panic*` in a transformed body)? Resolved against the
/// WALKED body's `locals`, by the marker the encoder itself dispatches on.
pub(super) fn is_kani_panic_callee(func: &Operand, locals: &[LocalDecl]) -> bool {
    let Ok(func_ty) = func.ty(locals) else {
        return false;
    };
    let TyKind::RigidTy(RigidTy::FnDef(fn_def, fn_args)) = func_ty.kind() else {
        return false;
    };
    let marker = Instance::resolve(fn_def, &fn_args)
        .ok()
        .and_then(|instance| attributes::fn_marker(instance.def))
        .or_else(|| attributes::fn_marker(fn_def));
    matches!(
        marker.as_ref().and_then(|marker| try_get_kani_function(marker)),
        Some(
            KaniFunction::Hook(KaniHook::Panic)
                | KaniFunction::Model(crate::kani_middle::kani_functions::KaniModel::PanicStub)
        )
    )
}

/// The message Kani reports for a panic call with arguments `args`: its
/// constant `&str` (the std shims pass the literal through), else Kani's
/// placeholder for a message built at run time. `args` are WALKED-body
/// operands, so only a constant is read (a Copy/Move would trace host locals).
pub(super) fn kani_panic_message(ctx: &ChcCtx<'_, '_>, args: &[Operand]) -> String {
    args.first()
        .and_then(|arg| match arg {
            Operand::Constant(_) => {
                let (bytes, _) = ctx.try_extract_const_str_bytes(arg)?;
                String::from_utf8(bytes).ok()
            }
            _ => None,
        })
        .unwrap_or_else(|| KANI_RUNTIME_PANIC_MESSAGE.to_string())
}

/// Handle diverging Call terminators (no target).
fn execute_diverging_call<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    walk_ctx: &InlineWalkCtx<'_>,
    state: &mut InlineExecutionState,
    func: &rustc_public::mir::Operand,
    args: &[rustc_public::mir::Operand],
    current_bb: usize,
) -> TerminatorStep {
    // `kani::panic(msg)`: Kani's `codegen_panic` is a fatal assertion failure
    // with the message, so reaching it fails, exactly, like a panic arm or
    // `unreachable_unchecked`. It used to be an unmodelled diverging call:
    // an uncertified reach check, so the harness FAILED but was never
    // certified Genuine (fix/chc-walker-fail-closed, package round 2 item d).
    if is_kani_panic_callee(func, walk_ctx.locals) {
        let message = kani_panic_message(ctx, args);
        debug!(bb_idx = walk_ctx.bb_idx, ?current_bb, %message, "diverging: kani::panic reached");
        state.record_deferred_check(
            trust_mc_core::violation::PropertyKind::Assertion,
            Some(message),
            Expr::bool_const(false),
            ctx.heap_state.write_mark(),
        );
        return TerminatorStep::Return(diverged_path_return(ctx, walk_ctx, state));
    }
    let Some(path) = resolve_inline_callee_path(ctx, func, walk_ctx.locals) else {
        return TerminatorStep::Return(None);
    };
    if ChcCtx::is_formatting_path(&path) {
        debug!(bb_idx = walk_ctx.bb_idx, ?current_bb, %path, "diverging: panic/formatting fallback");
        return TerminatorStep::Return(diverged_path_return(ctx, walk_ctx, state));
    }
    // Mechanism D: reaching `unreachable_unchecked` is a failing check, exactly
    // as a panic is. Used to be an unsupported call, whose arm then bailed into
    // a blessed havoc and took the obligation with it. The check is `false` on
    // this path (the path condition is added by `record_deferred_check` and the
    // SwitchInt merges); the path then ends as a panic's does. An arm that
    // reaches it directly is filtered by `switchint.rs` (`is_ub_unreachable_arm`)
    // and never gets here.
    if is_ub_unreachable_callee(&path) {
        debug!(bb_idx = walk_ctx.bb_idx, ?current_bb, %path, "diverging: unreachable_unchecked reached");
        state.record_deferred_check(
            trust_mc_core::violation::PropertyKind::Unreachable,
            Some(UNREACHABLE_CODE_MESSAGE.to_string()),
            Expr::bool_const(false),
            ctx.heap_state.write_mark(),
        );
        return TerminatorStep::Return(diverged_path_return(ctx, walk_ctx, state));
    }
    // Any other diverging call (a user `-> !` function, `process::exit`, ...)
    // is not modelled. When its callee CAN carry an obligation (the walk of
    // its body, transitively and in any crate, is not provably free of one),
    // reaching it is recorded as a check that fails wherever it is reached,
    // never certified (`uncertified_check.rs`): a panic inside the callee is
    // one of its behaviours, and ending the walk here used to drop it with
    // the arm's blessed havoc (walker_validity_intrinsics_dual.rs
    // `diverge_bug`). The path then ends with a freed value; it is not the
    // certifiable panic fallback, because the callee may exit without
    // failing. A provably obligation-free callee (it can only loop or stop)
    // still ends the walk, as before.
    if diverging_callee_may_carry_obligation(ctx, func, walk_ctx.locals) {
        debug!(bb_idx = walk_ctx.bb_idx, ?current_bb, %path, "diverging: unmodelled call — uncertified reach check");
        let check = super::uncertified_check::uncertified_reach_check(
            ctx,
            super::uncertified_check::WALKER_UNMODELLED_DIVERGING_CALL,
        );
        state.record_deferred_check(
            trust_mc_core::violation::PropertyKind::Panic,
            Some(format!(
                "a panic or other divergence the CHC walker does not model is reachable: `{path}`"
            )),
            check,
            ctx.heap_state.write_mark(),
        );
        return TerminatorStep::Return(unmodelled_divergence_return(ctx, walk_ctx, state));
    }
    debug!(bb_idx = walk_ctx.bb_idx, ?current_bb, %path, "diverging: unsupported call");
    TerminatorStep::Return(None)
}

/// Can the diverging callee `func` carry an obligation? See
/// `uncertified_check::callee_may_carry_obligation`.
fn diverging_callee_may_carry_obligation(
    ctx: &ChcCtx<'_, '_>,
    func: &Operand,
    locals: &[LocalDecl],
) -> bool {
    let stubs = crate::kani_middle::transform::walker_stub_map();
    super::uncertified_check::callee_may_carry_obligation(ctx, func, locals, &stubs)
}

/// The walk result of a path that reaches an unmodelled diverging call: a
/// fresh value, accounted as a freed variable (the call never returns, so any
/// counterexample reading it is not the program's), with the side-channel
/// checks the path recorded, the reach check included.
fn unmodelled_divergence_return<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    walk_ctx: &InlineWalkCtx<'_>,
    state: &mut InlineExecutionState,
) -> Option<InlineReturn> {
    let ret_ty = ctx.resolve_inline_local_ty(walk_ctx.body, 0).unwrap_or(walk_ctx.locals[0].ty);
    let ret_sort = match ret_ty.kind() {
        TyKind::RigidTy(RigidTy::Tuple(tys)) if tys.is_empty() => {
            Expr::bool_const(true).sort().clone()
        }
        _ => ChcCtx::translate_ty(ret_ty)?,
    };
    let name = super::super::chc_fresh_name("__walker_diverged_value");
    let booked = ctx.record_sound_fallback_reason_identified(
        super::uncertified_check::WALKER_UNMODELLED_DIVERGING_CALL,
        Some(&name),
    );
    let mut result = InlineReturn::value_only(crate::codegen_ay::chc::codegen_ctx::Havoc::booked(
        booked, name, ret_sort,
    ));
    result.deferred_checks = std::mem::take(&mut state.deferred_checks);
    Some(result)
}

/// The walk result of a path that ends in a failing diverging call: the
/// panic fallback value (`__assert_fail_inline`, the value channel) with the
/// side-channel checks the path recorded on its way here. The fallback alone
/// is value-only, so every check recorded before the call, the call's own
/// included, used to be dropped with the walk state.
fn diverged_path_return<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    walk_ctx: &InlineWalkCtx<'_>,
    state: &mut InlineExecutionState,
) -> Option<InlineReturn> {
    let mut result = virtual_panic_fallback(ctx, walk_ctx)?;
    result.deferred_checks = std::mem::take(&mut state.deferred_checks);
    Some(result)
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
    Some(crate::intrinsics::callee_path_model_spelling(
        ctx.tcx.def_path_str(internal_def_id),
        fn_def,
        &fn_args,
    ))
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
    match fn_def.callee_body() {
        Some(body) => body_contains_check_sites(ctx, &body, &mut visited, 0),
        None => false,
    }
}

/// Resolve a call operand to a monomorphic instance, mirroring
/// `nested_call::resolve_inline_callee` (body-ty normalization with a raw
/// FnDef fallback, Part of #4161), THROUGH the unit's stub map
/// (`stubs`, `kani_middle::transform::walker_stub_map`): an obligation scan
/// must inspect the function the unit runs, and a stub can add a check the
/// original lacks.
pub(super) fn resolve_check_scan_instance(
    ctx: &ChcCtx<'_, '_>,
    func: &Operand,
    locals: &[LocalDecl],
    stubs: &crate::codegen_ay::obligation_free_walk::StubMap,
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
    crate::codegen_ay::obligation_free_walk::resolve_through_stubs(fn_def, &fn_args, stubs)
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
        .or_else(|| instance.callee_body())
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
            if let Some(callee) = resolve_check_scan_instance(
                ctx,
                callee_op,
                body.locals(),
                &crate::kani_middle::transform::walker_stub_map(),
            ) && instance_contains_check_sites(ctx, callee, visited, depth + 1)
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

/// Has this over-approximated callee already been reported in this run?
///
/// Returns true exactly once per distinct callee path. The walker reaches the
/// same call from every harness and on every pass, so without this a single
/// `Vec::push` would print once per visit and bury the list it exists to
/// produce. Process-global for the same reason as the inline pass's twin
/// (`first_report_of_missing_stdlib_mir`): the compiler runs once per crate and
/// this site has no single owner to hang the set on.
fn first_report_of_overapproximated_callee(callee: &str) -> bool {
    use std::collections::HashSet;
    use std::sync::{Mutex, OnceLock};

    static REPORTED: OnceLock<Mutex<HashSet<String>>> = OnceLock::new();
    REPORTED
        .get_or_init(|| Mutex::new(HashSet::new()))
        .lock()
        .map_or(true, |mut seen| seen.insert(callee.to_owned()))
}

/// Rule D, site B: is the callee this site gave up on PROVEN inert — an
/// obligation-free intrinsic, or a body whose whole region from its entry
/// neither checks nor writes (`inline_walk_guard::region_may_check_or_write`,
/// the one predicate every Rule D site reads)? `false` for "has an
/// obligation", for "could not tell" (no body, indirect, virtual, the walk's
/// budget) and for a write. Writes through a pointer argument are also booked
/// on their own, beside it.
fn nested_callee_is_certified_inert(
    ctx: &ChcCtx<'_, '_>,
    func: &Operand,
    locals: &[LocalDecl],
) -> bool {
    let Ok(raw_func_ty) = func.ty(locals) else { return false };
    let TyKind::RigidTy(RigidTy::FnDef(fn_def, fn_args)) = ctx.resolve_body_ty(raw_func_ty).kind()
    else {
        return false;
    };
    let Ok(instance) = Instance::resolve(fn_def, &fn_args) else {
        return false;
    };
    if matches!(instance.kind, rustc_public::mir::mono::InstanceKind::Virtual { .. }) {
        return false;
    }
    if crate::codegen_ay::obligation_free_walk::is_obligation_free_intrinsic(&instance) {
        return true;
    }
    let Some(body) = instance.callee_body() else {
        return false;
    };
    !super::super::inline_walk_guard::region_may_check_or_write(ctx, &body, 0)
}

/// The validity of a nested-call havoc of a FIELDLESS enum: the fresh value
/// holds one of the enum's discriminants
/// (`inline_shared::inline_fieldless_enum_validity`), when the call cannot
/// return any other (`obligation_free_walk::call_may_return_invalid_value`):
/// the callee manufactures none (no transmute, raw-pointer access, union
/// field or unreadable callee anywhere it reaches) and cannot pass one on
/// (no argument whose type can hold the enum, no constant reference to one
/// anywhere it reaches). The program's value is then a valid one, and the
/// walker assumes the havoc is too.
///
/// Passing on was not considered at first: a helper returning its enum
/// argument, or `*e` through `&E`, handed back an invalid value its caller
/// wrote through `*mut u8`, the assumption pruned that execution, and Kani's
/// "unreachable code" failure verified clean (walker fail-closed review 6
/// round 2, finding 2, `rp1_forged_enum.rs`). An argument OF the enum's own
/// type, by value, is the one way in the result can be kept exact: the
/// result is then a valid value or that argument's (the walker knows it), so
/// a valid argument keeps the proof and a forged one reaches the arm.
///
/// A fieldless enum is a raw bitvector here, and the exhaustive `otherwise`
/// arm of a `match` on it is Kani's "unreachable code" check, because bits
/// written through memory can leave its range (walker_invalid_enum_dual.rs).
/// A havoc ranging over every bit pattern took that arm on values no
/// execution produces: an enum returned by a float helper the walker gives up
/// on failed "unreachable code" where main and Kani prove (walker fail-closed
/// review 6, finding 2, `a6_havocked_enum_safe`). `None` for any other
/// destination, a projected one, or a callee that may forge.
fn havocked_result_validity(
    ctx: &mut ChcCtx<'_, '_>,
    walk_ctx: &InlineWalkCtx<'_>,
    local_exprs: &HashMap<usize, Expr>,
    func: &Operand,
    args: &[Operand],
    destination: &rustc_public::mir::Place,
    havoc: &Expr,
) -> Option<Expr> {
    if !destination.projection.is_empty() {
        return None;
    }
    let dest_ty = ctx.resolve_body_ty(walk_ctx.locals.get(destination.local)?.ty);
    let mut validity =
        super::super::inline_shared::inline_fieldless_enum_validity(ctx, dest_ty, havoc.clone())?;
    // Arguments of exactly the enum's type, by value, join the result's
    // possible values; any other argument that can hold one refuses.
    let mut passed_on = Vec::new();
    let mut other_arg_tys = Vec::new();
    for arg in args {
        let ty = ctx.resolve_body_ty(arg.ty(walk_ctx.locals).ok()?);
        if ty == dest_ty {
            passed_on.push(arg);
        } else {
            other_arg_tys.push(ty);
        }
    }
    let stubs = crate::kani_middle::transform::walker_stub_map();
    let instance = resolve_check_scan_instance(ctx, func, walk_ctx.locals, &stubs)?;
    if crate::codegen_ay::obligation_free_walk::call_may_return_invalid_value(
        ctx.tcx,
        instance,
        &other_arg_tys,
        dest_ty,
        &stubs,
    ) {
        return None;
    }
    for arg in passed_on {
        let value = super::super::inline_shared::inline_operand_to_expr(
            ctx,
            arg,
            local_exprs,
            &walk_ctx.resolver,
            walk_ctx.locals,
        )?;
        if value.sort() != havoc.sort() {
            return None;
        }
        if host_value_built_valid(ctx, &value, dest_ty) {
            debug!("walker: passed-on enum value is a host local only ever built valid");
            continue;
        }
        validity = validity.or(havoc.clone().eq(value));
    }
    debug!(
        local = destination.local,
        "walker: havocked fieldless enum from a callee that cannot forge one — valid"
    );
    Some(validity)
}

/// Is `value` the state variable of a host local of the fieldless enum
/// `enum_ty` that only ever holds a valid value ([`host_local_built_valid`])?
/// Passing such a value on adds nothing to the havocked result's valid
/// values. The pass-on disjunct `h == e` on a valid `e` cost
/// `walker_enum_pass_on_dual.rs`'s `f1_valid_by_value_safe` its proof (91 s
/// undecided where main proves it in 22 s), since the solver then has to
/// carry `e`'s validity from where the harness built it (walker fail-closed
/// repair round 5).
fn host_value_built_valid(
    ctx: &ChcCtx<'_, '_>,
    value: &Expr,
    enum_ty: rustc_public::ty::Ty,
) -> bool {
    let ay_bindings::ExprValue::Var { name } = value.value() else {
        return false;
    };
    let body = ctx.body;
    let names_local = |local: usize| {
        let Some(&idx) = ctx.state_var_mgr.local_to_state_idx.get(&local) else {
            return false;
        };
        let is = |vars: &[(std::sync::Arc<str>, Sort)]| {
            vars.get(idx).is_some_and(|(var, _)| **var == **name)
        };
        is(&ctx.state_var_mgr.state_vars) || is(&ctx.state_var_mgr.output_state_vars)
    };
    body.locals().iter().enumerate().any(|(local, decl)| {
        decl.ty == enum_ty
            && names_local(local)
            && host_local_built_valid(body, local, enum_ty, &mut std::collections::HashSet::new())
    })
}

/// Does host local `local` of the fieldless enum `enum_ty` only ever hold a
/// valid value? It is not an argument, nothing borrows it or takes its
/// address (so nothing writes it through a cast pointer), and each of its
/// definitions is whole: a variant aggregate of the enum, a constant of its
/// type (const evaluation rejects an invalid one), or a copy of another such
/// local. A call result, a cast, a `SetDiscriminant`, a projected write and
/// inline assembly all refuse.
pub(in crate::codegen_ay::chc) fn host_local_built_valid(
    body: &rustc_public::mir::Body,
    local: usize,
    enum_ty: rustc_public::ty::Ty,
    seen: &mut std::collections::HashSet<usize>,
) -> bool {
    use rustc_public::mir::{AggregateKind, Rvalue, StatementKind};
    if !seen.insert(local) {
        // A cycle of copies holds only what flows in from outside it.
        return true;
    }
    if (1..=body.arg_locals().len()).contains(&local) {
        return false;
    }
    let TyKind::RigidTy(RigidTy::Adt(enum_def, _)) = enum_ty.kind() else {
        return false;
    };
    for block in &body.blocks {
        for stmt in &block.statements {
            match &stmt.kind {
                StatementKind::Assign(lhs, rvalue) => {
                    if let Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place) = rvalue
                        && place.local == local
                    {
                        return false;
                    }
                    if lhs.local != local {
                        continue;
                    }
                    if !lhs.projection.is_empty() {
                        return false;
                    }
                    let built_valid = match rvalue {
                        Rvalue::Aggregate(AggregateKind::Adt(def, ..), operands) => {
                            *def == enum_def && operands.is_empty()
                        }
                        Rvalue::Use(Operand::Constant(constant), ..) => constant.ty() == enum_ty,
                        Rvalue::Use(Operand::Copy(place) | Operand::Move(place), ..)
                            if place.projection.is_empty() =>
                        {
                            body.locals().get(place.local).is_some_and(|decl| decl.ty == enum_ty)
                                && host_local_built_valid(body, place.local, enum_ty, seen)
                        }
                        _ => false,
                    };
                    if !built_valid {
                        return false;
                    }
                }
                StatementKind::SetDiscriminant { place, .. } if place.local == local => {
                    return false;
                }
                _ => {}
            }
        }
        match &block.terminator.kind {
            TerminatorKind::Call { destination, .. } if destination.local == local => return false,
            TerminatorKind::InlineAsm { .. } => return false,
            _ => {}
        }
    }
    true
}

/// Can the callee a nested-call havoc replaces fail Kani's UNWINDING
/// assertion? Only under a declared unwind bound with unwinding assertions
/// on, when the callee (resolved through the unit's stub map) or anything it
/// reaches holds a loop or recursion (`obligation_free_walk::instance_may_loop`,
/// fail-closed where it cannot tell). The havoc keeps the return value and
/// drops the loop's passes, and with them the pass past the bound that Kani
/// reports; the walker records it only where it replays the loop
/// (`walker.rs`, `LoopHeaderVisit::UnwindExceeded`). A callee the walker
/// cannot enter (more than 16 effective blocks, the inline depth) is the
/// whole-call form of the abandoned arm
/// (`uncertified_check::region_may_fail_unwinding_assertion`; walker
/// fail-closed review 6, finding 4). An unresolvable callee is booked by the
/// indirect-call rule.
fn nested_callee_may_fail_unwinding_assertion(
    ctx: &ChcCtx<'_, '_>,
    func: &Operand,
    locals: &[LocalDecl],
) -> bool {
    if ctx.recursive_unwind_depth == 0 || !ctx.unwinding_assertions {
        return false;
    }
    let stubs = crate::kani_middle::transform::walker_stub_map();
    resolve_check_scan_instance(ctx, func, locals, &stubs).is_some_and(|instance| {
        super::uncertified_check::instance_may_loop_cached(ctx, instance, &stubs)
    })
}

/// Is the nested call indirect: through a fn pointer, or to a `dyn` method
/// (a `Virtual` instance)? Its target is then not named by the call.
fn nested_callee_is_indirect(
    ctx: &ChcCtx<'_, '_>,
    func: &rustc_public::mir::Operand,
    locals: &[LocalDecl],
) -> bool {
    let Ok(func_ty) = func.ty(locals) else { return false };
    match ctx.resolve_body_ty(func_ty).kind() {
        TyKind::RigidTy(RigidTy::FnPtr(..)) => true,
        TyKind::RigidTy(RigidTy::FnDef(fn_def, fn_args)) => Instance::resolve(fn_def, &fn_args)
            .is_ok_and(|instance| {
                matches!(instance.kind, rustc_public::mir::mono::InstanceKind::Virtual { .. })
            }),
        _ => false,
    }
}

/// Can the havocked nested callee write through one of its arguments? Any raw
/// pointer, any `&mut T`, and a `&T` whose pointee is interior-mutable says yes
/// ([`arg_is_writable_pointer`]). The argument types are read against the
/// INLINED body's locals, not the enclosing function's.
fn nested_callee_may_write_through_a_pointer_arg(
    ctx: &ChcCtx<'_, '_>,
    args: &[rustc_public::mir::Operand],
    locals: &[rustc_public::mir::LocalDecl],
) -> bool {
    args.iter().any(|arg| {
        arg.ty(locals)
            .is_ok_and(|ty| crate::codegen_ay::foreign_defs::arg_is_writable_pointer(ctx.tcx, ty))
    })
}
