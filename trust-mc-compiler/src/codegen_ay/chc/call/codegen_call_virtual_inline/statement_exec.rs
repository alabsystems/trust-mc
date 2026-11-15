// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Statement execution for the inline body walker.
//! Part of #3913: extracted from walker.rs statement loop.
//! Discriminant and ADT variant helpers split to statement_exec_helpers.rs
//! per #4206.

use ay_bindings::Expr;
use rustc_public::mir::{Rvalue, StatementKind};
use rustc_public::ty::{RigidTy, TyKind};
use std::collections::HashMap;
use tracing::debug;

use super::super::ChcCtx;
use super::super::inline_shared::{
    INLINE_RVALUE_UB_CHECK_DROPPED, InlineUbChecks, PlaceResolver, inline_binop_ub_checks,
    inline_operand_to_expr, inline_rvalue_to_expr,
};
use super::super::inline_walk_guard::{
    WALKER_DEREF_WRITE_DROPPED, WALKER_DEREF_WRITE_REBIND_LOST, WALKER_DEREF_WRITEBACK_MEMORY_ONLY,
    WALKER_SET_DISCRIMINANT_DROPPED, local_is_reference,
};
use super::execution_state::InlineExecutionState;
use super::kani_inline::inline_bool_condition;
use super::loop_replay::InlineWalkCtx;
use super::projected_assign::{
    apply_inline_coroutine_set_discriminant, apply_inline_projected_assign,
    rebuild_inline_coroutine_receiver, try_inline_memory_store,
};
use super::statement_exec_helpers::{
    try_inline_adt_variant_assign_expr, try_inline_set_discriminant_expr,
    try_inline_unit_enum_discriminant_expr,
};
use super::statement_metadata::{
    clear_inline_subslice_metadata_for_write, propagate_inline_subslice_metadata,
    seed_inline_array_view_len,
};
use super::vtable_prop::propagate_inline_vtable;

/// Whether assigning to `place` writes through a pointer (`*p = v`,
/// `(*p).f = v`, `(*(*p).g).f = v`), not only to a local.
pub(super) fn place_writes_through_deref(place: &rustc_public::mir::Place) -> bool {
    place.projection.iter().any(|elem| matches!(elem, rustc_public::mir::ProjectionElem::Deref))
}

/// Execute one MIR statement inside an inline body walk.
///
/// Returns `Some(())` on success, `None` if the walker should bail.
pub(super) fn execute_inline_statement<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    walk_ctx: &InlineWalkCtx<'_>,
    state: &mut InlineExecutionState,
    stmt: &rustc_public::mir::Statement,
    current_bb: usize,
) -> Option<()> {
    // Each walked statement's memory writes form their own heap view group.
    ctx.heap_state.view_ledger.next_statement();
    match &stmt.kind {
        StatementKind::Assign(place, rvalue) => {
            // A Box cast's pointer and UB checks are one operation. The
            // generic inline value API refuses this cast, so no alternate
            // value-only consumer can accidentally discard its checks.
            #[cfg(all(trust_toolchain, version("1.101")))]
            let checked_box_value = if let rustc_public::mir::Rvalue::Cast(
                rustc_public::mir::CastKind::BoxDerefTransmute,
                operand,
                target,
            ) = rvalue
            {
                let checked = (|| {
                    if !place.projection.is_empty() {
                        ctx.native_dyn_carrier_write(walk_ctx.locals, place);
                        return None;
                    }
                    let source = operand.ty(walk_ctx.locals).ok()?;
                    let value = inline_operand_to_expr(
                        ctx,
                        operand,
                        &state.local_exprs,
                        &walk_ctx.resolver,
                        walk_ctx.locals,
                    )?;
                    let origin = ctx.inline_native_dyn_origin(operand, walk_ctx.locals);
                    ctx.checked_native_box_deref_with_origin(
                        source,
                        *target,
                        value,
                        origin.as_ref(),
                    )
                })();
                let Some(checked) = checked else {
                    ctx.record_sound_fallback_reason("box_deref_validity_unmodeled");
                    return None;
                };
                for check in checked.checks {
                    state.record_deferred_check(
                        trust_mc_core::violation::PropertyKind::MemorySafety,
                        Some("Box dereference requires a non-null, aligned pointer to the full live pointee".to_owned()),
                        check,
                        ctx.heap_state.write_mark(),
                    );
                }
                Some(checked.value)
            } else {
                None
            };
            #[cfg(not(all(trust_toolchain, version("1.101"))))]
            let checked_box_value: Option<Expr> = None;
            // Integer BinOp UB (unchecked overflow, shift distance, Div/Rem):
            // the checks the statement path records, on the deferred-check
            // channel the host emits as error rules. First, so the operands are
            // read before the destination is written and no skip below can
            // drop the check. Never an assume and never a value change.
            match inline_binop_ub_checks(
                ctx,
                rvalue,
                &state.local_exprs,
                &walk_ctx.resolver,
                walk_ctx.locals,
                place.projection.is_empty().then_some(place.local),
            ) {
                InlineUbChecks::NotApplicable => {}
                InlineUbChecks::Checks(checks) => {
                    for check in checks {
                        state.record_deferred_check(
                            check.kind,
                            check.message,
                            check.check,
                            check.write_mark,
                        );
                    }
                }
                InlineUbChecks::Untranslatable => {
                    debug!(bb_idx = walk_ctx.bb_idx, current_bb, "inline BinOp UB check dropped");
                    ctx.record_sound_fallback_reason(INLINE_RVALUE_UB_CHECK_DROPPED);
                }
            }
            if !place.projection.is_empty() {
                ctx.native_dyn_carrier_write(walk_ctx.locals, place);
                if !place_writes_through_deref(place) {
                    ctx.note_inline_mut_ref_assignment(walk_ctx.body, place.local, None);
                }
                // F2 residual: a field of a local written with a value that may
                // hold an address makes the whole local address-carrying.
                if !place_writes_through_deref(place)
                    && rvalue_carries_address(ctx, walk_ctx, rvalue, true)
                {
                    ctx.mark_inline_walk_address_carrying(place.local);
                }
                let effects_before = ctx.heap_state.effect_mark();
                let lane = execute_inline_projected_assign(
                    ctx, walk_ctx, state, place, rvalue, current_bb,
                );
                // A write through a deref, whichever arm took it (a local update,
                // a memory store or a skip): a drop consumer asks whether the body
                // it walked wrote (`walk_drop_body`), and F1 reads it. Noted AFTER
                // the statement's own reads (its rhs, the base of a functional
                // update), which see the writes before it, not this one.
                if place_writes_through_deref(place) {
                    ctx.heap_state.note_write();
                }
                if let Some(lane) = lane {
                    note_projected_write_effects(ctx, walk_ctx, state, place, lane, effects_before);
                }
                return lane.map(|_| ());
            }
            ctx.last_inline_ref_was_address = false;
            // The write replaces the local's slice metadata
            // (`clear_inline_subslice_metadata_for_write`).
            clear_inline_subslice_metadata_for_write(ctx, Some(rvalue), place.local);
            let box_cast_address = checked_box_value.is_some();
            let resolved_expr = checked_box_value.or_else(|| {
                inline_assign_rvalue_expr(
                    ctx,
                    walk_ctx,
                    rvalue,
                    &state.local_exprs,
                    Some(place.local),
                )
            });
            if let Some(expr) = resolved_expr {
                let native_dyn_binding =
                    ctx.note_native_dyn_assignment(walk_ctx.body, place.local, Some(rvalue));
                ctx.note_inline_mut_ref_assignment(walk_ctx.body, place.local, Some(rvalue));
                ctx.note_readonly_resolved_value(place.local, &expr);
                let produces_address =
                    box_cast_address || rvalue_yields_address(ctx, walk_ctx, rvalue);
                // F2 (inline_walk_guard.rs): carry address-ness to the
                // destination before it is written.
                if local_is_reference(ctx, walk_ctx.locals, place.local) {
                    if produces_address || rvalue_reads_field_address(ctx, walk_ctx, rvalue) {
                        ctx.tag_inline_walk_address_local(place.local);
                    } else if match rvalue {
                        Rvalue::Ref(..) => !ctx.last_inline_ref_was_address,
                        Rvalue::Use(operand, ..) => {
                            ctx.inline_walk_operand_is_referent(operand)
                                || ctx.readonly_ref_value_matches(
                                    operand,
                                    walk_ctx.locals[place.local].ty,
                                )
                        }
                        Rvalue::CopyForDeref(source) => ctx.inline_walk_operand_is_referent(
                            &rustc_public::mir::Operand::Copy(source.clone()),
                        ),
                        _ => false,
                    } {
                        ctx.tag_inline_walk_referent_local(place.local);
                    } else {
                        ctx.forget_inline_walk_referent_local(place.local);
                    }
                } else {
                    if produces_address
                        && matches!(
                            ctx.resolve_body_ty(walk_ctx.locals[place.local].ty).kind(),
                            TyKind::RigidTy(RigidTy::RawPtr(..))
                        )
                    {
                        ctx.tag_inline_walk_address_local(place.local);
                    }
                    if rvalue_carries_address(ctx, walk_ctx, rvalue, false) {
                        ctx.mark_inline_walk_address_carrying(place.local);
                    }
                }
                let src_alloc_local = inline_alloc_source_local(rvalue);
                let src_alloc_id =
                    src_alloc_local.and_then(|src| state.inline_alloc_ids.get(&src).copied());
                propagate_inline_vtable(
                    ctx,
                    rvalue,
                    place.local,
                    &expr,
                    &state.local_exprs,
                    &walk_ctx.resolver,
                    walk_ctx.locals,
                    &mut state.inline_vtable_ids,
                );
                propagate_inline_subslice_metadata(ctx, rvalue, place.local);
                if let Some(origin) = native_dyn_binding {
                    state.inline_vtable_ids.insert(place.local, origin.vtable_expr());
                }
                state.write_local_with_alloc_id(place.local, expr, src_alloc_id);
            } else {
                ctx.note_native_dyn_assignment(walk_ctx.body, place.local, None);
                ctx.note_inline_mut_ref_assignment(walk_ctx.body, place.local, None);
                if local_is_reference(ctx, walk_ctx.locals, place.local) {
                    ctx.forget_inline_walk_referent_local(place.local);
                }
                // Part of #3861, #4095: Record constraint loss so diagnostic
                // infrastructure can flag harnesses with silent rvalue skips.
                //
                // Part of #4050: Record per-rvalue-variant gap reason so the
                // exact-file diagnostic can distinguish root-cause failures
                // from cascading None. Cascading = operand references a local
                // that was itself skipped in an earlier assignment.
                let variant_tag = classify_rvalue_gap(rvalue, &state.local_exprs, walk_ctx.locals);
                ctx.record_aggregate_gap(&variant_tag);
                // Part of #4050: enriched diagnostic for root projected gaps.
                if variant_tag.contains("root_projected") || variant_tag.contains("root_Offset") {
                    let rvalue_str = format!("{rvalue:?}");
                    let base_sort = match rvalue {
                        rustc_public::mir::Rvalue::Use(
                            rustc_public::mir::Operand::Copy(p)
                            | rustc_public::mir::Operand::Move(p),
                            ..,
                        ) if !p.projection.is_empty() => {
                            state.local_exprs.get(&p.local).map(|e| format!("{:?}", e.sort()))
                        }
                        _ => None,
                    };
                    debug!(
                        bb_idx = walk_ctx.bb_idx,
                        current_bb,
                        local = place.local,
                        %variant_tag,
                        %rvalue_str,
                        ?base_sort,
                        "walker: ROOT rvalue skip -- enriched diagnostic (#4050)"
                    );
                } else {
                    debug!(
                        bb_idx = walk_ctx.bb_idx,
                        current_bb,
                        local = place.local,
                        %variant_tag,
                        "walker: silent rvalue skip -- local not populated"
                    );
                }
            }
            // An array's slice view has the array's length, whatever became of
            // its value (`seed_inline_array_view_len`).
            seed_inline_array_view_len(ctx, rvalue, walk_ctx.locals, place.local);
        }
        StatementKind::SetDiscriminant { place, variant_index } => {
            let Ok(ty) = place.ty(walk_ctx.locals) else {
                return None;
            };
            // A discriminant written through a deref is a write through a deref
            // (F1, `walk_drop_body`), whichever arm below takes it; noted after
            // the arm's own read of the place.
            let writes_through_deref = place_writes_through_deref(place);
            if place.projection.is_empty()
                && let Some(discriminant_expr) = try_inline_set_discriminant_expr(
                    ctx,
                    ty,
                    *variant_index,
                    state.local_exprs.get(&place.local),
                )
            {
                state.write_local(place.local, discriminant_expr);
                return Some(());
            }
            if !matches!(ty.kind(), TyKind::RigidTy(RigidTy::Coroutine(..))) {
                // F6 (inline_walk_guard.rs): the new variant is lost for every
                // later read of the place.
                debug!(
                    bb_idx = walk_ctx.bb_idx,
                    local = place.local,
                    projection = ?place.projection,
                    "walker skip: SetDiscriminant not applied — fail closed"
                );
                ctx.record_sound_fallback_reason(WALKER_SET_DISCRIMINANT_DROPPED);
                if writes_through_deref {
                    ctx.heap_state.note_write();
                }
                return Some(());
            }
            let Some(updated) = apply_inline_coroutine_set_discriminant(
                ctx,
                walk_ctx,
                &state.local_exprs,
                place,
                ty,
                *variant_index,
            ) else {
                debug!(
                    bb_idx = walk_ctx.bb_idx,
                    local = place.local,
                    projection = ?place.projection,
                    "virtual body: coroutine SetDiscriminant cannot be tracked, bailing (#3807)"
                );
                return None;
            };
            state.write_local(place.local, updated);
            if let Some(receiver_updated) =
                rebuild_inline_coroutine_receiver(ctx, walk_ctx, &state.local_exprs, place, ty)
            {
                state.write_local(1, receiver_updated);
            }
            if writes_through_deref {
                ctx.heap_state.note_write();
            }
        }
        // Part of #4176: Intrinsic(Assume) encoded as path guard; CopyNonOverlapping dropped.
        StatementKind::Intrinsic(intrinsic) => match intrinsic {
            rustc_public::mir::NonDivergingIntrinsic::Assume(op) => {
                if let Some(cond_expr) = inline_operand_to_expr(
                    ctx,
                    op,
                    &state.local_exprs,
                    &walk_ctx.resolver,
                    walk_ctx.locals,
                )
                .and_then(inline_bool_condition)
                {
                    // Asserted, as Kani, not assumed: see the statement-level
                    // `NonDivergingIntrinsic::Assume` arm in `codegen_stmt`.
                    state.record_deferred_check(
                        trust_mc_core::violation::PropertyKind::Assumption,
                        Some("Rust intrinsic assumption failed".to_string()),
                        cond_expr,
                        ctx.heap_state.write_mark(),
                    );
                    debug!(bb_idx = walk_ctx.bb_idx, current_bb, "inline Assume checked");
                } else {
                    debug!(bb_idx = walk_ctx.bb_idx, current_bb, "inline Assume dropped");
                    ctx.record_sound_fallback_reason("inline_assume_intrinsic_check_dropped");
                }
            }
            rustc_public::mir::NonDivergingIntrinsic::CopyNonOverlapping(_) => {
                debug!(
                    bb_idx = walk_ctx.bb_idx,
                    current_bb, "inline walker: CopyNonOverlapping dropped (DEMOTED-equivalent)"
                );
                ctx.record_fallback();
            }
        },
        // Explicitly no-op (matching main encoder at codegen_stmt/mod.rs:738-744):
        StatementKind::StorageDead(local) => {
            ctx.forget_native_dyn_binding(*local);
            ctx.note_inline_mut_ref_assignment(walk_ctx.body, *local, None);
            if local_is_reference(ctx, walk_ctx.locals, *local) {
                ctx.forget_inline_walk_referent_local(*local);
            }
        }
        StatementKind::StorageLive(_)
        | StatementKind::FakeRead(..)
        | StatementKind::PlaceMention(..)
        | StatementKind::AscribeUserType { .. }
        | StatementKind::Coverage(..)
        | StatementKind::Nop
        | StatementKind::ConstEvalCounter => {}
        #[cfg(not(trust_toolchain))]
        StatementKind::Retag(..) => {}
    }
    Some(())
}

/// Whether `local` is an argument of the walked body declared as a reference
/// or raw pointer.
fn is_arg_pointer_local(ctx: &ChcCtx<'_, '_>, walk_ctx: &InlineWalkCtx<'_>, local: usize) -> bool {
    (1..=walk_ctx.body.arg_locals().len()).contains(&local)
        && walk_ctx.locals.get(local).is_some_and(|decl| {
            matches!(
                ctx.resolve_body_ty(decl.ty).kind(),
                TyKind::RigidTy(RigidTy::Ref(..) | RigidTy::RawPtr(..))
            )
        })
}

/// Which lane took a projected assignment.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum ProjectedAssignLane {
    /// The functional lane: the root local was rebound to the updated value.
    Rebound,
    /// The memory-store lane.
    Stored,
    /// Exact typed native heap/static SSA; the caller retains its address,
    /// and all observations use the shared memory chain, not a value rebind.
    NativeMemory,
    /// Skipped (recorded where it is lost).
    Skipped,
}

/// The Phase 0 records of one projected write to `place` that `lane` took,
/// `effects_before` being the heap effect mark before it
/// (`inline_walk_guard.rs`): the F1 exemption's rebind record and F3.
pub(super) fn note_projected_write_effects(
    ctx: &mut ChcCtx<'_, '_>,
    walk_ctx: &InlineWalkCtx<'_>,
    state: &mut InlineExecutionState,
    place: &rustc_public::mir::Place,
    lane: ProjectedAssignLane,
    effects_before: u64,
) {
    if lane == ProjectedAssignLane::NativeMemory {
        return;
    }
    let effect = ctx.heap_state.effect_mark() > effects_before;
    // The F1 exemption's record: a W2 rebind of the root, with no memory
    // effect (a mid-chain store) in the write.
    if lane == ProjectedAssignLane::Rebound
        && matches!(place.projection.first(), Some(rustc_public::mir::ProjectionElem::Deref))
        && !effect
    {
        ctx.note_inline_walk_rebind_write(place.local);
    }
    // F3 (inline_walk_guard.rs): a memory store through a reference or
    // pointer ARGUMENT, including a mid-chain store inside the functional
    // lane, reaches the heap arrays only. The caller's state variable is
    // written back from alias updates, which see no change, so it keeps the
    // old value. (A store through any other pointer is classified where the
    // store lanes make it, `note_inline_walk_lane_store`.)
    if lane != ProjectedAssignLane::Skipped
        && effect
        && is_arg_pointer_local(ctx, walk_ctx, place.local)
    {
        debug!(
            bb_idx = walk_ctx.bb_idx,
            local = place.local,
            "walker: memory-only write through a pointer argument — fail closed (F3)"
        );
        ctx.record_sound_fallback_reason(WALKER_DEREF_WRITEBACK_MEMORY_ONLY);
        state.memory_written_args.insert(place.local);
    }
}

/// A projected assignment (`(*p).f = v`, `*p = v`, `x.f = v`) inside an inline
/// walk: the functional lane, the memory-store lane, or a skip. `None` bails
/// the walk.
fn execute_inline_projected_assign<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    walk_ctx: &InlineWalkCtx<'_>,
    state: &mut InlineExecutionState,
    place: &rustc_public::mir::Place,
    rvalue: &rustc_public::mir::Rvalue,
    current_bb: usize,
) -> Option<ProjectedAssignLane> {
    // Part of #3561: projected assignments in &mut self methods.
    if let Some(rhs) = inline_assign_rvalue_expr(ctx, walk_ctx, rvalue, &state.local_exprs, None) {
        let rhs_vtable = match rvalue {
            rustc_public::mir::Rvalue::Use(
                rustc_public::mir::Operand::Copy(src) | rustc_public::mir::Operand::Move(src),
                ..,
            )
            | rustc_public::mir::Rvalue::Ref(_, _, src)
            | rustc_public::mir::Rvalue::CopyForDeref(src)
                if src.projection.is_empty() =>
            {
                state.inline_vtable_ids.get(&src.local).cloned()
            }
            _ => None,
        };
        if let Some(lane) =
            write_inline_projected_value(ctx, walk_ctx, state, place, rhs, rhs_vtable, 0)
        {
            return Some(lane);
        }
    }
    // Part of #4014 refinement: FnMut closure capture writes through
    // `(*_1).field = rhs` must NOT be skipped — they are semantic side
    // effects (the mutation the closure body performs). Bail so closure
    // dispatch returns `false` and virtual dispatch handles the FnMut
    // call with proper &mut writeback via resolve_mut_ref_value_args.
    if place.local == 1 {
        if let PlaceResolver::Captures(_) = &walk_ctx.resolver {
            debug!(
                bb_idx = walk_ctx.bb_idx,
                current_bb,
                local = place.local,
                "walker bail: closure capture deref-write — defer to virtual dispatch"
            );
            return None;
        }
    }
    // Part of #4014: When a projected deref write has an untranslatable
    // RHS (e.g., `(*_1) = (_2.0)` where `_2` wasn't populated due to
    // a deref-through-static width mismatch), skip instead of bailing
    // IF the target is a Deref-prefixed write. Such writes are memory
    // side effects (static-mut updates) that don't affect the return value.
    // Bailing would lose all return-value information -> unconstrained fallback.
    if matches!(place.projection.first(), Some(rustc_public::mir::ProjectionElem::Deref)) {
        // FC-06: the dropped store is invisible to every frame check.
        if ctx.in_modifies_frame_extent() {
            ctx.modifies_frame_fail_closed("walker dropped deref write (untranslatable rhs)");
        }
        // F6 (inline_walk_guard.rs): the write is lost for every reader, not
        // only for a frame check.
        ctx.record_sound_fallback_reason(WALKER_DEREF_WRITE_DROPPED);
        debug!(
            bb_idx = walk_ctx.bb_idx,
            current_bb,
            local = place.local,
            "walker skip: deref-write with untranslatable RHS (#4014) — fail closed"
        );
        return Some(ProjectedAssignLane::Skipped);
    }
    // Part of #4099: skip instead of bail -- unpopulated local
    // cascades through existing gap-recording path.
    if ctx.in_modifies_frame_extent()
        && place.projection.iter().any(|p| matches!(p, rustc_public::mir::ProjectionElem::Deref))
    {
        ctx.modifies_frame_fail_closed("walker dropped projected deref write");
    }
    // F6: a populated local keeps its old value for every later read (an
    // unpopulated one fails on its own gap-recording path).
    if state.local_exprs.contains_key(&place.local) {
        ctx.record_sound_fallback_reason(WALKER_DEREF_WRITE_DROPPED);
    }
    debug!(
        bb_idx = walk_ctx.bb_idx,
        current_bb,
        local = place.local,
        "walker skip: projected assignment (#3236->#4099)"
    );
    Some(ProjectedAssignLane::Skipped)
}

/// The functional lane or the memory-store lane for a projected write of the
/// translated `rhs`: a statement's, a call destination's, or a write
/// `referent_write.rs` retargets to a referent (`hops` counts those). `None`
/// when neither lane takes it; the caller skips, bails or records the loss.
pub(super) fn write_inline_projected_value(
    ctx: &mut ChcCtx<'_, '_>,
    walk_ctx: &InlineWalkCtx<'_>,
    state: &mut InlineExecutionState,
    place: &rustc_public::mir::Place,
    rhs: Expr,
    rhs_vtable: Option<Expr>,
    hops: usize,
) -> Option<ProjectedAssignLane> {
    let leading_deref =
        matches!(place.projection.first(), Some(rustc_public::mir::ProjectionElem::Deref));
    if ctx.native_drop_memory.is_some() && leading_deref {
        if ctx.store_native_drop_place(&state.local_exprs, place, walk_ctx.locals, &rhs)
            == Some(true)
        {
            return Some(ProjectedAssignLane::NativeMemory);
        }
        if ctx.native_drop_static_store(&state.local_exprs, place, walk_ctx.locals)
            && try_inline_memory_store(
                ctx,
                walk_ctx.locals,
                &state.local_exprs,
                place,
                rhs.clone(),
                None,
            )
        {
            return Some(ProjectedAssignLane::NativeMemory);
        }
    }
    // A Deref-first write whose root term is a memory address: the functional
    // lane below loads the pointee, updates it and REBINDS the pointer local
    // to the value, writing no memory (W2).
    let rebinds_memory_pointee = leading_deref
        && state.local_exprs.get(&place.local).is_some_and(|root| {
            let pointee_ty = walk_ctx.locals.get(place.local).and_then(|decl| {
                super::projected_assign_helpers::inline_deref_pointee_ty(
                    ctx,
                    ctx.resolve_body_ty(decl.ty),
                )
            });
            super::projected_assign::inline_deref_target_addr(root, pointee_ty).is_some()
        });
    // Part of #3828: functional projected-assign path.
    if let Some(updated) =
        apply_inline_projected_assign(ctx, walk_ctx.locals, &state.local_exprs, place, rhs.clone())
    {
        state.write_local(place.local, updated);
        // An argument's rebound value reaches the caller as an alias update; a
        // non-argument local's reaches nothing by itself.
        if leading_deref && !(1..=walk_ctx.body.arg_locals().len()).contains(&place.local) {
            if rebinds_memory_pointee {
                // The memory cell it came from keeps the old value.
                debug!(
                    bb_idx = walk_ctx.bb_idx,
                    local = place.local,
                    "walker: deref write rebinds a non-argument pointer local — write lost"
                );
                ctx.record_sound_fallback_reason(WALKER_DEREF_WRITE_REBIND_LOST);
            } else {
                // M1: the local's term was its referent's value; the referent
                // keeps the old one unless the write reaches it too.
                super::referent_write::write_through_nonarg_referent(
                    ctx, walk_ctx, state, place, &rhs, rhs_vtable, hops,
                );
            }
        }
        return Some(ProjectedAssignLane::Rebound);
    }
    // Part of #3793: memory store for heap/static pointer writes.
    if try_inline_memory_store(ctx, walk_ctx.locals, &state.local_exprs, place, rhs, rhs_vtable) {
        return Some(ProjectedAssignLane::Stored);
    }
    None
}

/// F2 (inline_walk_guard.rs): whether assigning `rvalue` to a reference-typed
/// local leaves an ADDRESS in it rather than the referent value the walker's
/// transparent `Deref` reads it as: a copy or cast of an address-bound local,
/// a reborrow that took the address lane (or reborrows an address-bound
/// local), a local's address hint, or a reference read through a pointer
/// (memory holds a reference as its address).
fn rvalue_yields_address(
    ctx: &ChcCtx<'_, '_>,
    walk_ctx: &InlineWalkCtx<'_>,
    rvalue: &rustc_public::mir::Rvalue,
) -> bool {
    use rustc_public::mir::{Operand, Rvalue};
    let reads_through_pointer = |src: &rustc_public::mir::Place| place_writes_through_deref(src);
    match rvalue {
        Rvalue::Use(Operand::Copy(src) | Operand::Move(src), ..) | Rvalue::CopyForDeref(src) => {
            if src
                .ty(walk_ctx.locals)
                .ok()
                .is_some_and(|ty| ctx.readonly_ref_value_matches(&Operand::Copy(src.clone()), ty))
            {
                return false;
            }
            (src.projection.is_empty() && ctx.inline_walk_local_is_address(src.local))
                || (reads_through_pointer(src)
                    && matches!(walk_ctx.resolver, PlaceResolver::FieldMap(_)))
        }
        Rvalue::Cast(_, Operand::Copy(src) | Operand::Move(src), _) => {
            src.projection.is_empty() && ctx.inline_walk_local_is_address(src.local)
        }
        Rvalue::Ref(_, _, src) | Rvalue::AddressOf(_, src) => {
            ctx.last_inline_ref_was_address
                || (src.projection.is_empty()
                    && ctx.inline_local_address_hint(walk_ctx.body, src.local).is_some())
                || (reads_through_pointer(src) && ctx.inline_walk_local_is_address(src.local))
        }
        _ => false,
    }
}

/// F2 residual (inline_walk_guard.rs): whether `local` is an argument of the
/// walked body that the walk did not build and whose fields it cannot read
/// exactly: every argument, except a closure's environment under the capture
/// resolver (local 1, whose fields the capture map resolves).
fn is_unbuilt_argument(walk_ctx: &InlineWalkCtx<'_>, local: usize) -> bool {
    let first = if matches!(walk_ctx.resolver, PlaceResolver::Captures(_)) { 2 } else { 1 };
    (first..=walk_ctx.body.arg_locals().len()).contains(&local)
}

/// F2 residual (inline_walk_guard.rs): whether reading `place` whole may yield
/// a value that holds an ADDRESS in one of its fields, where the walker's
/// transparent `Deref` of a reference copied out of it would read the address
/// bits as the referent:
/// * a by-value argument, or a field of one ([`is_unbuilt_argument`]): the
///   caller built it, and its reference fields are addresses, or bits of one
///   when a BV-flattened `Option<&T>` types its payload by the referent;
/// * an address-bound reference, or a local (or a field of one) the walk
///   marked address-carrying;
/// * a place read through a pointer under the field-map resolver (memory holds
///   a reference as its address).
fn place_may_carry_address(
    ctx: &ChcCtx<'_, '_>,
    walk_ctx: &InlineWalkCtx<'_>,
    place: &rustc_public::mir::Place,
) -> bool {
    if place_writes_through_deref(place) {
        return matches!(walk_ctx.resolver, PlaceResolver::FieldMap(_));
    }
    if ctx.inline_walk_local_carries_address(place.local) {
        return true;
    }
    if place.projection.is_empty() {
        // A whole reference local carries an address exactly when it is
        // address-bound (its binder decided); a whole aggregate argument may.
        return if local_is_reference(ctx, walk_ctx.locals, place.local) {
            ctx.inline_walk_local_is_address(place.local)
        } else {
            is_unbuilt_argument(walk_ctx, place.local)
        };
    }
    is_unbuilt_argument(walk_ctx, place.local)
}

/// F2 residual: whether assigning `rvalue` to a NON-reference local (or, with
/// `projected`, to a field of one) may leave an address inside it: a copy,
/// cast or repeat of such a value, or an aggregate with such an operand
/// ([`place_may_carry_address`]). A borrow written into a field is counted as
/// one too: whether it took the address lane is decided while it is written.
fn rvalue_carries_address(
    ctx: &ChcCtx<'_, '_>,
    walk_ctx: &InlineWalkCtx<'_>,
    rvalue: &rustc_public::mir::Rvalue,
    projected: bool,
) -> bool {
    use rustc_public::mir::{Operand, Rvalue};
    let operand_carries = |operand: &Operand| match operand {
        Operand::Copy(place) | Operand::Move(place) => {
            place_may_carry_address(ctx, walk_ctx, place)
        }
        Operand::Constant(_) => false,
        // A `cfg!(ub_checks|contract_checks|overflow_checks)` flag read at
        // codegen time: a `bool`, never an address or bits of one.
        #[cfg(trust_toolchain)]
        Operand::RuntimeChecks(_) => false,
    };
    match rvalue {
        Rvalue::Use(operand, ..) | Rvalue::Cast(_, operand, _) | Rvalue::Repeat(operand, _) => {
            operand_carries(operand)
        }
        Rvalue::Aggregate(_, operands) => operands.iter().any(operand_carries),
        Rvalue::CopyForDeref(place) => place_may_carry_address(ctx, walk_ctx, place),
        Rvalue::Ref(..) | Rvalue::AddressOf(..) => projected,
        _ => false,
    }
}

/// F2 residual (inline_walk_guard.rs): a reference copied (or cast) out of a
/// field, variant payload or element of a by-value argument of the walked body
/// (`_5 = deref_copy (_2.0)`, `((_2 as Some).0)`), or of a local the walk
/// marked address-carrying (`let pair = (w.k, w.r); *pair.1`). The walk never
/// saw how the caller bound that field, and a caller's reference field is an
/// address, or bits of one: a BV-flattened `Option<&T>` types its payload by
/// the referent, so the caller's `Some(&x)` reaches the walk as the low bits
/// of x's address, or as another term built from them (a `bool`, a tuple, an
/// array). No term shape tells such bits from the referent's value, so the
/// reference is address-bound whatever its term; its read fails closed. A
/// closure's arguments are covered under the capture resolver too; only its
/// environment is excluded ([`is_unbuilt_argument`]).
fn rvalue_reads_field_address(
    ctx: &ChcCtx<'_, '_>,
    walk_ctx: &InlineWalkCtx<'_>,
    rvalue: &rustc_public::mir::Rvalue,
) -> bool {
    use rustc_public::mir::{Operand, Rvalue};
    let src = match rvalue {
        Rvalue::Use(Operand::Copy(src) | Operand::Move(src), ..)
        | Rvalue::CopyForDeref(src)
        | Rvalue::Cast(_, Operand::Copy(src) | Operand::Move(src), _) => src,
        _ => return false,
    };
    if src
        .ty(walk_ctx.locals)
        .ok()
        .is_some_and(|ty| ctx.readonly_ref_value_matches(&Operand::Copy(src.clone()), ty))
    {
        return false;
    }
    if !src.projection.is_empty()
        && src.ty(walk_ctx.locals).ok().is_some_and(|ty| ctx.readonly_scalar_pointee(ty).is_some())
    {
        // This may be the address, a truncated address, or a logical value.
        // Address-like taint alone cannot authorize a later pointer observer.
        ctx.record_sound_fallback_reason("inline_projected_reference_value_unmodeled");
    }
    !src.projection.is_empty()
        && (src
            .ty(walk_ctx.locals)
            .ok()
            .is_some_and(|ty| ctx.readonly_scalar_pointee(ty).is_some())
            || is_unbuilt_argument(walk_ctx, src.local)
            || ctx.inline_walk_local_carries_address(src.local))
}

fn inline_alloc_source_local(rvalue: &rustc_public::mir::Rvalue) -> Option<usize> {
    match rvalue {
        rustc_public::mir::Rvalue::Use(
            rustc_public::mir::Operand::Copy(src) | rustc_public::mir::Operand::Move(src),
            ..,
        ) if src.projection.is_empty() => Some(src.local),
        _ => None,
    }
}

/// Translate an inline rvalue, with address-hint short-circuit for Ref/AddressOf.
pub(super) fn inline_assign_rvalue_expr<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    walk_ctx: &InlineWalkCtx<'_>,
    rvalue: &rustc_public::mir::Rvalue,
    local_exprs: &HashMap<usize, Expr>,
    dest_local: Option<usize>,
) -> Option<Expr> {
    let resolver = walk_ctx.resolver;
    if let rustc_public::mir::Rvalue::Discriminant(place) = rvalue
        && let Some(expr) = try_inline_unit_enum_discriminant_expr(
            ctx,
            &resolver,
            place,
            local_exprs,
            walk_ctx.locals,
        )
    {
        return Some(expr);
    }
    if let Some(expr) = try_inline_adt_variant_assign_expr(
        ctx,
        rvalue,
        local_exprs,
        &resolver,
        walk_ctx.locals,
        dest_local,
    ) {
        return Some(expr);
    }
    match rvalue {
        rustc_public::mir::Rvalue::AddressOf(_, place) if place.projection.is_empty() => {
            ctx.inline_local_address_hint(walk_ctx.body, place.local).or_else(|| {
                inline_rvalue_to_expr(
                    ctx,
                    rvalue,
                    local_exprs,
                    &resolver,
                    walk_ctx.locals,
                    dest_local,
                )
            })
        }
        rustc_public::mir::Rvalue::Ref(_, _, place)
            if place
                .ty(walk_ctx.locals)
                .ok()
                .is_some_and(|ty| ctx.readonly_scalar_pointee(ty).is_some()) =>
        {
            inline_rvalue_to_expr(ctx, rvalue, local_exprs, &resolver, walk_ctx.locals, dest_local)
        }
        rustc_public::mir::Rvalue::Ref(_, _, place) if place.projection.is_empty() => {
            // ZST address hints must take priority over local_exprs for Ref/AddressOf.
            // local_exprs maps ZST params to their canonical Bool values (the ZST content),
            // but &zst needs the *address* (BV64), not the value. Without this priority,
            // `&a as *const Void` returns Bool instead of a non-null BV64 address,
            // causing downstream `!= null` assertions to fail with sort mismatch
            // or unconditional __assert_fail_inline.
            ctx.inline_local_address_hint(walk_ctx.body, place.local)
                .or_else(|| local_exprs.get(&place.local).cloned())
                .or_else(|| {
                    inline_rvalue_to_expr(
                        ctx,
                        rvalue,
                        local_exprs,
                        &resolver,
                        walk_ctx.locals,
                        dest_local,
                    )
                })
        }
        _ => {
            inline_rvalue_to_expr(ctx, rvalue, local_exprs, &resolver, walk_ctx.locals, dest_local)
        }
    }
}

// Gap classification extracted to gap_classify.rs for file-size compliance.
use super::gap_classify::classify_rvalue_gap;
