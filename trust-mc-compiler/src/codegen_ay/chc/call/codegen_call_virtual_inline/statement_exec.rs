// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Statement execution for the inline body walker.
//! Part of #3913: extracted from walker.rs statement loop.
//! Discriminant and ADT variant helpers split to statement_exec_helpers.rs
//! per #4206.

use ay_bindings::Expr;
use rustc_public::mir::StatementKind;
use rustc_public::ty::{RigidTy, TyKind};
use std::collections::HashMap;
use tracing::debug;

use super::super::ChcCtx;
use super::super::inline_shared::{PlaceResolver, inline_operand_to_expr, inline_rvalue_to_expr};
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
use super::statement_metadata::propagate_inline_subslice_metadata;
use super::vtable_prop::propagate_inline_vtable;

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
    match &stmt.kind {
        StatementKind::Assign(place, rvalue) => {
            if !place.projection.is_empty() {
                // Part of #3561: projected assignments in &mut self methods.
                if let Some(rhs) =
                    inline_assign_rvalue_expr(ctx, walk_ctx, rvalue, &state.local_exprs, None)
                {
                    let rhs_vtable = match rvalue {
                        rustc_public::mir::Rvalue::Use(
                            rustc_public::mir::Operand::Copy(src)
                            | rustc_public::mir::Operand::Move(src),
                        )
                        | rustc_public::mir::Rvalue::Ref(_, _, src)
                        | rustc_public::mir::Rvalue::CopyForDeref(src)
                            if src.projection.is_empty() =>
                        {
                            state.inline_vtable_ids.get(&src.local).cloned()
                        }
                        _ => None,
                    };
                    // Part of #3828: functional projected-assign path.
                    if let Some(updated) = apply_inline_projected_assign(
                        ctx,
                        walk_ctx.locals,
                        &state.local_exprs,
                        place,
                        rhs.clone(),
                    ) {
                        state.write_local(place.local, updated);
                        return Some(());
                    }
                    // Part of #3793: memory store for heap/static pointer writes.
                    if try_inline_memory_store(
                        ctx,
                        walk_ctx.locals,
                        &state.local_exprs,
                        place,
                        rhs,
                        rhs_vtable,
                    ) {
                        return Some(());
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
                if matches!(
                    place.projection.first(),
                    Some(rustc_public::mir::ProjectionElem::Deref)
                ) {
                    debug!(
                        bb_idx = walk_ctx.bb_idx,
                        current_bb,
                        local = place.local,
                        "walker skip: deref-write with untranslatable RHS (#4014)"
                    );
                    return Some(());
                }
                // Part of #4099: skip instead of bail -- unpopulated local
                // cascades through existing gap-recording path.
                debug!(
                    bb_idx = walk_ctx.bb_idx,
                    current_bb,
                    local = place.local,
                    "walker skip: projected assignment (#3236->#4099)"
                );
                return Some(());
            }
            let resolved_expr = inline_assign_rvalue_expr(
                ctx,
                walk_ctx,
                rvalue,
                &state.local_exprs,
                Some(place.local),
            );
            if let Some(expr) = resolved_expr {
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
                state.write_local_with_alloc_id(place.local, expr, src_alloc_id);
            } else {
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
        }
        StatementKind::SetDiscriminant { place, variant_index } => {
            let Ok(ty) = place.ty(walk_ctx.locals) else {
                return None;
            };
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
                    state.assume_guards.push(cond_expr);
                    debug!(bb_idx = walk_ctx.bb_idx, current_bb, "inline Assume encoded");
                } else {
                    debug!(bb_idx = walk_ctx.bb_idx, current_bb, "inline Assume dropped");
                    ctx.record_sound_fallback_reason("inline_assume_guard_dropped");
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
        StatementKind::StorageLive(_)
        | StatementKind::StorageDead(_)
        | StatementKind::FakeRead(..)
        | StatementKind::PlaceMention(..)
        | StatementKind::AscribeUserType { .. }
        | StatementKind::Coverage(..)
        | StatementKind::Nop
        | StatementKind::ConstEvalCounter
        | StatementKind::Retag(..) => {}
    }
    Some(())
}

fn inline_alloc_source_local(rvalue: &rustc_public::mir::Rvalue) -> Option<usize> {
    match rvalue {
        rustc_public::mir::Rvalue::Use(
            rustc_public::mir::Operand::Copy(src) | rustc_public::mir::Operand::Move(src),
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
        rustc_public::mir::Rvalue::Ref(_, _, place)
        | rustc_public::mir::Rvalue::AddressOf(_, place)
            if place.projection.is_empty() =>
        {
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
