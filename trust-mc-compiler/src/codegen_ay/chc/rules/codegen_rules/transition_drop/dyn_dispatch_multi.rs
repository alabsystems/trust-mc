// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! D2 multi-impl dyn drop dispatch for CHC encoding.
//!
//! Handles the case where multiple concrete drop bodies exist for a
//! `dyn Trait` type. Each candidate gets its own CHC rule guarded by
//! a vtable discriminant match.
//!
//! Split from `dyn_dispatch.rs` — Part of #3927.

use ay_bindings::Expr;
use tracing::debug;

use crate::codegen_ay::chc::ChcCtx;
use crate::codegen_ay::chc::call::inline_body::{
    extract_inline_assert_guard, translate_inline_body,
};

use super::super::{CodegenRules, TransitionContext};
use super::baseline::restore_dyn_drop_d2_candidate_baseline;
use super::dyn_dispatch::seed_box_new_payload_vtable;
use super::emit_helpers::{emit_inline_guard_error, vtable_guard};

/// Resolve the vtable discriminant expression for D2 multi-impl dispatch.
///
/// Part of #3793: When the dropped local's vtable state var was NOT modified
/// in this block, use the INPUT name. When modified, use the OUTPUT name so
/// the propagation constraint transitively resolves the source.
pub(super) fn resolve_d2_vtable_discriminant(
    ctx: &mut ChcCtx<'_, '_>,
    place: &rustc_public::mir::Place,
    tctx: &TransitionContext<'_>,
) -> Expr {
    if let Some((in_name, out_name)) = ctx.vtable_state_vars.get(&place.local) {
        let in_idx = ctx.state_var_index_by_name(in_name);
        let modified_in_block =
            in_idx.map_or(false, |idx| ctx.encode.modified_state_indices.contains(&idx));
        let use_name = if modified_in_block { out_name } else { in_name };
        debug!(
            local = place.local,
            modified_in_block, "Drop(dyn) D2: vtable guard variable (#3793)"
        );
        Expr::var(&**use_name, ay_bindings::Sort::bitvec(crate::codegen_ay::types::POINTER_WIDTH))
    } else {
        resolve_d2_vtable_disc_general(ctx, place, tctx)
    }
}

/// Resolve vtable discriminant via general extraction when no direct
/// vtable state var exists.
fn resolve_d2_vtable_disc_general(
    ctx: &mut ChcCtx<'_, '_>,
    place: &rustc_public::mir::Place,
    tctx: &TransitionContext<'_>,
) -> Expr {
    let place_expr = ctx.translate_place_with_modified(place, tctx.modified_locals);
    let receiver_local = Some(place.local);
    let disc = if let Some(ref pe) = place_expr {
        ctx.try_extract_vtable_discriminant(std::slice::from_ref(pe), receiver_local)
    } else {
        ctx.try_extract_vtable_discriminant(&[], receiver_local)
    };
    // Part of #3793: If the discriminant resolved to a vtable state var's
    // OUTPUT name, replace with the INPUT name.
    let disc_str = format!("{disc}");
    if disc_str.ends_with("__out") {
        let in_candidate = &disc_str[..disc_str.len() - 5];
        if ctx.state_var_index_by_name(in_candidate).is_some() {
            debug!(
                disc_out = %disc_str,
                disc_in = %in_candidate,
                "Drop(dyn) D2: rewrote vtable disc from __out to INPUT (#3793)"
            );
            Expr::var(
                in_candidate,
                ay_bindings::Sort::bitvec(crate::codegen_ay::types::POINTER_WIDTH),
            )
        } else {
            disc
        }
    } else {
        disc
    }
}

/// Execute D2 multi-impl dispatch: emit one guarded CHC rule per candidate.
///
/// Each candidate gets `shared_constraints /\ vtable_disc == vtable_id /\
/// inline_effects -> target`. The solver picks the rule whose vtable guard
/// is satisfiable.
///
/// Returns `true` if at least one candidate was emitted.
pub(super) fn dispatch_d2_multi_impl(
    ctx: &mut ChcCtx<'_, '_>,
    place: &rustc_public::mir::Place,
    self_expr: &Expr,
    vtable_disc: &Expr,
    drop_bodies: &[(u64, rustc_public::mir::Body, rustc_public::mir::mono::Instance)],
    target: usize,
    tctx: &TransitionContext<'_>,
    dealloc_extras: &[Expr],
) -> bool {
    let baseline_modified = ctx.encode.modified_state_indices.clone();
    let baseline_heap = ctx.heap_state.snapshot_transient_rule_state();
    debug!(
        local = place.local,
        vtable_disc = %vtable_disc,
        "D2 vtable guard resolved"
    );
    let mut any_inlined = false;

    for (vtable_id, body, drop_instance) in drop_bodies {
        restore_dyn_drop_d2_candidate_baseline(ctx, &baseline_modified, &baseline_heap);

        let params = [self_expr.clone()];
        // Part of #4097: Register callee statics before inlining.
        ctx.register_callee_body_statics(body);
        ctx.mark_inline_field_reads(body, &params, tctx.bb_idx);
        let mut caller_vtable_ids = std::collections::HashMap::new();
        caller_vtable_ids.insert(1, vtable_disc.clone());
        seed_box_new_payload_vtable(ctx, place.local, body, &mut caller_vtable_ids);
        let inline_result = translate_inline_body(
            ctx,
            body,
            &params,
            tctx.bb_idx,
            &caller_vtable_ids,
            Some(*drop_instance),
            0,
        );
        if let Some(inline_result) = inline_result {
            emit_d2_inlined_candidate(
                ctx,
                vtable_disc,
                *vtable_id,
                &inline_result.value,
                target,
                tctx,
                dealloc_extras,
            );
            debug!(
                bb_idx = tctx.bb_idx,
                vtable_id = *vtable_id,
                has_dealloc = !dealloc_extras.is_empty(),
                "CHC: Drop(dyn) → multi-impl candidate inlined ({})",
                drop_instance.name()
            );
            any_inlined = true;
        } else {
            // Keep fallback emission isolated from any partial heap effects.
            restore_dyn_drop_d2_candidate_baseline(ctx, &baseline_modified, &baseline_heap);
            emit_d2_fallback_candidate(ctx, vtable_disc, *vtable_id, target, tctx, dealloc_extras);
            debug!(
                bb_idx = tctx.bb_idx,
                vtable_id = *vtable_id,
                "CHC: Drop(dyn) D2 → fallback for failed candidate ({})",
                drop_instance.name()
            );
            any_inlined = true;
        }
    }

    restore_dyn_drop_d2_candidate_baseline(ctx, &baseline_modified, &baseline_heap);
    any_inlined
}

/// Emit a successfully-inlined D2 candidate's transition rule.
fn emit_d2_inlined_candidate(
    ctx: &mut ChcCtx<'_, '_>,
    vtable_disc: &Expr,
    vtable_id: u64,
    inline_value: &Expr,
    target: usize,
    tctx: &TransitionContext<'_>,
    dealloc_extras: &[Expr],
) {
    let inline_guard = extract_inline_assert_guard(inline_value);
    emit_inline_guard_error(
        ctx,
        tctx.from_app,
        tctx.shared_constraints,
        tctx.bb_idx,
        inline_guard.as_ref(),
    );
    for check in ctx.heap_state.pending_checks.drain(..).collect::<Vec<_>>() {
        ctx.emit_error_rule_for_condition_shared(
            tctx.from_app,
            check,
            tctx.shared_constraints,
            tctx.bb_idx,
        );
    }
    let mut extra_constraints = Vec::new();
    extra_constraints.append(&mut ctx.heap_state.pending_updates);
    extra_constraints.append(&mut ctx.heap_state.drain_store_chains(&ctx.diagnostics));
    extra_constraints.extend(inline_guard);
    extra_constraints.push(vtable_guard(vtable_disc, vtable_id));
    extra_constraints.extend_from_slice(dealloc_extras);
    let new_output_args = ctx.build_block_output_args(tctx.modified_locals, None);
    ctx.emit_goto_rule_shared_extra(
        tctx.from_app,
        target,
        &new_output_args,
        tctx.shared_constraints,
        extra_constraints,
    );
}

/// Emit a sound fallback rule for a D2 candidate whose inline walk failed.
///
/// Part of #3804: Without this, a failed candidate gets NO transition rule.
/// The solver then cannot reach any state through that vtable_id, potentially
/// hiding bugs reachable only through the failed candidate's drop path.
fn emit_d2_fallback_candidate(
    ctx: &mut ChcCtx<'_, '_>,
    vtable_disc: &Expr,
    vtable_id: u64,
    target: usize,
    tctx: &TransitionContext<'_>,
    dealloc_extras: &[Expr],
) {
    let mut fallback_constraints = Vec::new();
    fallback_constraints.push(vtable_guard(vtable_disc, vtable_id));
    fallback_constraints.extend_from_slice(dealloc_extras);
    ctx.emit_goto_rule_shared_extra(
        tctx.from_app,
        target,
        tctx.output_args,
        tctx.shared_constraints,
        fallback_constraints,
    );
    ctx.record_sound_fallback_categorized("dyn_drop_d2_partial_inline");
}
