// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Exact native Box drop: execute the concrete glue, then free the owner.

use super::super::{CodegenRules, TransitionContext};
use super::{
    box_drop::collect_box_dyn_dealloc_effects,
    effects::{
        compose_box_deallocation_updates, compose_host_drop_constraints,
        metadata_observers_are_inputs, require_native_deallocation_extent,
    },
};
use crate::callee_body::CalleeBody;
use crate::codegen_ay::chc::{
    ChcCtx,
    call::{
        inline_body::{
            InlineReturn, extract_inline_assert_guard, translate_inline_body, walk_drop_body,
        },
        native_dyn_origin::NativeDynOrigin,
    },
};
use crate::codegen_ay::shared::{
    mono_ty,
    native_box_drop::native_global_box_pointee,
    native_box_raw::{native_bmc_has_custom_global_allocator, native_thin_global_box_pointee},
};
#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use ay_bindings::Expr;
use rustc_public::mir::{Mutability, Operand, Place};
use rustc_public::ty::{RigidTy, Ty, TyKind};
use std::collections::HashMap;

pub(in crate::codegen_ay::chc) fn append_outer_free(
    ctx: &mut ChcCtx<'_, '_>,
    pointer: Expr,
    id: Option<u32>,
) -> Option<()> {
    let effects = collect_box_dyn_dealloc_effects(ctx, pointer, id)?;
    let updates = compose_box_deallocation_updates(ctx, &effects.pending_updates)?;
    ctx.heap_state.pending_checks.extend(effects.pending_checks);
    ctx.heap_state.pending_updates.extend(updates);
    Some(())
}

/// Both the host and walked drop front doors use this exact typed operation.
/// A failed walk restores partial effects and retains hard refusal.
pub(in crate::codegen_ay::chc) fn translate_native_dyn_box_drop(
    ctx: &mut ChcCtx<'_, '_>,
    ty: Ty,
    origin: &NativeDynOrigin,
    bb: usize,
    depth: usize,
) -> Option<InlineReturn> {
    let heap = ctx.heap_state.snapshot_transient_rule_state();
    let modified = ctx.encode.modified_state_indices.clone();
    let result = (|| {
        if native_global_box_pointee(ctx.tcx, ty)? != origin.dynamic
            || native_bmc_has_custom_global_allocator(ctx.tcx)
            || ctx.get_type_size(origin.concrete)? == 0
        {
            return None;
        }
        let pointer =
            Expr::bitvec_const(origin.allocation, 32).concat(Expr::bitvec_const(0u32, 32));
        let checked = ctx.checked_native_dyn_pointer(pointer.clone(), origin)?;
        ctx.heap_state.pending_checks.extend(checked.checks);
        let glue = mono_ty::drop_in_place(origin.concrete)?;
        let result = if glue.is_empty_shim() {
            InlineReturn::value_only(Expr::bool_const(true))
        } else {
            let body = glue.callee_body()?;
            ctx.register_callee_body_consts(&body);
            ctx.mark_inline_field_reads(&body, std::slice::from_ref(&pointer), bb);
            ctx.with_native_drop_memory(origin, |ctx| {
                walk_drop_body(ctx, |ctx| {
                    translate_inline_body(
                        ctx,
                        &body,
                        std::slice::from_ref(&pointer),
                        bb,
                        &HashMap::new(),
                        Some(glue),
                        depth + 1,
                    )
                })
            })?
        };
        let observers = result
            .deferred_checks
            .iter()
            .map(|check| check.check.clone())
            .chain(std::iter::once(result.value.clone()))
            .collect::<Vec<_>>();
        if !metadata_observers_are_inputs(ctx, &observers) {
            return None;
        }
        let bytes = u32::try_from(ctx.get_type_size(origin.concrete)?).ok()?;
        require_native_deallocation_extent(ctx, Expr::bitvec_const(origin.allocation, 32), bytes)?;
        append_outer_free(ctx, pointer, Some(origin.allocation))?;
        Some(result)
    })();
    if result.is_none() {
        ctx.heap_state.restore_transient_rule_state(&heap);
        ctx.encode.modified_state_indices = modified;
        ctx.record_sound_fallback_reason("native_box_drop_origin_or_effects_unmodeled");
    }
    result
}

/// A walked thin Box whose pointee glue is empty still owns an actual free.
/// General user destructors must execute their own body.
pub(in crate::codegen_ay::chc) fn translate_native_thin_box_free(
    ctx: &mut ChcCtx<'_, '_>,
    ty: Ty,
    value: Expr,
) -> Option<()> {
    let inner = native_thin_global_box_pointee(ctx.tcx, ty)?;
    if ctx.get_type_size(inner)? == 0 {
        return None;
    }
    if native_bmc_has_custom_global_allocator(ctx.tcx)
        || !mono_ty::drop_in_place(inner)?.is_empty_shim()
    {
        return None;
    }
    let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() else { return None };
    let carrier = mono_ty::field_ty(def.variants().first()?.fields().first()?, &args)?;
    let target = Ty::from_rigid_kind(RigidTy::RawPtr(inner, Mutability::Mut));
    let checked = ctx.checked_native_box_deref(carrier, target, value)?;
    ctx.heap_state.pending_checks.extend(checked.checks);
    let bytes = u32::try_from(ctx.get_type_size(inner)?).ok()?;
    require_native_deallocation_extent(ctx, checked.value.clone().extract(63, 32), bytes)?;
    append_outer_free(ctx, checked.value, None)
}

pub(in crate::codegen_ay::chc) fn codegen_native_dyn_box_drop(
    ctx: &mut ChcCtx<'_, '_>,
    place: &Place,
    ty: Ty,
    target: usize,
    tctx: &TransitionContext<'_>,
) {
    let origins = ctx.host_native_dyn_drop_origins(&Operand::Copy(place.clone()));
    let Some(origins) = origins else {
        ctx.record_sound_fallback_reason("native_box_drop_exact_origin_required");
        ctx.emit_goto_rule_shared(tctx.from_app, target, tctx.output_args, tctx.shared_constraints);
        return;
    };
    if origins.len() == 1 {
        let result = translate_native_dyn_box_drop(ctx, ty, &origins[0], tctx.bb_idx, 0);
        emit_native_drop_result(ctx, result, target, tctx);
        return;
    }
    // The whole-definition certificate above exhausts actual native Unsize
    // producers. Every distinct metadata ID names exactly one allocation.
    // A global candidate universe or an unconstrained metadata guess does not
    // establish this coverage. Require the real propagated metadata lane.
    if !ctx.vtable_state_vars.contains_key(&place.local) {
        ctx.record_sound_fallback_reason("native_box_drop_join_metadata_unavailable");
        ctx.emit_goto_rule_shared(tctx.from_app, target, tctx.output_args, tctx.shared_constraints);
        return;
    }
    let disc = super::dyn_dispatch_multi::resolve_d2_vtable_discriminant(ctx, place, tctx);
    let heap = ctx.heap_state.snapshot_transient_rule_state();
    let modified = ctx.encode.modified_state_indices.clone();
    for origin in origins {
        ctx.heap_state.restore_transient_rule_state(&heap);
        ctx.encode.modified_state_indices = modified.clone();
        let mut guarded = tctx.shared_constraints.to_vec();
        guarded.push(disc.clone().eq(origin.vtable_expr()));
        let guarded = std::sync::Arc::from(guarded);
        let branch = TransitionContext { shared_constraints: &guarded, ..*tctx };
        let result = translate_native_dyn_box_drop(ctx, ty, &origin, tctx.bb_idx, 0);
        emit_native_drop_result(ctx, result, target, &branch);
    }
    ctx.heap_state.restore_transient_rule_state(&heap);
    ctx.encode.modified_state_indices = modified;
}

fn emit_native_drop_result(
    ctx: &mut ChcCtx<'_, '_>,
    result: Option<InlineReturn>,
    target: usize,
    tctx: &TransitionContext<'_>,
) {
    let Some(result) = result else {
        ctx.record_sound_fallback_reason("native_box_drop_exact_origin_required");
        ctx.emit_goto_rule_shared(tctx.from_app, target, tctx.output_args, tctx.shared_constraints);
        return;
    };
    let observed = result
        .deferred_checks
        .iter()
        .map(|check| check.check.clone())
        .chain(ctx.heap_state.pending_checks.iter().cloned())
        .chain(extract_inline_assert_guard(&result.value))
        .collect::<Vec<_>>();
    ctx.emit_deferred_inline_checks_at(
        tctx.from_app,
        &tctx.shared_constraints[..],
        tctx.bb_idx,
        result.deferred_checks,
    );
    let guard = extract_inline_assert_guard(&result.value);
    for check in
        ctx.heap_state.pending_checks.drain(..).collect::<Vec<_>>().into_iter().chain(guard.clone())
    {
        ctx.emit_error_rule_for_condition_shared(
            tctx.from_app,
            check,
            tctx.shared_constraints,
            tctx.bb_idx,
        );
    }
    let mut effects = std::mem::take(&mut ctx.heap_state.pending_updates);
    effects.extend(ctx.heap_state.drain_store_chains(&ctx.diagnostics));
    effects.extend(guard);
    let Some(shared) =
        compose_host_drop_constraints(ctx, &tctx.shared_constraints[..], &effects, &observed)
    else {
        ctx.emit_goto_rule_shared(tctx.from_app, target, tctx.output_args, tctx.shared_constraints);
        return;
    };
    let shared = std::sync::Arc::from(shared);
    let outputs = ctx.build_block_output_args(tctx.modified_locals, None);
    ctx.emit_goto_rule_shared_extra(tctx.from_app, target, &outputs, &shared, effects);
}
