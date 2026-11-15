// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use ay_bindings::Expr;
use tracing::debug;

use crate::codegen_ay::chc::ChcCtx;
use crate::codegen_ay::chc::rules::codegen_rules_helpers::{
    CodegenRulesHelpers, rust_dealloc_base_pointer_guard, rust_dealloc_base_ptr_for_known_alloc_id,
    rust_dealloc_obj_id_expr, rust_dealloc_validity_guard,
    traced_alloc_id_for_unprojected_drop_place,
};
use crate::codegen_ay::provenance::Loc;
use crate::codegen_ay::ptr_repr::PtrRepr;

use super::super::{CodegenRules, TransitionContext};
use super::dyn_dispatch::try_dyn_drop_dispatch;
use super::no_drop::{is_box_with_dyn_inner, ty_trivially_no_drop_with_dyn_candidates};

pub(super) fn try_codegen_box_drop(
    ctx: &mut ChcCtx<'_, '_>,
    place: &rustc_public::mir::Place,
    drop_ty: Option<rustc_public::ty::Ty>,
    target: usize,
    tctx: &TransitionContext<'_>,
) -> bool {
    if !drop_ty.is_some_and(|ty| matches!(ty.kind(),rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::Adt(def,_)) if def.is_box())) {
        return false;
    }
    if crate::codegen_ay::shared::native_box_raw::native_bmc_has_custom_global_allocator(ctx.tcx) {
        ctx.record_sound_fallback_reason("box_drop_custom_global_allocator_unmodeled");
        return false;
    }

    if let Some(ty) = drop_ty {
        use rustc_public::ty::{GenericArgKind, RigidTy, TyKind};
        if let TyKind::RigidTy(RigidTy::Adt(_, args)) = ty.kind()
            && matches!(args.0.first(), Some(GenericArgKind::Type(inner)) if matches!(inner.kind(), TyKind::RigidTy(RigidTy::Dynamic(..))))
        {
            super::native_box::codegen_native_dyn_box_drop(ctx, place, ty, target, tctx);
            return true;
        }
    }

    // Fix #2736: Emit Box dealloc safety checks at ALL track levels.
    // obj_valid/obj_size arrays are now declared unconditionally, and
    // exchange_malloc already emits valid/size constraints at any level.
    // This enables double-free/use-after-free detection at Reg level.
    if drop_ty.is_some_and(is_box_with_dyn_inner) {
        try_codegen_box_dyn_drop(ctx, place, drop_ty, target, tctx);
        return true;
    }

    // This shortcut deallocates only. A real pointee destructor or a user's
    // allocator can change observable state, so leave those to their actual
    // body/refusal path even when a MIR producer bypassed preprocessing.
    if !drop_ty.is_some_and(|ty| {
        crate::codegen_ay::shared::native_box_raw::native_bmc_box_drop_is_modeled(ctx.tcx, ty)
    }) {
        return false;
    }

    let Some(checked) = ctx.checked_host_native_thin_box_drop(place) else {
        ctx.record_sound_fallback_reason("native_box_drop_allocation_origin_unmodeled");
        return false;
    };
    let known_alloc_id = ChcCtx::try_extract_constant_addr(&checked.value).map(|(id, _)| id);
    if ctx.memory_safety_checks {
        for check in checked.checks {
            ctx.emit_error_rule_for_condition_shared(
                tctx.from_app,
                check,
                tctx.shared_constraints,
                tctx.bb_idx,
            );
        }
    }
    if ctx.emit_box_dealloc_transition(
        tctx.bb_idx,
        tctx.from_app,
        target,
        checked.value,
        known_alloc_id,
        tctx.shared_constraints,
        tctx.modified_locals,
    ) {
        debug!(
            bb_idx = tctx.bb_idx,
            local_idx = place.local,
            "CHC: native Drop(Box) with authenticated birth and exact allocator layout"
        );
        return true;
    }

    false
}

pub(in crate::codegen_ay::chc) struct BoxDynDeallocEffects {
    pub bv_ptr: Expr,
    pub pending_checks: Vec<Expr>,
    pub pending_updates: Vec<Expr>,
}

pub(in crate::codegen_ay::chc) fn collect_box_dyn_dealloc_effects(
    ctx: &mut ChcCtx<'_, '_>,
    ptr_expr: Expr,
    known_alloc_id: Option<u32>,
) -> Option<BoxDynDeallocEffects> {
    use super::super::super::codegen_expr_heap::{
        obj_size_in, obj_size_out, obj_valid_in, obj_valid_out,
    };

    let storage = super::super::super::dyn_coercion::extract_pointer_expr(&ptr_expr)
        .map(Loc::into_expr)
        .unwrap_or(ptr_expr);
    // Wave 4: this deallocates. The `width == 2 * POINTER_WIDTH` test it
    // replaces decided which half of a wide pointer names the object being
    // FREED, and it could not tell a real `Box<dyn T>` fat pointer from a thin
    // one widened into the same slot. `PtrRepr::into_data` is total across all
    // three shapes and picks the address half structurally, so the obj_id fed
    // to the double-free / validity obligations below comes from a decode
    // rather than a width coincidence.
    //
    // The no-decode arm used to read `Loc::of_address(storage)` — a tag on the
    // term `PtrRepr` had just declined to recognize as pointer-shaped, naming
    // the object this path FREES. `split_pointer` below would have rejected it
    // anyway on every shape that matters, so refusing here loses no coverage and
    // stops the tag asserting what the decoder denied.
    let bv_ptr = PtrRepr::classify(&storage)?.into_data().into_expr();
    let Some((raw_obj_id_expr, offset_expr)) = ctx.split_pointer(&bv_ptr) else {
        return None;
    };
    let obj_id_expr = rust_dealloc_obj_id_expr(raw_obj_id_expr, known_alloc_id);

    let obj_valid_in = obj_valid_in();
    let obj_valid_out = obj_valid_out();
    let obj_size_in = obj_size_in();
    let obj_size_out = obj_size_out();
    let is_valid = rust_dealloc_validity_guard(&obj_valid_in, &obj_size_in, &obj_id_expr);
    let offset_zero = rust_dealloc_base_pointer_guard(&obj_size_in, &obj_id_expr, offset_expr);

    let mut pending_updates = Vec::new();
    for stack_obj_id in ctx.heap_state.stack_local_obj_ids() {
        let stack_id_expr = Expr::bitvec_const(stack_obj_id as i128, 32);
        pending_updates.push(obj_id_expr.clone().eq(stack_id_expr).not());
    }
    pending_updates
        .push(obj_valid_out.eq(obj_valid_in.store(obj_id_expr, Expr::bool_const(false))));
    pending_updates.push(obj_size_out.eq(obj_size_in));

    Some(BoxDynDeallocEffects {
        bv_ptr,
        pending_checks: vec![is_valid, offset_zero],
        pending_updates,
    })
}

fn emit_box_dyn_dealloc_checks(
    ctx: &mut ChcCtx<'_, '_>,
    dealloc_effects: &BoxDynDeallocEffects,
    tctx: &TransitionContext<'_>,
) {
    for check in &dealloc_effects.pending_checks {
        ctx.emit_error_rule_for_condition_shared(
            tctx.from_app,
            check.clone(),
            tctx.shared_constraints,
            tctx.bb_idx,
        );
    }
}

/// Handle Drop for Box<dyn T> (unsized inner type).
///
/// Attempts vtable-based dyn dispatch for the inner value, then concrete type
/// resolution via MIR Unsize coercion tracing, falling back to dealloc-only.
fn try_codegen_box_dyn_drop(
    ctx: &mut ChcCtx<'_, '_>,
    place: &rustc_public::mir::Place,
    drop_ty: Option<rustc_public::ty::Ty>,
    target: usize,
    tctx: &TransitionContext<'_>,
) {
    let local_idx: usize = place.local;
    let ptr_expr = ctx.translate_place_with_modified(place, tctx.modified_locals).or_else(|| {
        let drop_vec_idx = ctx.try_state_idx_for_local(local_idx)?;
        ctx.state_var_mgr
            .state_vars
            .get(drop_vec_idx)
            .map(|(var_name, var_sort)| Expr::var(&**var_name, var_sort.clone()))
    });
    let known_alloc_id = traced_alloc_id_for_unprojected_drop_place(ctx, place);
    let Some(ptr_expr) =
        ptr_expr.or_else(|| known_alloc_id.map(rust_dealloc_base_ptr_for_known_alloc_id))
    else {
        // Pointer unconstrained: can't identify obj_id, skip deallocation.
        debug!(bb_idx = tctx.bb_idx, "CHC: Drop(Box<dyn>) → skip (unconstrained pointer)");
        // Part of #4075: when the spawn scheduler vtable model is active, Box<dyn Future>
        // drops with unconstrained pointers are a consequence of vtable identity loss
        // through Vec<Option<BoxFuture>> storage. The scheduler guarantees each future
        // is consumed exactly once, so skipping deallocation is a sound over-approximation.
        if ctx.spawn_scheduler_vtable_model.is_some() {
            ctx.record_sound_fallback_reason("box_dyn_spawn_dealloc_skip");
        } else {
            ctx.record_fallback();
        }
        ctx.emit_goto_rule_shared(tctx.from_app, target, tctx.output_args, tctx.shared_constraints);
        return;
    };
    let Some(dealloc_effects) = collect_box_dyn_dealloc_effects(ctx, ptr_expr, known_alloc_id)
    else {
        debug!(bb_idx = tctx.bb_idx, "CHC: Drop(Box<dyn>) → skip (unconstrained pointer)");
        if ctx.spawn_scheduler_vtable_model.is_some() {
            ctx.record_sound_fallback_reason("box_dyn_spawn_dealloc_skip");
        } else {
            ctx.record_fallback();
        }
        ctx.emit_goto_rule_shared(tctx.from_app, target, tctx.output_args, tctx.shared_constraints);
        return;
    };
    emit_box_dyn_dealloc_checks(ctx, &dealloc_effects, tctx);

    // Extract the inner dyn type from Box<dyn T>.
    let box_drop_ty = drop_ty.expect("invariant: drop_ty checked by is_box_with_dyn_inner guard");
    let inner_dyn_ty = extract_box_inner_ty(box_drop_ty);

    // Try vtable-based dyn dispatch with combined deallocation.
    if let Some(dyn_ty) = inner_dyn_ty
        && try_dyn_drop_dispatch(
            ctx,
            place,
            dyn_ty,
            target,
            tctx,
            Some(dealloc_effects.bv_ptr.clone()),
            &dealloc_effects.pending_updates,
        )
    {
        debug!(bb_idx = tctx.bb_idx, "CHC: Drop(Box<dyn>) → inner dyn drop + dealloc");
        return;
    }

    // Inner drop dispatch failed — fall back to dealloc-only.
    emit_box_dyn_dealloc_only_fallback(
        ctx,
        inner_dyn_ty,
        dealloc_effects.pending_updates,
        target,
        tctx,
    );
}

/// Extract the inner type `T` from `Box<T>`.
fn extract_box_inner_ty(box_ty: rustc_public::ty::Ty) -> Option<rustc_public::ty::Ty> {
    use rustc_public::ty::{GenericArgKind, RigidTy, TyKind};
    if let TyKind::RigidTy(RigidTy::Adt(_, args)) = box_ty.kind() {
        args.0.first().and_then(|ga| match ga {
            GenericArgKind::Type(t) => Some(*t),
            _ => None,
        })
    } else {
        None
    }
}

/// Emit dealloc-only fallback when inner drop dispatch fails for Box<dyn T>.
fn emit_box_dyn_dealloc_only_fallback(
    ctx: &mut ChcCtx<'_, '_>,
    inner_dyn_ty: Option<rustc_public::ty::Ty>,
    dealloc_updates: Vec<Expr>,
    target: usize,
    tctx: &TransitionContext<'_>,
) {
    let dealloc_updates =
        super::effects::compose_box_deallocation_updates(ctx, &dealloc_updates).unwrap_or_default();
    for check in ctx.heap_state.pending_checks.drain(..).collect::<Vec<_>>() {
        ctx.emit_error_rule_for_condition_shared(
            tctx.from_app,
            check,
            tctx.shared_constraints,
            tctx.bb_idx,
        );
    }
    let new_output_args = ctx.build_block_output_args(tctx.modified_locals, None);
    ctx.emit_goto_rule_extra(
        tctx.from_app,
        target,
        &new_output_args,
        tctx.shared_constraints,
        dealloc_updates,
    );
    let inner_has_drop =
        inner_dyn_ty.is_none_or(|t| !ty_trivially_no_drop_with_dyn_candidates(ctx, t));
    if inner_has_drop {
        debug!(bb_idx = tctx.bb_idx, "CHC: Drop(Box<dyn>) → dealloc only (inner drop unsupported)");
        ctx.record_sound_fallback_reason("box_dyn_inner_drop");
        crate::codegen_ay::chc::codegen_ctx::record_drop_fallback_reason_for_fn(
            &ctx.fn_name,
            "box_dyn_inner_drop_unsupported",
        );
    } else {
        debug!(
            bb_idx = tctx.bb_idx,
            "CHC: Drop(Box<unsized>) → dealloc only (inner type trivially no-drop)"
        );
    }
}

/// Compiler-only inspection for native Unsize producers. It never supplies
/// runtime allocation/destructor authority (the exact native origin does).
#[cfg(test)]
pub(super) fn find_concrete_source_for_box_dyn_local(
    ctx: &ChcCtx<'_, '_>,
    local: usize,
) -> Option<rustc_public::ty::Ty> {
    use rustc_public::mir::{CastKind, Operand, PointerCoercion, Rvalue, StatementKind};
    let mut seen = std::collections::HashSet::new();
    let mut next = local;
    for _ in 0..32 {
        if !seen.insert(next) {
            return None;
        }
        let mut definitions =
            ctx.body.blocks.iter().flat_map(|block| &block.statements).filter_map(|statement| {
                match &statement.kind {
                    StatementKind::Assign(place, rhs) if place.local == next => Some((place, rhs)),
                    _ => None,
                }
            });
        let (destination, rhs) = definitions.next()?;
        if !destination.projection.is_empty() || definitions.next().is_some() {
            return None;
        }
        match rhs {
            Rvalue::Use(Operand::Copy(source) | Operand::Move(source), ..)
                if source.projection.is_empty() =>
            {
                next = source.local
            }
            Rvalue::Cast(CastKind::PointerCoercion(PointerCoercion::Unsize), source, target) => {
                crate::codegen_ay::shared::native_box_drop::native_global_box_pointee(
                    ctx.tcx, *target,
                )?;
                let ty = source.ty(ctx.body.locals()).ok()?;
                return crate::codegen_ay::shared::native_box_drop::native_global_box_pointee(
                    ctx.tcx, ty,
                );
            }
            _ => return None,
        }
    }
    None
}
