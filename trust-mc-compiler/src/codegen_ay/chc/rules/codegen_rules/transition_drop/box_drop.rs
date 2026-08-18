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
    if !drop_ty.is_some_and(ChcCtx::is_box_ty) {
        return false;
    }

    // Fix #2736: Emit Box dealloc safety checks at ALL track levels.
    // obj_valid/obj_size arrays are now declared unconditionally, and
    // exchange_malloc already emits valid/size constraints at any level.
    // This enables double-free/use-after-free detection at Reg level.
    if drop_ty.is_some_and(is_box_with_dyn_inner) {
        try_codegen_box_dyn_drop(ctx, place, drop_ty, target, tctx);
        return true;
    }

    let local_idx: usize = place.local;
    // Fix #2745: drop places can be assigned earlier in the same block
    // (`_tmp = move _box; drop(_tmp)`). Use the modified-place translation so
    // dealloc checks see the post-statement value, not the unconstrained block input.
    let ptr_expr =
        if place.projection.is_empty() && ctx.flatten.flattened_tuple_locals.contains(&local_idx) {
            // Box<T> locals are flattened. Drop(Box) only needs the pointer slot,
            // so bypass generic bare-read translation to avoid spurious
            // place_translation_drop diagnostics on the deallocation path.
            ctx.flattened_local_field_expr(local_idx, 0, tctx.modified_locals)
        } else {
            ctx.translate_place_with_modified(place, tctx.modified_locals)
        }
        .or_else(|| {
            let drop_vec_idx = ctx.try_state_idx_for_local(local_idx)?;
            ctx.state_var_mgr
                .state_vars
                .get(drop_vec_idx)
                .map(|(var_name, var_sort)| Expr::var(&**var_name, var_sort.clone()))
        });
    let known_alloc_id = traced_alloc_id_for_unprojected_drop_place(ctx, place);
    let ptr_expr =
        ptr_expr.or_else(|| known_alloc_id.map(rust_dealloc_base_ptr_for_known_alloc_id));
    if let Some(ptr_expr) = ptr_expr
        && ctx.emit_box_dealloc_transition(
            tctx.bb_idx,
            tctx.from_app,
            target,
            ptr_expr,
            known_alloc_id,
            tctx.shared_constraints,
            tctx.modified_locals,
        )
    {
        debug!(bb_idx = tctx.bb_idx, local_idx, "CHC: Drop(Box) → dealloc with double-free check");
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
    ctx.mark_heap_metadata_modified();

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

    // Try concrete type resolution via MIR Unsize coercion (#4097 D2).
    if try_concrete_box_dyn_drop(
        ctx,
        place,
        &dealloc_effects.bv_ptr,
        &dealloc_effects.pending_updates,
        target,
        tctx,
    ) {
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

/// Try resolving the concrete type from Unsize coercion and inline its drop.
fn try_concrete_box_dyn_drop(
    ctx: &mut ChcCtx<'_, '_>,
    place: &rustc_public::mir::Place,
    bv_ptr: &Expr,
    dealloc_updates: &[Expr],
    target: usize,
    tctx: &TransitionContext<'_>,
) -> bool {
    use crate::codegen_ay::chc::call::inline_body::extract_inline_assert_guard;

    let Some(concrete_ty) = find_concrete_source_for_box_dyn_local(ctx, place.local) else {
        return false;
    };
    use rustc_public::mir::mono::Instance;
    let drop_instance = Instance::resolve_drop_in_place(concrete_ty);
    if drop_instance.is_empty_shim() {
        return false;
    }
    let Some(body) = drop_instance.body() else {
        return false;
    };
    let params = [bv_ptr.clone()];
    ctx.register_callee_body_statics(&body);
    ctx.mark_inline_field_reads(&body, &params, tctx.bb_idx);
    let caller_vtable_ids = std::collections::HashMap::new();
    let Some(inline_result) = crate::codegen_ay::chc::call::inline_body::translate_inline_body(
        ctx,
        &body,
        &params,
        tctx.bb_idx,
        &caller_vtable_ids,
        Some(drop_instance),
        0,
    ) else {
        return false;
    };
    let inline_guard = extract_inline_assert_guard(&inline_result.value);
    if let Some(guard) = &inline_guard {
        ctx.emit_error_rule_for_condition_shared(
            tctx.from_app,
            guard.clone(),
            tctx.shared_constraints,
            tctx.bb_idx,
        );
    }
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
    extra_constraints.extend_from_slice(dealloc_updates);
    let new_output_args = ctx.build_block_output_args(tctx.modified_locals, None);
    ctx.emit_goto_rule_extra(
        tctx.from_app,
        target,
        &new_output_args,
        tctx.shared_constraints,
        extra_constraints,
    );
    debug!(
        bb_idx = tctx.bb_idx,
        ?concrete_ty,
        "CHC: Drop(Box<dyn auto>) → concrete drop + dealloc (#4097 D2)"
    );
    true
}

/// Emit dealloc-only fallback when inner drop dispatch fails for Box<dyn T>.
fn emit_box_dyn_dealloc_only_fallback(
    ctx: &mut ChcCtx<'_, '_>,
    inner_dyn_ty: Option<rustc_public::ty::Ty>,
    dealloc_updates: Vec<Expr>,
    target: usize,
    tctx: &TransitionContext<'_>,
) {
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

/// Part of #4097 D2: Find the concrete source type for a Box<dyn AutoTrait> local
/// by scanning the MIR body for Unsize coercion assignments.
///
/// For `_N: Box<dyn Send> = Box::new(Concrete{})`, the MIR contains an
/// Unsize cast `_N = move _M as Box<dyn Send>` where `_M: Box<Concrete>`.
/// This function traces the assignment chain to find `Concrete`.
///
/// Also follows Move/Copy chains: if `_dropped = move _N` and `_N` was
/// the Unsize cast target, we follow through.
///
/// For nested dyn chains (`Box<Box<dyn Send>>` unsized to `Box<dyn Send>`),
/// the Unsize source is itself `Box<dyn T>`. In that case, recursively trace
/// the source operand's local to find the original concrete type.
pub(super) fn find_concrete_source_for_box_dyn_local(
    ctx: &crate::codegen_ay::chc::ChcCtx<'_, '_>,
    local_idx: usize,
) -> Option<rustc_public::ty::Ty> {
    find_concrete_source_for_box_dyn_local_depth(ctx, local_idx, 8)
}

fn find_concrete_source_for_box_dyn_local_depth(
    ctx: &crate::codegen_ay::chc::ChcCtx<'_, '_>,
    local_idx: usize,
    depth_remaining: usize,
) -> Option<rustc_public::ty::Ty> {
    use rustc_public::mir::{CastKind, Operand, PointerCoercion, Rvalue, StatementKind};
    use rustc_public::ty::{GenericArgKind, RigidTy, TyKind};

    if depth_remaining == 0 {
        return None;
    }

    // Check for direct Unsize cast to this local.
    for bb in &ctx.body.blocks {
        for stmt in &bb.statements {
            if let StatementKind::Assign(place, rhs) = &stmt.kind
                && place.local == local_idx
            {
                match rhs {
                    Rvalue::Cast(
                        CastKind::PointerCoercion(PointerCoercion::Unsize),
                        operand,
                        _,
                    ) => {
                        let src_ty = operand.ty(ctx.body.locals()).ok()?;
                        // Extract T from Box<T>.
                        if let TyKind::RigidTy(RigidTy::Adt(_, args)) = src_ty.kind() {
                            let inner_ty = args.0.first().and_then(|ga| match ga {
                                GenericArgKind::Type(t) => Some(*t),
                                _ => None,
                            })?;
                            // If the inner type is itself dyn (nested dyn chain),
                            // trace through the source operand to find the original
                            // concrete type.
                            if matches!(inner_ty.kind(), TyKind::RigidTy(RigidTy::Dynamic(..))) {
                                if let Operand::Copy(src) | Operand::Move(src) = operand
                                    && src.projection.is_empty()
                                    && src.local != local_idx
                                {
                                    return find_concrete_source_for_box_dyn_local_depth(
                                        ctx,
                                        src.local,
                                        depth_remaining - 1,
                                    );
                                }
                                return None;
                            }
                            return Some(inner_ty);
                        }
                        return None;
                    }
                    // Follow Move/Copy chains.
                    Rvalue::Use(Operand::Move(src) | Operand::Copy(src))
                        if src.projection.is_empty() =>
                    {
                        let src_local: usize = src.local;
                        if src_local != local_idx {
                            return find_concrete_source_for_box_dyn_local_depth(
                                ctx,
                                src_local,
                                depth_remaining - 1,
                            );
                        }
                    }
                    _ => {}
                }
            }
        }
    }
    None
}
