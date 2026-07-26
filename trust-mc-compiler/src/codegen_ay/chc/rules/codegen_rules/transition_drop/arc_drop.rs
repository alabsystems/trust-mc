// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Arc/Rc drop handling for CHC encoding.
//!
//! In single-threaded verification, Arc/Rc always have strong count = 1,
//! so drop always deallocates. The full drop shim contains complex atomic
//! operations and recursive `drop_in_place::<dyn T>` calls through vtable
//! dispatch that cause recursion unwinding assertions. Handle like Box drop:
//! emit deallocation + skip inner drop (sound for assertion checking).
//!
//! Split from `codegen_drop.rs` — Part of #3927.

use ay_bindings::Expr;
use tracing::debug;

use crate::codegen_ay::chc::ChcCtx;
use crate::codegen_ay::chc::call::codegen_call_coerce::CallCoerce;
use crate::codegen_ay::chc::call::inline_body::extract_inline_assert_guard;
use crate::codegen_ay::chc::rules::codegen_rules_helpers::{
    rust_dealloc_base_ptr_for_known_alloc_id, traced_alloc_id_for_unprojected_drop_place,
};

use super::super::{CodegenRules, TransitionContext};
use super::shared_ptr::{
    collect_shared_pointer_dealloc_effects, shared_pointer_inner_ty,
    shared_pointer_value_ptr_for_drop, try_translate_shared_pointer_inner_drop,
};

/// Part of #4067: Handle Arc<T>/Rc<T> drop as simple deallocation.
///
/// In single-threaded verification, Arc/Rc always have strong count = 1,
/// so drop always deallocates. The full drop shim contains complex atomic
/// operations and recursive `drop_in_place::<dyn T>` calls through vtable
/// dispatch that cause recursion unwinding assertions. Handle like Box drop:
/// emit deallocation + skip inner drop (sound for assertion checking).
pub(super) fn try_codegen_arc_drop(
    ctx: &mut ChcCtx<'_, '_>,
    place: &rustc_public::mir::Place,
    drop_ty: Option<rustc_public::ty::Ty>,
    target: usize,
    tctx: &TransitionContext<'_>,
) -> bool {
    let drop_ty = match drop_ty {
        Some(ty) => ty,
        None => return false,
    };
    let Some(inner_ty) = shared_pointer_inner_ty(drop_ty) else {
        return false;
    };

    // Resolve the pointer expression for the Arc/Rc local
    let local_idx: usize = place.local;
    let wrapper_local_idx = place.projection.is_empty().then_some(local_idx);
    let wrapper_expr =
        ctx.translate_place_with_modified(place, tctx.modified_locals).or_else(|| {
            let drop_vec_idx = ctx.try_state_idx_for_local(local_idx)?;
            ctx.state_var_mgr
                .state_vars
                .get(drop_vec_idx)
                .map(|(var_name, var_sort)| Expr::var(&**var_name, var_sort.clone()))
        });

    let known_alloc_id = traced_alloc_id_for_unprojected_drop_place(ctx, place);
    if known_alloc_id.is_some_and(|obj_id| ctx.rc_arc_shared_alloc_ids.contains(&obj_id))
        && super::no_drop::ty_trivially_no_drop(inner_ty)
    {
        debug!(
            bb_idx = tctx.bb_idx,
            ?known_alloc_id,
            "CHC: Drop(Arc/Rc clone alias) → skip dealloc for no-drop pointee"
        );
        ctx.emit_goto_rule_shared(tctx.from_app, target, tctx.output_args, tctx.shared_constraints);
        return true;
    }

    let wrapper_expr =
        wrapper_expr.or_else(|| known_alloc_id.map(rust_dealloc_base_ptr_for_known_alloc_id));
    if let Some(wrapper_expr) = wrapper_expr
        && let Some(dealloc_effects) =
            collect_shared_pointer_dealloc_effects(ctx, &wrapper_expr, known_alloc_id)
    {
        emit_arc_inner_drop_or_dealloc_only(
            ctx,
            inner_ty,
            wrapper_local_idx,
            known_alloc_id,
            &wrapper_expr,
            &dealloc_effects,
            target,
            tctx,
        );
        return true;
    }

    // Can't extract pointer — fall through to skip (sound over-approximation).
    debug!(bb_idx = tctx.bb_idx, "CHC: Drop(Arc/Rc) → skip (pointer unconstrained, #4067)");
    ctx.emit_goto_rule_shared(tctx.from_app, target, tctx.output_args, tctx.shared_constraints);
    true
}

/// Emit either inner-drop + dealloc, or dealloc-only for Arc/Rc.
fn emit_arc_inner_drop_or_dealloc_only(
    ctx: &mut ChcCtx<'_, '_>,
    inner_ty: rustc_public::ty::Ty,
    wrapper_local_idx: Option<usize>,
    known_alloc_id: Option<u32>,
    wrapper_expr: &Expr,
    dealloc_effects: &super::shared_ptr::SharedPointerDeallocEffects,
    target: usize,
    tctx: &TransitionContext<'_>,
) {
    // Try the original unsized inner type first.
    if let Some(inline_result) = try_translate_shared_pointer_inner_drop(
        ctx,
        inner_ty,
        wrapper_local_idx,
        known_alloc_id,
        wrapper_expr,
        tctx.bb_idx,
        0,
    ) {
        emit_arc_inner_drop_success(ctx, inline_result, dealloc_effects, target, tctx);
        return;
    }

    // When the inner type has a dyn tail (e.g., Wrapper<dyn Trait>), the unsized
    // drop shim may fail to inline. Try resolving the concrete inner type from
    // other Rc<ConcreteType> locals in the harness body that share the same ADT.
    if let Some(local_idx) = wrapper_local_idx
        && let Some(concrete_inner_ty) = find_concrete_rc_inner_ty(ctx, inner_ty, local_idx)
    {
        if let Some(inline_result) = try_translate_shared_pointer_inner_drop(
            ctx,
            concrete_inner_ty,
            wrapper_local_idx,
            known_alloc_id,
            wrapper_expr,
            tctx.bb_idx,
            0,
        ) {
            debug!(bb_idx = tctx.bb_idx, "CHC: Drop(Arc/Rc<dyn>) → concrete inner drop + dealloc");
            emit_arc_inner_drop_success(ctx, inline_result, dealloc_effects, target, tctx);
            return;
        }
    }

    // Part of #4193: When inner drop inlining fails and the inner type has a
    // dyn trait tail, try dyn drop dispatch with concrete candidates.
    if let Some(local_idx) = wrapper_local_idx
        && crate::codegen_ay::chc::dyn_coercion::find_dyn_trait_tail_ty(ctx, inner_ty).is_some()
    {
        if let Some(value_ptr) =
            shared_pointer_value_ptr_for_drop(ctx, wrapper_local_idx, inner_ty, wrapper_expr)
        {
            let dealloc_extras: Vec<Expr> = dealloc_effects.pending_updates.clone();
            for check in &dealloc_effects.pending_checks {
                ctx.emit_error_rule_for_condition_shared(
                    tctx.from_app,
                    check.clone(),
                    tctx.shared_constraints,
                    tctx.bb_idx,
                );
            }
            if super::dyn_dispatch::try_dyn_drop_dispatch(
                ctx,
                &rustc_public::mir::Place { local: local_idx, projection: Vec::new() },
                inner_ty,
                target,
                tctx,
                Some(value_ptr),
                &dealloc_extras,
            ) {
                debug!(
                    bb_idx = tctx.bb_idx,
                    "CHC: Drop(Arc/Rc) → dyn inner drop dispatch + dealloc (#4193)"
                );
                return;
            }
        }
    }

    // Dealloc-only fallback.
    for check in &dealloc_effects.pending_checks {
        ctx.emit_error_rule_for_condition_shared(
            tctx.from_app,
            check.clone(),
            tctx.shared_constraints,
            tctx.bb_idx,
        );
    }
    let new_output_args = ctx.build_output_args(tctx.modified_locals, &[]);
    ctx.emit_goto_rule_extra(
        tctx.from_app,
        target,
        &new_output_args,
        tctx.shared_constraints,
        dealloc_effects.pending_updates.clone(),
    );
    debug!(bb_idx = tctx.bb_idx, "CHC: Drop(Arc/Rc) → dealloc only");
}

/// Shared success path: emit inline guard + dealloc constraints.
fn emit_arc_inner_drop_success(
    ctx: &mut ChcCtx<'_, '_>,
    inline_result: crate::codegen_ay::chc::call::inline_body::InlineReturn,
    dealloc_effects: &super::shared_ptr::SharedPointerDeallocEffects,
    target: usize,
    tctx: &TransitionContext<'_>,
) {
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
    for check in &dealloc_effects.pending_checks {
        ctx.emit_error_rule_for_condition_shared(
            tctx.from_app,
            check.clone(),
            tctx.shared_constraints,
            tctx.bb_idx,
        );
    }
    let mut extra_constraints = Vec::new();
    extra_constraints.append(&mut ctx.heap_state.pending_updates);
    extra_constraints.append(&mut ctx.heap_state.drain_store_chains(&ctx.diagnostics));
    extra_constraints.extend(inline_guard);
    extra_constraints.extend(dealloc_effects.pending_updates.iter().cloned());
    let new_output_args = ctx.build_output_args(tctx.modified_locals, &[]);
    ctx.emit_goto_rule_extra(
        tctx.from_app,
        target,
        &new_output_args,
        tctx.shared_constraints,
        extra_constraints,
    );
    debug!(bb_idx = tctx.bb_idx, "CHC: Drop(Arc/Rc) → inner drop + dealloc");
}

/// Find the concrete inner type for an Rc/Arc local whose inner type has a dyn tail.
///
/// When dropping `Rc<Wrapper<dyn Trait>>`, the unsized drop shim may fail to inline.
/// This function scans the harness body for other Rc/Arc locals with the same outer
/// ADT but concrete type parameters, or traces Move/Copy chains from the dropped
/// local to find the original concrete Rc source.
fn find_concrete_rc_inner_ty(
    ctx: &ChcCtx<'_, '_>,
    dyn_inner_ty: rustc_public::ty::Ty,
    dropped_local: usize,
) -> Option<rustc_public::ty::Ty> {
    use rustc_public::CrateDef;
    use rustc_public::ty::{GenericArgKind, RigidTy, TyKind};

    // Only applicable when the inner type has a dyn tail.
    if crate::codegen_ay::chc::dyn_coercion::find_dyn_trait_tail_ty(ctx, dyn_inner_ty).is_none() {
        return None;
    }

    // Extract the outer ADT name for matching (e.g., "Wrapper").
    let dyn_adt_name = match dyn_inner_ty.kind() {
        TyKind::RigidTy(RigidTy::Adt(def, _)) => Some(def.name()),
        _ => None,
    };

    // Strategy 1: Trace Move/Copy chains from the dropped local back to a
    // concrete Rc source.
    if let Some(ty) = trace_rc_local_to_concrete(ctx, dropped_local, 8) {
        return Some(ty);
    }

    // Strategy 2: Scan all Rc/Arc locals in the body for a concrete version
    // of the same ADT.
    for local in ctx.body.locals() {
        let ty = ctx.resolve_body_ty(local.ty);
        let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() else {
            continue;
        };
        let trimmed = def.trimmed_name();
        if !matches!(trimmed.as_str(), "Rc" | "Arc") {
            continue;
        }
        let Some(GenericArgKind::Type(inner_ty)) = args.0.first() else {
            continue;
        };
        let inner_ty = ctx.resolve_body_ty(*inner_ty);
        // Skip dyn types — we want concrete.
        if crate::codegen_ay::chc::dyn_coercion::find_dyn_trait_tail_ty(ctx, inner_ty).is_some() {
            continue;
        }
        // Check if this inner type matches the same ADT as the dyn one.
        if let Some(ref dyn_name) = dyn_adt_name
            && let TyKind::RigidTy(RigidTy::Adt(concrete_def, _)) = inner_ty.kind()
            && concrete_def.name() == *dyn_name
        {
            return Some(inner_ty);
        }
    }

    None
}

/// Trace Move/Copy assignment chains from a local back to find a concrete Rc source.
fn trace_rc_local_to_concrete(
    ctx: &ChcCtx<'_, '_>,
    local_idx: usize,
    depth_remaining: usize,
) -> Option<rustc_public::ty::Ty> {
    use rustc_public::CrateDef;
    use rustc_public::mir::{Operand, Rvalue, StatementKind};
    use rustc_public::ty::{GenericArgKind, RigidTy, TyKind};

    if depth_remaining == 0 {
        return None;
    }

    // Check the local's type directly.
    let local_ty = ctx.body.locals().get(local_idx).map(|l| ctx.resolve_body_ty(l.ty));
    if let Some(ty) = local_ty {
        if let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() {
            let trimmed = def.trimmed_name();
            if matches!(trimmed.as_str(), "Rc" | "Arc") {
                if let Some(GenericArgKind::Type(inner_ty)) = args.0.first() {
                    let inner_ty = ctx.resolve_body_ty(*inner_ty);
                    if crate::codegen_ay::chc::dyn_coercion::find_dyn_trait_tail_ty(ctx, inner_ty)
                        .is_none()
                    {
                        return Some(inner_ty);
                    }
                }
            }
        }
    }

    // Trace assignment chains.
    for bb in &ctx.body.blocks {
        for stmt in &bb.statements {
            let StatementKind::Assign(place, rhs) = &stmt.kind else {
                continue;
            };
            if place.local != local_idx || !place.projection.is_empty() {
                continue;
            }
            if let Rvalue::Use(Operand::Move(src) | Operand::Copy(src)) = rhs
                && src.projection.is_empty()
                && src.local != local_idx
            {
                return trace_rc_local_to_concrete(ctx, src.local, depth_remaining - 1);
            }
        }
    }

    None
}
