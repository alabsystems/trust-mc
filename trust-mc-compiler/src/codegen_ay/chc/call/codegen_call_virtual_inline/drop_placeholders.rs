// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! No-op inline placeholders for cleanup-only nested calls.
//! Dyn drop dispatch helpers split to drop_placeholder_dispatch.rs per #4206.

use super::super::ChcCtx;
use super::super::codegen_types::CodegenTypes;
use super::super::inline_shared::{PlaceResolver, inline_operand_to_expr};
use super::InlineReturn;
use super::drop_placeholder_dispatch::{
    forwarded_heap_vtable_for_expr, resolve_nested_drop_arg_value,
    try_inline_dyn_drop_dispatch_call,
};
use super::pointer_wrapper::{
    resolve_inline_ref_local_target_place, resolve_nested_ref_arg_referent,
};
use crate::codegen_ay::chc::rules::codegen_rules::transition_drop::{
    collect_box_dyn_dealloc_effects, collect_shared_pointer_dealloc_effects,
    shared_pointer_inner_ty, shared_pointer_value_ptr_for_drop,
    shared_pointer_value_ptr_from_obj_id, try_translate_shared_pointer_inner_drop,
};
use crate::codegen_ay::chc::rules::codegen_rules_helpers::rust_dealloc_base_ptr_for_known_alloc_id;
use crate::codegen_ay::provenance::{Loc, Val};
use crate::codegen_ay::types::POINTER_WIDTH;
use ay_bindings::Expr;
use rustc_public::mir::Operand;
use rustc_public::ty::{GenericArgKind, RigidTy, TyKind};
use std::collections::HashMap;

pub(super) fn unprojected_inline_drop_arg_base_local(
    outer_body: &rustc_public::mir::Body,
    arg: &Operand,
) -> Option<usize> {
    let (Operand::Copy(place) | Operand::Move(place)) = arg else {
        return None;
    };
    if !place.projection.is_empty() {
        return None;
    }
    match resolve_inline_ref_local_target_place(outer_body, place.local, 8) {
        Some(target) if target.projection.is_empty() => Some(target.local),
        Some(_) => None,
        None => Some(place.local),
    }
}

pub(super) fn try_inline_shared_pointer_drop_call<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    callee_path: &str,
    args: &[Operand],
    outer_body: &rustc_public::mir::Body,
    local_exprs: &HashMap<usize, Expr>,
    resolver: &PlaceResolver<'_>,
    inline_alloc_ids: &HashMap<usize, u32>,
    inline_depth: usize,
) -> Option<InlineReturn> {
    if !callee_path.contains("Drop>::drop") && !callee_path.contains("drop_in_place") {
        return None;
    }

    let pointee_ty = args.first().and_then(|arg| {
        let arg_ty = ctx.resolve_body_ty(arg.ty(outer_body.locals()).ok()?);
        match arg_ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(_, pointee, _))
            | TyKind::RigidTy(RigidTy::RawPtr(pointee, _)) => Some(ctx.resolve_body_ty(pointee)),
            _ => None,
        }
    })?;
    let inner_ty = shared_pointer_inner_ty(pointee_ty)?;

    let wrapper_expr = args.first().and_then(|arg| {
        let ref_result =
            resolve_nested_ref_arg_referent(ctx, arg, outer_body, local_exprs, resolver);
        ref_result.or_else(|| {
            inline_operand_to_expr(ctx, arg, local_exprs, resolver, outer_body.locals())
        })
    });
    let wrapper_local_idx =
        args.first().and_then(|arg| unprojected_inline_drop_arg_base_local(outer_body, arg));
    let Some(wrapper_expr) = wrapper_expr else {
        // Part of #4193: Do NOT silently swallow Rc/Arc drop as a zero-valued
        // no-op when the wrapper expression is unresolvable. Return None to let
        // the outer encoding handle it (consistent with the guard in
        // inline_trivial_drop_placeholder that also refuses to no-op Rc/Arc).
        return None;
    };
    let known_alloc_id = wrapper_local_idx.and_then(|idx| inline_alloc_ids.get(&idx).copied());
    let dealloc_wrapper_expr = known_alloc_id
        .map(rust_dealloc_base_ptr_for_known_alloc_id)
        .unwrap_or_else(|| wrapper_expr.clone());

    if let Some(inline_result) = try_translate_shared_pointer_inner_drop(
        ctx,
        inner_ty,
        None,
        known_alloc_id,
        &wrapper_expr,
        0,
        inline_depth + 1,
    ) {
        if let Some(dealloc_effects) =
            collect_shared_pointer_dealloc_effects(ctx, &dealloc_wrapper_expr, known_alloc_id)
        {
            ctx.heap_state.pending_checks.extend(dealloc_effects.pending_checks);
            ctx.heap_state.pending_updates.extend(dealloc_effects.pending_updates);
        }
        return Some(inline_result);
    }

    // Retry concrete dyn-tail Rc/Arc inner types when the unsized shim fails.
    if let Some(concrete_inner_ty) =
        find_concrete_rc_inner_ty_for_inline(ctx, inner_ty, wrapper_local_idx)
    {
        if let Some(inline_result) = try_translate_shared_pointer_inner_drop(
            ctx,
            concrete_inner_ty,
            None,
            known_alloc_id,
            &wrapper_expr,
            0,
            inline_depth + 1,
        ) {
            if let Some(dealloc_effects) =
                collect_shared_pointer_dealloc_effects(ctx, &dealloc_wrapper_expr, known_alloc_id)
            {
                ctx.heap_state.pending_checks.extend(dealloc_effects.pending_checks);
                ctx.heap_state.pending_updates.extend(dealloc_effects.pending_updates);
            }
            return Some(inline_result);
        }
    }

    // Part of #4193 Surface 3: Dyn drop dispatch fallback for Rc/Arc<dyn Trait>.
    // When both the original and concrete inner type retries fail, attempt dyn
    // dispatch inlining — enumerate trait candidates and build an ITE chain,
    // mirroring the arc_drop.rs (Surface 1) dyn dispatch path.
    if crate::codegen_ay::chc::dyn_coercion::find_dyn_trait_tail_ty(ctx, inner_ty).is_some() {
        if let Some(value_ptr) = known_alloc_id
            .and_then(|obj_id| shared_pointer_value_ptr_from_obj_id(ctx, obj_id, inner_ty))
            .or_else(|| shared_pointer_value_ptr_for_drop(ctx, None, inner_ty, &wrapper_expr))
        {
            if let Some(dealloc_effects) =
                collect_shared_pointer_dealloc_effects(ctx, &dealloc_wrapper_expr, known_alloc_id)
            {
                ctx.heap_state.pending_checks.extend(dealloc_effects.pending_checks);
                ctx.heap_state.pending_updates.extend(dealloc_effects.pending_updates);
            }
            let vtable_disc = ctx.extract_embedded_vtable_expr(&wrapper_expr).map(Val::into_expr);
            if let Some(dispatch_result) = try_inline_dyn_drop_dispatch_call(
                ctx,
                inner_ty,
                value_ptr,
                vtable_disc,
                outer_body,
                local_exprs,
                &HashMap::new(),
                wrapper_local_idx,
                inline_depth,
            ) {
                return Some(dispatch_result);
            }
        }
    }

    // Dealloc-only fallback (sound over-approximation: skip inner drop).
    if let Some(dealloc_effects) =
        collect_shared_pointer_dealloc_effects(ctx, &dealloc_wrapper_expr, known_alloc_id)
    {
        ctx.heap_state.pending_checks.extend(dealloc_effects.pending_checks);
        ctx.heap_state.pending_updates.extend(dealloc_effects.pending_updates);
    }
    Some(InlineReturn::value_only(Expr::bitvec_const(0u64, POINTER_WIDTH)))
}

pub(super) fn try_inline_dyn_drop_call<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    callee_path: &str,
    args: &[Operand],
    outer_body: &rustc_public::mir::Body,
    local_exprs: &HashMap<usize, Expr>,
    resolver: &PlaceResolver<'_>,
    inline_vtable_ids: &HashMap<usize, Expr>,
    inline_alloc_ids: &HashMap<usize, u32>,
    inline_depth: usize,
) -> Option<InlineReturn> {
    if !callee_path.contains("Drop>::drop") && !callee_path.contains("drop_in_place") {
        return None;
    }

    let pointee_ty = args.first().and_then(|arg| {
        let arg_ty = ctx.resolve_body_ty(arg.ty(outer_body.locals()).ok()?);
        match arg_ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(_, pointee, _))
            | TyKind::RigidTy(RigidTy::RawPtr(pointee, _)) => Some(ctx.resolve_body_ty(pointee)),
            _ => None,
        }
    })?;

    let arg_base_local =
        args.first().and_then(|arg| unprojected_inline_drop_arg_base_local(outer_body, arg));

    if matches!(pointee_ty.kind(), TyKind::RigidTy(RigidTy::Dynamic(..))) {
        let dyn_arg =
            inline_operand_to_expr(ctx, args.first()?, local_exprs, resolver, outer_body.locals())?;
        // The inline callee's `self` PARAMETER is an untyped `Expr` slot, and
        // the fallback lane hands back the untranslated arg, so the wave-11 tag
        // ends at this crossing.
        let self_expr = crate::codegen_ay::chc::dyn_coercion::extract_pointer_expr(&dyn_arg)
            .map(Loc::into_expr)
            .unwrap_or(dyn_arg.clone());
        let inline_vtable =
            arg_base_local.and_then(|local_idx| inline_vtable_ids.get(&local_idx).cloned());
        let known_vtable =
            arg_base_local.and_then(|local_idx| ctx.known_vtable_expr_for_local(local_idx));
        let embedded_vtable = ctx.extract_embedded_vtable_expr(&dyn_arg).map(Val::into_expr);
        let vtable_disc = inline_vtable.or(known_vtable).or(embedded_vtable);
        return try_inline_dyn_drop_dispatch_call(
            ctx,
            pointee_ty,
            self_expr,
            vtable_disc,
            outer_body,
            local_exprs,
            inline_vtable_ids,
            arg_base_local,
            inline_depth,
        );
    }

    let TyKind::RigidTy(RigidTy::Adt(_, args_ty)) = pointee_ty.kind() else {
        return None;
    };
    let inner_dyn_ty = match args_ty.0.first() {
        Some(rustc_public::ty::GenericArgKind::Type(inner))
            if matches!(
                ctx.resolve_body_ty(*inner).kind(),
                TyKind::RigidTy(RigidTy::Dynamic(..))
            ) =>
        {
            ctx.resolve_body_ty(*inner)
        }
        _ => return None,
    };
    let box_expr = resolve_nested_drop_arg_value(
        ctx,
        args.first()?,
        pointee_ty,
        outer_body,
        local_exprs,
        resolver,
    )
    .or_else(|| {
        inline_operand_to_expr(ctx, args.first()?, local_exprs, resolver, outer_body.locals())
    })?;
    let bv_ptr = crate::codegen_ay::chc::dyn_coercion::extract_pointer_expr(&box_expr)?;
    // Two untyped consumers: the inline `self` parameter slot and the
    // deallocation helper (itself still `Expr`-taking). Tag dropped once.
    let bv_ptr = bv_ptr.into_expr();
    let inline_vtable =
        arg_base_local.and_then(|local_idx| inline_vtable_ids.get(&local_idx).cloned());
    let known_vtable =
        arg_base_local.and_then(|local_idx| ctx.known_vtable_expr_for_local(local_idx));
    let embedded_vtable = ctx
        .extract_embedded_vtable_expr(&box_expr)
        .map(Val::into_expr)
        .or_else(|| forwarded_heap_vtable_for_expr(ctx, &box_expr));
    let vtable_disc = inline_vtable.or(known_vtable).or(embedded_vtable);
    let inline_result = try_inline_dyn_drop_dispatch_call(
        ctx,
        inner_dyn_ty,
        bv_ptr.clone(),
        vtable_disc,
        outer_body,
        local_exprs,
        inline_vtable_ids,
        arg_base_local,
        inline_depth,
    )
    .unwrap_or_else(|| InlineReturn::value_only(Expr::bitvec_const(0u64, POINTER_WIDTH)));

    let known_alloc_id =
        arg_base_local.and_then(|local_idx| inline_alloc_ids.get(&local_idx).copied());
    let dealloc_effects = collect_box_dyn_dealloc_effects(ctx, bv_ptr, known_alloc_id)?;
    ctx.heap_state.pending_checks.extend(dealloc_effects.pending_checks);
    ctx.heap_state.pending_updates.extend(dealloc_effects.pending_updates);
    Some(inline_result)
}

pub(super) fn inline_trivial_drop_placeholder<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    callee_path: &str,
    args: &[Operand],
    outer_body: &rustc_public::mir::Body,
    destination: &rustc_public::mir::Place,
) -> Option<InlineReturn> {
    if !callee_path.contains("Drop>::drop") && !callee_path.contains("drop_in_place") {
        return None;
    }

    let pointee_ty = args.first().and_then(|arg| {
        let arg_ty = ctx.resolve_body_ty(arg.ty(outer_body.locals()).ok()?);
        match arg_ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(_, pointee, _))
            | TyKind::RigidTy(RigidTy::RawPtr(pointee, _)) => Some(ctx.resolve_body_ty(pointee)),
            _ => None,
        }
    })?;
    // Part of #4193: Rc/Arc must NOT be treated as trivial no-op drops.
    // Even though ty_trivially_no_drop returns true for Rc/Arc (dealloc-only
    // allowlist), at the drop-call level they need inner-drop + dealloc
    // handling via try_inline_shared_pointer_drop_call. If that handler
    // returned None (wrapper expr unresolvable), we must NOT silently swallow
    // the drop as a no-op — fall through to let the outer encoding handle it.
    if shared_pointer_inner_ty(pointee_ty).is_some() {
        return None;
    }
    let vec_into_iter_drop = callee_path.contains("vec::IntoIter");
    // Part of #2183: Vec::IntoIter::drop is abstracted at reachability time.
    // Treat it like the existing Vec/RawVec drop lanes instead of synthesizing
    // a nested symbolic RawVec result that later trips CHC heap/error checks.
    let trivially_no_drop =
        crate::codegen_ay::chc::rules::codegen_rules::transition_drop::ty_trivially_no_drop(
            pointee_ty,
        );
    // Part of #4067: dyn types hit recursive self-calls in drop_in_place
    // (vtable dispatch loops back to the same function). In the inline
    // walker this causes recursion unwinding assertions. Skip as no-op
    // (sound: skipping drop only adds behaviors, safe for assertion checking).
    let is_dyn_drop = matches!(pointee_ty.kind(), TyKind::RigidTy(RigidTy::Dynamic(..)));
    if !trivially_no_drop && !vec_into_iter_drop && !is_dyn_drop {
        return None;
    }

    inline_noop_call_placeholder(ctx, outer_body, destination, "__drop_inline")
}

pub(super) fn inline_trivial_hashbrown_drop_elements_placeholder<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    callee_path: &str,
    fn_substs: &rustc_public::ty::GenericArgs,
    outer_body: &rustc_public::mir::Body,
    destination: &rustc_public::mir::Place,
) -> Option<InlineReturn> {
    if !callee_path.contains("hashbrown::raw::RawTableInner::drop_elements") {
        return None;
    }

    let element_ty = fn_substs.0.iter().find_map(|arg| match arg {
        GenericArgKind::Type(ty) => Some(ctx.resolve_body_ty(*ty)),
        _ => None,
    })?;
    if !crate::codegen_ay::chc::rules::codegen_rules::transition_drop::ty_trivially_no_drop(
        element_ty,
    ) {
        return None;
    }

    inline_noop_call_placeholder(ctx, outer_body, destination, "__drop_elements_inline")
}

fn inline_noop_call_placeholder<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    outer_body: &rustc_public::mir::Body,
    destination: &rustc_public::mir::Place,
    fresh_name: &str,
) -> Option<InlineReturn> {
    // Part of #3955: resolve through body-local normalization so opaque
    // async destinations match the state-var sort.
    let dest_ty = ctx
        .resolve_inline_local_ty(outer_body, destination.local)
        .or_else(|| destination.ty(outer_body.locals()).ok().map(|ty| ctx.resolve_body_ty(ty)))?;
    let value = match dest_ty.kind() {
        TyKind::RigidTy(RigidTy::Tuple(tys)) if tys.is_empty() => {
            Expr::bitvec_const(0u64, POINTER_WIDTH)
        }
        _ => {
            let dest_sort = ChcCtx::translate_ty(dest_ty)?;
            ctx.record_aggregate_gap("inline_drop_placeholder_symbolic");
            super::super::declare_pending_var(super::super::chc_fresh_name(fresh_name), dest_sort)
        }
    };
    Some(InlineReturn::value_only(value))
}

/// Find the concrete inner type for an Rc/Arc whose inner type has a dyn tail.
/// Mirrors `find_concrete_rc_inner_ty` in arc_drop.rs and
/// `find_concrete_rc_inner_ty_for_call` in generic_preroutes.rs for the
/// nested inline walker path (Surface 3).
///
/// When dropping `Rc<Wrapper<dyn Trait>>`, the unsized drop shim may fail to
/// inline. This function scans the harness body for other Rc/Arc locals with
/// the same outer ADT but concrete type parameters, or traces Move/Copy chains
/// from the dropped local to find the original concrete Rc source.
///
/// Part of #4193.
fn find_concrete_rc_inner_ty_for_inline(
    ctx: &ChcCtx<'_, '_>,
    dyn_inner_ty: rustc_public::ty::Ty,
    dropped_local: Option<usize>,
) -> Option<rustc_public::ty::Ty> {
    use rustc_public::CrateDef;

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
    // concrete Rc source (reuses the main body locals via ctx.body).
    if let Some(local_idx) = dropped_local {
        if let Some(ty) = trace_rc_local_to_concrete_inline(ctx, local_idx, 8) {
            return Some(ty);
        }
    }

    // Strategy 2: Scan all Rc/Arc locals in the main body for a concrete
    // version of the same ADT.
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
/// Inline-walker variant: scans `ctx.body` (harness body).
/// Part of #4193.
fn trace_rc_local_to_concrete_inline(
    ctx: &ChcCtx<'_, '_>,
    local_idx: usize,
    depth_remaining: usize,
) -> Option<rustc_public::ty::Ty> {
    use rustc_public::CrateDef;
    use rustc_public::mir::{Operand, Rvalue, StatementKind};

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

    // Trace assignment chains through the harness body.
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
                return trace_rc_local_to_concrete_inline(ctx, src.local, depth_remaining - 1);
            }
        }
    }

    None
}
