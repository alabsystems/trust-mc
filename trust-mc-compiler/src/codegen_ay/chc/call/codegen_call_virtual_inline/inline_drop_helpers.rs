// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! MIR analysis helpers for inline drop translation.
//! Extracted from inline_drop.rs per #4206.

use ay_bindings::Expr;
use std::collections::HashMap;

use super::super::ChcCtx;
use super::walker::InlineWalkCtx;
use crate::codegen_ay::types::POINTER_WIDTH;

/// Find the concrete Rust type that was coerced to `dyn Trait` for a local.
///
/// Walks MIR backwards through casts and assignments to find the original
/// concrete type before unsizing coercion.
pub(super) fn find_inline_concrete_source_for_dyn_local(
    ctx: &ChcCtx<'_, '_>,
    body: &rustc_public::mir::Body,
    local_idx: usize,
    depth_remaining: usize,
) -> Option<rustc_public::ty::Ty> {
    use rustc_public::mir::{Operand, Rvalue, StatementKind, TerminatorKind};

    if depth_remaining == 0 {
        return None;
    }

    for block in &body.blocks {
        for stmt in &block.statements {
            let StatementKind::Assign(place, rhs) = &stmt.kind else {
                continue;
            };
            if place.local != local_idx || !place.projection.is_empty() {
                continue;
            }

            match rhs {
                Rvalue::Cast(_, Operand::Copy(src) | Operand::Move(src), target_ty) => {
                    let src_ty = ctx.resolve_body_ty(src.ty(body.locals()).ok()?);
                    let target_ty = ctx.resolve_body_ty(*target_ty);
                    let target_inner =
                        crate::codegen_ay::chc::dyn_coercion::peel_pointer_like_wrapper_ty(
                            target_ty,
                        );
                    if crate::codegen_ay::chc::dyn_coercion::find_dyn_trait_tail_ty(
                        ctx,
                        target_inner,
                    )
                    .is_some()
                    {
                        let src_inner =
                            crate::codegen_ay::chc::dyn_coercion::peel_pointer_like_wrapper_ty(
                                src_ty,
                            );
                        let concrete_ty =
                            crate::codegen_ay::chc::dyn_coercion::extract_concrete_tail_for_dyn(
                                src_inner,
                                target_inner,
                            );
                        if concrete_ty == target_inner {
                            if src.projection.is_empty() && src.local != local_idx {
                                if let Some(concrete_ty) = find_inline_concrete_source_for_dyn_local(
                                    ctx,
                                    body,
                                    src.local,
                                    depth_remaining - 1,
                                ) {
                                    return Some(concrete_ty);
                                }
                            }
                            continue;
                        }
                        if crate::codegen_ay::chc::dyn_coercion::find_dyn_trait_tail_ty(
                            ctx,
                            concrete_ty,
                        )
                        .is_some()
                            && src.projection.is_empty()
                            && src.local != local_idx
                        {
                            if let Some(concrete_ty) = find_inline_concrete_source_for_dyn_local(
                                ctx,
                                body,
                                src.local,
                                depth_remaining - 1,
                            ) {
                                return Some(concrete_ty);
                            }
                        }
                        return Some(concrete_ty);
                    }
                }
                Rvalue::Use(Operand::Copy(src) | Operand::Move(src))
                | Rvalue::Ref(_, _, src)
                | Rvalue::AddressOf(_, src)
                | Rvalue::CopyForDeref(src)
                    if src.projection.is_empty() && src.local != local_idx =>
                {
                    if let Some(concrete_ty) = find_inline_concrete_source_for_dyn_local(
                        ctx,
                        body,
                        src.local,
                        depth_remaining - 1,
                    ) {
                        return Some(concrete_ty);
                    }
                }
                _ => {}
            }
        }

        let TerminatorKind::Call { func, args, destination, .. } = &block.terminator.kind else {
            continue;
        };
        if destination.local != local_idx
            || !destination.projection.is_empty()
            || !is_box_new_call(ctx, body, func)
        {
            continue;
        }
        let Some(Operand::Copy(src) | Operand::Move(src)) = args.first() else {
            continue;
        };
        let src_ty = ctx.resolve_body_ty(src.ty(body.locals()).ok()?);
        if src.projection.is_empty() && src.local != local_idx {
            if let Some(concrete_ty) =
                find_inline_concrete_source_for_dyn_local(ctx, body, src.local, depth_remaining - 1)
            {
                return Some(concrete_ty);
            }
        }
        return Some(src_ty);
    }

    None
}

pub(super) fn is_box_new_call(
    ctx: &ChcCtx<'_, '_>,
    body: &rustc_public::mir::Body,
    func: &rustc_public::mir::Operand,
) -> bool {
    use rustc_public::CrateDef;
    use rustc_public::mir::mono::Instance;
    use rustc_public::rustc_internal;
    use rustc_public::ty::{RigidTy, TyKind};

    let Ok(func_ty) = func.ty(body.locals()) else {
        return false;
    };
    let (fn_def, fn_args) = match func_ty.kind() {
        TyKind::RigidTy(RigidTy::FnDef(def, args)) => (def, args),
        _ => return false,
    };
    let def_id =
        Instance::resolve(fn_def, &fn_args).ok().map_or(fn_def.def_id(), |inst| inst.def.def_id());
    let path = ctx.tcx.def_path_str(rustc_internal::internal(ctx.tcx, def_id));
    path.contains("boxed::Box") && path.ends_with("::new")
}

pub(super) fn find_box_new_payload_local(
    ctx: &ChcCtx<'_, '_>,
    body: &rustc_public::mir::Body,
    local_idx: usize,
    depth_remaining: usize,
) -> Option<usize> {
    use rustc_public::mir::{Operand, Rvalue, StatementKind, TerminatorKind};

    if depth_remaining == 0 {
        return None;
    }

    for block in &body.blocks {
        for stmt in &block.statements {
            let StatementKind::Assign(lhs, rhs) = &stmt.kind else {
                continue;
            };
            if lhs.local != local_idx || !lhs.projection.is_empty() {
                continue;
            }
            let next_local = match rhs {
                Rvalue::Use(Operand::Copy(src) | Operand::Move(src))
                | Rvalue::Cast(_, Operand::Copy(src) | Operand::Move(src), _)
                    if src.projection.is_empty() && src.local != local_idx =>
                {
                    src.local
                }
                _ => continue,
            };
            return find_box_new_payload_local(ctx, body, next_local, depth_remaining - 1)
                .or(Some(next_local));
        }

        let TerminatorKind::Call { func, args, destination, .. } = &block.terminator.kind else {
            continue;
        };
        if destination.local != local_idx
            || !destination.projection.is_empty()
            || !is_box_new_call(ctx, body, func)
        {
            continue;
        }
        let Some(Operand::Copy(src) | Operand::Move(src)) = args.first() else {
            continue;
        };
        if src.projection.is_empty() {
            return Some(src.local);
        }
    }

    None
}

pub(super) fn dyn_projection_locals(
    ctx: &ChcCtx<'_, '_>,
    body: &rustc_public::mir::Body,
) -> Vec<usize> {
    use rustc_public::mir::{Operand, ProjectionElem, Rvalue, StatementKind};

    let mut locals = Vec::new();
    for block in &body.blocks {
        for stmt in &block.statements {
            let StatementKind::Assign(lhs, rhs) = &stmt.kind else {
                continue;
            };
            let Rvalue::Cast(_, Operand::Copy(src) | Operand::Move(src), target_ty) = rhs else {
                continue;
            };
            if !lhs.projection.is_empty()
                || src.projection.is_empty()
                || !matches!(src.projection.first(), Some(ProjectionElem::Deref))
            {
                continue;
            }
            if crate::codegen_ay::chc::dyn_coercion::find_dyn_trait_tail_ty(
                ctx,
                ctx.resolve_body_ty(*target_ty),
            )
            .is_some()
            {
                locals.push(lhs.local);
            }
        }
    }
    locals.sort_unstable();
    locals.dedup();
    locals
}

pub(super) fn seed_box_new_payload_vtable_inline(
    ctx: &ChcCtx<'_, '_>,
    walk_body: &rustc_public::mir::Body,
    local_exprs: &HashMap<usize, Expr>,
    inline_vtable_ids: &HashMap<usize, Expr>,
    dropped_local: usize,
    callee_body: &rustc_public::mir::Body,
    caller_vtable_ids: &mut HashMap<usize, Expr>,
) {
    let Some(payload_local) = find_box_new_payload_local(ctx, walk_body, dropped_local, 8) else {
        return;
    };
    let Some(payload_vtable) = inline_vtable_ids
        .get(&payload_local)
        .cloned()
        .or_else(|| ctx.known_vtable_expr_for_local(payload_local))
        .or_else(|| {
            local_exprs.get(&payload_local).and_then(|expr| ctx.extract_embedded_vtable_expr(expr))
        })
    else {
        return;
    };
    for local_idx in dyn_projection_locals(ctx, callee_body) {
        caller_vtable_ids.entry(local_idx).or_insert_with(|| payload_vtable.clone());
    }
}

pub(super) fn forwarded_heap_vtable_for_expr(ctx: &ChcCtx<'_, '_>, expr: &Expr) -> Option<Expr> {
    if let Some((obj_id, offset)) = ChcCtx::try_extract_constant_addr(expr) {
        let fwd_key = ((obj_id as u64) << 32) | (offset as u64);
        if let Some(vtable) = ctx.heap_state.region_vtable_forwards.get(&fwd_key) {
            return Some(vtable.clone());
        }
    }
    ctx.heap_state.region_vtable_forward_exprs.get(&format!("{expr}")).cloned()
}

pub(super) fn forwarded_heap_vtable_for_dyn_local(
    ctx: &ChcCtx<'_, '_>,
    body: &rustc_public::mir::Body,
    local_exprs: &HashMap<usize, Expr>,
    local_idx: usize,
    depth_remaining: usize,
) -> Option<Expr> {
    use rustc_public::mir::{Operand, ProjectionElem, Rvalue, StatementKind};

    if depth_remaining == 0 {
        return None;
    }

    for block in &body.blocks {
        for stmt in &block.statements {
            let StatementKind::Assign(place, rhs) = &stmt.kind else {
                continue;
            };
            if place.local != local_idx || !place.projection.is_empty() {
                continue;
            }

            match rhs {
                Rvalue::Cast(_, Operand::Copy(src) | Operand::Move(src), target_ty) => {
                    let target_ty = ctx.resolve_body_ty(*target_ty);
                    if !src.projection.is_empty()
                        && matches!(src.projection.first(), Some(ProjectionElem::Deref))
                        && crate::codegen_ay::chc::dyn_coercion::find_dyn_trait_tail_ty(
                            ctx, target_ty,
                        )
                        .is_some()
                        && let Some(root_expr) = local_exprs.get(&src.local)
                    {
                        let addr =
                            crate::codegen_ay::chc::dyn_coercion::extract_pointer_expr(root_expr)
                                .unwrap_or_else(|| root_expr.clone());
                        if let Some(vtable) = forwarded_heap_vtable_for_expr(ctx, &addr) {
                            return Some(vtable);
                        }
                    }
                    if src.projection.is_empty() && src.local != local_idx {
                        if let Some(vtable) = forwarded_heap_vtable_for_dyn_local(
                            ctx,
                            body,
                            local_exprs,
                            src.local,
                            depth_remaining - 1,
                        ) {
                            return Some(vtable);
                        }
                    }
                }
                Rvalue::Use(Operand::Copy(src) | Operand::Move(src))
                | Rvalue::Ref(_, _, src)
                | Rvalue::AddressOf(_, src)
                | Rvalue::CopyForDeref(src)
                    if src.projection.is_empty() && src.local != local_idx =>
                {
                    if let Some(vtable) = forwarded_heap_vtable_for_dyn_local(
                        ctx,
                        body,
                        local_exprs,
                        src.local,
                        depth_remaining - 1,
                    ) {
                        return Some(vtable);
                    }
                }
                _ => {}
            }
        }
    }

    None
}

/// Part of #4067: Check if a type is (or wraps) a platform sync type that we model
/// as a transparent scalar (BV32). Such types have no meaningful Drop in our model --
/// their drop glue involves Box deallocation of pthread_mutex_t which is not
/// heap-allocated. Walking the drop body fails at depth 4+ and produces spurious CTREX.
pub(super) fn is_transparent_platform_drop(ty: rustc_public::ty::Ty) -> bool {
    use rustc_public::CrateDef;
    use rustc_public::ty::{RigidTy, TyKind};

    match ty.kind() {
        TyKind::RigidTy(RigidTy::Adt(def, args)) => {
            let full_name = def.0.name();
            // Direct platform sync types
            if full_name.contains("sys::sync::mutex")
                || full_name.contains("sys::pal::unix::sync")
                || full_name.contains("once_box::OnceBox")
                || full_name.contains("sync::poison::Flag")
                || full_name.contains("pthread_mutex_t")
            {
                return true;
            }
            // Transparent wrappers: Pin, Box, Option -- recurse into inner type
            let name = def.trimmed_name();
            if matches!(name.as_str(), "Pin" | "Box" | "Option") {
                if let Some(rustc_public::ty::GenericArgKind::Type(inner)) = args.0.first() {
                    return is_transparent_platform_drop(*inner);
                }
            }
            false
        }
        _ => false,
    }
}

/// Resolve the self parameter (address) for an inline Drop terminator.
///
/// Part of #3848: The drop body expects `&mut Self` (a pointer to the value
/// being dropped). Returns the memory address if derivable from the inline
/// context. Returns `None` if not -- caller uses fresh symbolic BV64.
pub(super) fn resolve_inline_drop_self_expr(
    ctx: &mut ChcCtx<'_, '_>,
    walk_ctx: &InlineWalkCtx<'_>,
    local_exprs: &HashMap<usize, Expr>,
    place: &rustc_public::mir::Place,
) -> Option<Expr> {
    use rustc_public::CrateDef;
    use rustc_public::mir::ProjectionElem;
    use rustc_public::ty::{GenericArgKind, RigidTy, TyKind};

    let proj = place.projection.as_slice();

    // Case 1: Deref-prefixed place (e.g., `(*_1).field`). The local holds
    // a pointer -- the pointee address is the base for the drop target.
    if matches!(proj.first(), Some(ProjectionElem::Deref)) {
        let root = local_exprs.get(&place.local)?;
        let base_addr = crate::codegen_ay::chc::dyn_coercion::extract_pointer_expr(root)
            .unwrap_or_else(|| root.clone());
        if base_addr.sort().bitvec_width() != Some(POINTER_WIDTH) {
            return None;
        }
        let remaining = &proj[1..];
        if remaining.is_empty() {
            return Some(base_addr);
        }
        let local_decl = walk_ctx.locals.get(place.local)?;
        let pointer_ty = ctx.resolve_body_ty(local_decl.ty);
        let mut current_ty = match pointer_ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(_, pointee, _))
            | TyKind::RigidTy(RigidTy::RawPtr(pointee, _)) => ctx.resolve_body_ty(pointee),
            TyKind::RigidTy(RigidTy::Adt(def, args))
                if crate::codegen_ay::shared::is_pointer_wrapper_adt(&def.trimmed_name()) =>
            {
                args.0.iter().find_map(|arg| match arg {
                    GenericArgKind::Type(pointee) => Some(ctx.resolve_body_ty(*pointee)),
                    _ => None,
                })?
            }
            _ => return None,
        };
        let mut addr = base_addr;
        for p in remaining {
            match p {
                ProjectionElem::Field(idx, field_ty) => {
                    let layout_ty = ctx.normalize_unique_dyn_tail_ty(current_ty);
                    let offset = ctx.get_field_offset(layout_ty, *idx)?;
                    if offset > 0 {
                        addr = addr.bvadd(Expr::bitvec_const(offset as i64, POINTER_WIDTH));
                    }
                    current_ty = ctx.resolve_body_ty(*field_ty);
                }
                _ => return None,
            }
        }
        return Some(addr);
    }

    // Case 2: Simple local -- either a BV64 address or a fat-pointer
    // Datatype (Box<dyn T>, &dyn T). For fat pointers, extract the
    // BV64 pointer component. Part of #3872.
    if proj.is_empty() {
        if let Some(val) = local_exprs.get(&place.local) {
            // Coroutine locals already carry a structured state value in CHC.
            // Passing that value through preserves discriminant-driven drop
            // glue instead of forcing the walker onto a fresh synthetic
            // pointer with no field content.
            if crate::codegen_ay::types::is_coroutine_root_sort(val.sort()) {
                return Some(val.clone());
            }
            if val.sort().bitvec_width() == Some(POINTER_WIDTH) {
                return Some(val.clone());
            }
            // Part of #3872: Fat-pointer Datatype -- extract pointer component.
            if let Some(ptr) = crate::codegen_ay::chc::dyn_coercion::extract_pointer_expr(val) {
                if ptr.sort().bitvec_width() == Some(POINTER_WIDTH) {
                    return Some(ptr);
                }
            }
            // Part of #3977: BV128 packed fat pointer (data:64 | vtable:64).
            // Extract lower POINTER_WIDTH bits as the data pointer.
            if let Some(w) = val.sort().bitvec_width() {
                if w == 2 * POINTER_WIDTH {
                    return Some(val.clone().extract(POINTER_WIDTH - 1, 0));
                }
            }
        }
    }

    None
}

/// Part of #4150: Coroutine drop glue is too complex for the inline walker.
pub(super) fn is_coroutine_drop(ty: rustc_public::ty::Ty) -> bool {
    matches!(ty.kind(), rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::Coroutine(..)))
}
