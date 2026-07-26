// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Projected inline assignment helpers.
//!
//! Handles functional write-back for projected statement assignments and call
//! destinations inside inline virtual bodies.
//! Projection chain update and type helpers split to projected_assign_helpers.rs
//! per #4206.

use ay_bindings::Expr;
use rustc_abi::VariantIdx as InternalVariantIdx;
use rustc_public::mir::{LocalDecl, Operand, Place, ProjectionElem};
use rustc_public::rustc_internal;
use rustc_public::ty::{RigidTy, TyKind};
use std::collections::HashMap;

use super::super::ChcCtx;
use super::super::inline_shared::inline_operand_to_expr;
use super::projected_assign_helpers::{
    inline_deref_pointee_ty, load_inline_value_from_memory, mirror_static_state_var_update,
    record_inline_heap_vtable_forward, record_inline_loaded_value_vtable_forward,
    update_inline_value_expr,
};
use super::walker::InlineWalkCtx;
use crate::codegen_ay::chc::codegen_stmt_aggregate_adt::sign_extend_discr_val;
use crate::codegen_ay::types::POINTER_WIDTH;
use crate::rustc_public_bridge::IndexedVal;

/// Handle Deref-prefixed projected writes as memory stores.
///
/// Part of #3793: When an inline body writes through a dereferenced pointer
/// (e.g., `*ptr = val` or `(*ptr).field = val`), the write must go to memory
/// via `build_memory_store()`, not to `local_exprs`. Without this, side effects
/// of inlined drop bodies (like `CELL = 1`) are silently lost.
///
/// Returns `true` if the assignment was handled as a memory store (constraints
/// emitted via `ctx.build_memory_store`), `false` if this is not a Deref-prefixed
/// write and should fall through to the functional `apply_inline_projected_assign`.
pub(in crate::codegen_ay::chc) fn try_inline_memory_store(
    ctx: &mut ChcCtx<'_, '_>,
    locals: &[LocalDecl],
    local_exprs: &HashMap<usize, Expr>,
    place: &rustc_public::mir::Place,
    rhs: Expr,
    rhs_vtable: Option<Expr>,
) -> bool {
    // Only handle assignments that start with Deref.
    if !matches!(place.projection.first(), Some(ProjectionElem::Deref)) {
        return false;
    }
    let Some(root) = local_exprs.get(&place.local) else {
        return false;
    };
    let Some(local_decl) = locals.get(place.local) else {
        tracing::warn!(place_local = place.local, "try_inline_memory_store: no local_decl");
        return false;
    };
    let pointer_ty = ctx.resolve_body_ty(local_decl.ty);
    let Some(pointee_ty) = inline_deref_pointee_ty(ctx, pointer_ty) else {
        tracing::warn!(place_local = place.local, pointer_ty = ?pointer_ty.kind(), "try_inline_memory_store: no pointee_ty");
        return false;
    };

    // Extract the memory address from the pointer expression.
    let pointer_addr = crate::codegen_ay::chc::dyn_coercion::extract_pointer_expr(root)
        .unwrap_or_else(|| root.clone());
    if pointer_addr.sort().bitvec_width() != Some(POINTER_WIDTH) {
        tracing::warn!(place_local = place.local, addr_sort = ?pointer_addr.sort(), "try_inline_memory_store: addr not POINTER_WIDTH");
        return false;
    }

    let proj = &place.projection[1..];
    if proj.is_empty() {
        // Simple `*ptr = rhs` -- store the RHS directly.
        ctx.build_memory_store(pointer_addr.clone(), rhs.clone(), pointee_ty);
        record_inline_heap_vtable_forward(ctx, &pointer_addr, rhs_vtable.clone());
        record_inline_loaded_value_vtable_forward(ctx, &pointer_addr, pointee_ty, rhs_vtable);
        // Part of #3793: Mirror write to static state variable if this address
        // corresponds to a known static. The memory store updates heap arrays,
        // but the outer function reads statics through state variables.
        mirror_static_state_var_update(ctx, &pointer_addr, &rhs);
        return true;
    }

    // Deref + further projections: load the current value, apply functional
    // update, then store the entire updated value back.
    let Some(current) = load_inline_value_from_memory(ctx, pointer_addr.clone(), pointee_ty) else {
        return false;
    };
    let Some(updated) =
        update_inline_value_expr(ctx, current, pointee_ty, proj, None, rhs, local_exprs)
    else {
        return false;
    };
    ctx.build_memory_store(pointer_addr.clone(), updated.clone(), pointee_ty);
    record_inline_heap_vtable_forward(ctx, &pointer_addr, rhs_vtable.clone());
    record_inline_loaded_value_vtable_forward(ctx, &pointer_addr, pointee_ty, rhs_vtable);
    mirror_static_state_var_update(ctx, &pointer_addr, &updated);
    true
}

pub(in crate::codegen_ay::chc) fn apply_inline_coroutine_set_discriminant<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    walk_ctx: &InlineWalkCtx<'_>,
    local_exprs: &HashMap<usize, Expr>,
    place: &Place,
    ty: rustc_public::ty::Ty,
    variant_index: rustc_public::ty::VariantIdx,
) -> Option<Expr> {
    let current = inline_operand_to_expr(
        ctx,
        &Operand::Copy(place.clone()),
        local_exprs,
        &walk_ctx.resolver,
        walk_ctx.locals,
    )?;
    let discr_width = crate::codegen_ay::types::coroutine_discriminant_select(current.clone())
        .and_then(|expr| expr.sort().bitvec_width())
        .unwrap_or(POINTER_WIDTH);
    let internal_ty = rustc_internal::internal(ctx.tcx, ty);
    let discr = internal_ty.discriminant_for_variant(
        ctx.tcx,
        InternalVariantIdx::from_usize(variant_index.to_index()),
    )?;
    let discr_expr = Expr::bitvec_const(
        sign_extend_discr_val(discr.val, discr.ty, ctx.tcx, discr_width),
        discr_width,
    );
    let updated = crate::codegen_ay::types::coroutine_discriminant_update(&current, discr_expr)?;
    if place.projection.is_empty() {
        return Some(updated);
    }
    apply_inline_projected_assign(ctx, walk_ctx.locals, local_exprs, place, updated)
}

pub(in crate::codegen_ay::chc) fn rebuild_inline_coroutine_receiver<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    walk_ctx: &InlineWalkCtx<'_>,
    local_exprs: &HashMap<usize, Expr>,
    place: &Place,
    ty: rustc_public::ty::Ty,
) -> Option<Expr> {
    if place.local == 1 {
        return None;
    }
    let receiver_decl = walk_ctx.locals.get(1)?;
    let updated = local_exprs.get(&place.local)?.clone();
    match receiver_decl.ty.kind() {
        TyKind::RigidTy(RigidTy::Ref(_, inner, _)) if inner == ty => Some(updated),
        TyKind::RigidTy(RigidTy::Adt(def, args)) => {
            let variants = def.variants();
            let variant = variants.first()?;
            let fields = variant.fields();
            let field = fields.first()?;
            let field_ty = field.ty_with_args(&args);
            let TyKind::RigidTy(RigidTy::Ref(_, inner, _)) = field_ty.kind() else {
                return None;
            };
            if inner != ty {
                return None;
            }
            let receiver_place = Place {
                local: 1,
                projection: vec![ProjectionElem::Field(0, field_ty), ProjectionElem::Deref],
            };
            apply_inline_projected_assign(
                ctx,
                walk_ctx.locals,
                local_exprs,
                &receiver_place,
                updated,
            )
        }
        _ => None,
    }
}

/// Functional update for projected inline writes, including call destinations.
///
/// Part of #3561: covers `(*self).field = rhs`,
/// `(*self).field[idx] = rhs`, and chained field/index write-back.
pub(in crate::codegen_ay::chc) fn apply_inline_projected_assign(
    ctx: &mut ChcCtx<'_, '_>,
    locals: &[LocalDecl],
    local_exprs: &HashMap<usize, Expr>,
    place: &rustc_public::mir::Place,
    rhs: Expr,
) -> Option<Expr> {
    if place.projection.is_empty() {
        return Some(rhs);
    }
    let root = local_exprs.get(&place.local)?;
    let mut current = root.clone();
    let mut current_ty = ctx.resolve_body_ty(locals.get(place.local)?.ty);
    let mut proj = place.projection.as_slice();

    if matches!(proj.first(), Some(ProjectionElem::Deref)) {
        let pointer_addr = crate::codegen_ay::chc::dyn_coercion::extract_pointer_expr(&current)
            .unwrap_or_else(|| current.clone());
        let is_memory_addr = pointer_addr.sort().bitvec_width() == Some(POINTER_WIDTH);
        proj = &proj[1..];
        // Part of #3793: Pure `*ptr = rhs` where ptr is a memory address (BV64)
        // must go through try_inline_memory_store, not the functional path.
        // The functional path updates local_exprs[ptr_local] to rhs, which
        // silently loses the memory write and the static state var mirror.
        // Only handle Deref functionally when there are further projections
        // (e.g., `(*self).field = rhs`) that need load-modify-store.
        if proj.is_empty() && is_memory_addr {
            return None;
        }
        current_ty = inline_deref_pointee_ty(ctx, current_ty)?;
        current = if is_memory_addr {
            load_inline_value_from_memory(ctx, pointer_addr, current_ty)?
        } else {
            current
        };
    }

    update_inline_value_expr(ctx, current, current_ty, proj, None, rhs, local_exprs)
}
