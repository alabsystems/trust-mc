// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Projection chain update helpers for inline assignment.
//!
//! Extracted from projected_assign.rs for 500-line file-size compliance.
//! Part of #4206.

use ay_bindings::{Expr, Sort};
use rustc_public::CrateDef;
use rustc_public::mir::ProjectionElem;
use rustc_public::ty::{GenericArgKind, RigidTy, TyKind};
use std::collections::HashMap;

use super::super::codegen_types::CodegenTypes;
use crate::rustc_public_bridge::IndexedVal;

use super::super::inline_shared::apply_inline_subslice_write;
use super::super::{ChcCtx, FieldProjection, constant_index_offset};
use crate::codegen_ay::shared::{is_pointer_wrapper_adt, ty_signedness_shallow};
use crate::codegen_ay::types::{POINTER_WIDTH, SignExtension, coerce_bitvec_width_safe};

fn resolve_inline_index_expr(
    local_exprs: &HashMap<usize, Expr>,
    projection: &ProjectionElem,
) -> Option<Expr> {
    let raw = match projection {
        ProjectionElem::Index(index_local) => local_exprs.get(index_local).cloned(),
        ProjectionElem::ConstantIndex { offset, min_length, from_end } => Some(Expr::bitvec_const(
            constant_index_offset(*offset, *min_length, *from_end) as u128,
            POINTER_WIDTH,
        )),
        _ => None,
    }?;
    Some(coerce_bitvec_width_safe(raw, POINTER_WIDTH, SignExtension::ZeroExtend))
}

pub(super) fn update_inline_value_expr(
    ctx: &mut ChcCtx<'_, '_>,
    current: Expr,
    current_ty: rustc_public::ty::Ty,
    projections: &[ProjectionElem],
    pending_cons_idx: Option<usize>,
    rhs: Expr,
    local_exprs: &HashMap<usize, Expr>,
) -> Option<Expr> {
    if projections.is_empty() {
        return Some(rhs);
    }

    #[allow(unreachable_patterns)] // forward compat for new ProjectionElem variants
    match &projections[0] {
        ProjectionElem::Downcast(variant_idx) => update_inline_value_expr(
            ctx,
            current,
            current_ty,
            &projections[1..],
            Some(variant_idx.to_index()),
            rhs,
            local_exprs,
        ),
        ProjectionElem::Field(field_idx, field_ty) => {
            let field_ty = ctx.resolve_body_ty(*field_ty);
            let current = ctx.try_unflatten_bv_to_datatype(current, current_ty);
            let field_proj = FieldProjection {
                field_idx: *field_idx,
                cons_idx: pending_cons_idx,
                field_ty: Some(field_ty),
            };
            let field_value =
                ChcCtx::datatype_field_select(&current, field_proj.field_idx, field_proj.cons_idx)?;
            let updated_field = update_inline_value_expr(
                ctx,
                field_value,
                field_ty,
                &projections[1..],
                None,
                rhs,
                local_exprs,
            )?;
            ChcCtx::apply_projection_update(&current, &[field_proj], updated_field)
        }
        ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. } => {
            let index_expr = resolve_inline_index_expr(local_exprs, &projections[0])?;
            if !current.sort().is_array() {
                return None;
            }
            let elem_ty = inline_array_element_ty(ctx, current_ty)?;
            let current_element = current.clone().select(index_expr.clone());
            let updated_element = update_inline_value_expr(
                ctx,
                current_element,
                elem_ty,
                &projections[1..],
                None,
                rhs,
                local_exprs,
            )?;
            let signed = ty_signedness_shallow(elem_ty).unwrap_or(false);
            let updated_element = ChcCtx::coerce_store_value(
                current.sort(),
                updated_element,
                signed,
                &ctx.diagnostics,
            );
            Some(current.store(index_expr, updated_element))
        }
        ProjectionElem::Deref => {
            // Mid-chain Deref: current value is a pointer/reference. Load the
            // pointee from memory, apply remaining projections as a functional
            // update, then store the result back. The pointer local itself is
            // unchanged -- the write goes to memory.
            let pointee_ty = inline_deref_pointee_ty(ctx, current_ty)?;
            let pointer_addr = crate::codegen_ay::chc::dyn_coercion::extract_pointer_expr(&current)
                .unwrap_or_else(|| current.clone());
            if pointer_addr.sort().bitvec_width() != Some(POINTER_WIDTH) {
                return None;
            }
            let loaded = load_inline_value_from_memory(ctx, pointer_addr.clone(), pointee_ty)?;
            let updated = update_inline_value_expr(
                ctx,
                loaded,
                pointee_ty,
                &projections[1..],
                None,
                rhs,
                local_exprs,
            )?;
            ctx.build_memory_store(pointer_addr.clone(), updated.clone(), pointee_ty);
            mirror_static_state_var_update(ctx, &pointer_addr, &updated);
            // Return original pointer unchanged -- the write went to memory.
            Some(current)
        }
        // Part of #3188: OpaqueCast is a transparent MIR annotation for
        // coroutine/async types. Pass through to remaining projections.
        ProjectionElem::OpaqueCast(_) => update_inline_value_expr(
            ctx,
            current,
            current_ty,
            &projections[1..],
            pending_cons_idx,
            rhs,
            local_exprs,
        ),
        // Part of #3188: Subslice write -- copy elements from rhs into a
        // contiguous range of the current array.
        ProjectionElem::Subslice { from, to, from_end } => {
            if !current.sort().is_array() || !projections[1..].is_empty() {
                return None;
            }
            apply_inline_subslice_write(ctx, current, current_ty, *from, *to, *from_end, rhs)
        }
        _ => None,
    }
}

pub(super) fn load_inline_value_from_memory(
    ctx: &mut ChcCtx<'_, '_>,
    addr: Expr,
    ty: rustc_public::ty::Ty,
) -> Option<Expr> {
    let ty = ctx.resolve_body_ty(ty);
    let loaded = ctx.load_from_memory(addr.clone(), ty)?;
    let expected_sort = ChcCtx::translate_ty(ty)?;
    if *loaded.sort() == expected_sort || !expected_sort.is_datatype() {
        return Some(loaded);
    }
    rebuild_inline_datatype_from_memory(ctx, addr, ty, expected_sort)
}

fn rebuild_inline_datatype_from_memory(
    ctx: &mut ChcCtx<'_, '_>,
    base_addr: Expr,
    ty: rustc_public::ty::Ty,
    sort: Sort,
) -> Option<Expr> {
    let sort_owned = sort.clone();
    let dt = sort_owned.datatype_sort()?;
    let ctor = dt.constructors.first()?;
    let field_tys = inline_aggregate_field_tys(ctx, ty)?;
    if field_tys.len() != ctor.fields.len() {
        return None;
    }

    let mut field_exprs = Vec::with_capacity(field_tys.len());
    for (field_idx, field_ty) in field_tys.iter().enumerate() {
        let field_offset = ctx.get_field_offset(ty, field_idx)?;
        let field_addr = if field_offset > 0 {
            base_addr.clone().bvadd(Expr::bitvec_const(field_offset as i64, POINTER_WIDTH))
        } else {
            base_addr.clone()
        };
        field_exprs.push(load_inline_value_from_memory(ctx, field_addr, *field_ty)?);
    }

    Some(Expr::datatype_constructor(&*dt.name, &*ctor.name, field_exprs, sort))
}

fn inline_aggregate_field_tys(
    ctx: &ChcCtx<'_, '_>,
    ty: rustc_public::ty::Ty,
) -> Option<Vec<rustc_public::ty::Ty>> {
    let ty = ctx.resolve_body_ty(ty);
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Adt(def, args))
            if def.kind() == rustc_public::ty::AdtKind::Struct =>
        {
            let variants = def.variants();
            let variant = variants.first()?;
            Some(
                variant
                    .fields()
                    .iter()
                    .map(|field| ctx.resolve_body_ty(field.ty_with_args(&args)))
                    .collect(),
            )
        }
        TyKind::RigidTy(RigidTy::Tuple(field_tys)) => {
            Some(field_tys.iter().map(|ty| ctx.resolve_body_ty(*ty)).collect())
        }
        _ => None,
    }
}

pub(super) fn inline_deref_pointee_ty(
    ctx: &ChcCtx<'_, '_>,
    ty: rustc_public::ty::Ty,
) -> Option<rustc_public::ty::Ty> {
    match ctx.resolve_body_ty(ty).kind() {
        TyKind::RigidTy(RigidTy::Ref(_, pointee, _))
        | TyKind::RigidTy(RigidTy::RawPtr(pointee, _)) => Some(ctx.resolve_body_ty(pointee)),
        TyKind::RigidTy(RigidTy::Adt(def, args)) if is_pointer_wrapper_adt(&def.trimmed_name()) => {
            args.0.iter().find_map(|arg| match arg {
                GenericArgKind::Type(pointee) => Some(ctx.resolve_body_ty(*pointee)),
                _ => None,
            })
        }
        _ => None,
    }
}

fn inline_array_element_ty(
    ctx: &ChcCtx<'_, '_>,
    ty: rustc_public::ty::Ty,
) -> Option<rustc_public::ty::Ty> {
    match ctx.resolve_body_ty(ty).kind() {
        TyKind::RigidTy(RigidTy::Array(elem_ty, _)) | TyKind::RigidTy(RigidTy::Slice(elem_ty)) => {
            Some(ctx.resolve_body_ty(elem_ty))
        }
        _ => None,
    }
}

pub(super) fn record_inline_heap_vtable_forward(
    ctx: &mut ChcCtx<'_, '_>,
    addr: &Expr,
    rhs_vtable: Option<Expr>,
) {
    let Some(vtable_expr) = rhs_vtable else {
        return;
    };
    if let Some((obj_id, offset)) = ChcCtx::try_extract_constant_addr(addr) {
        let fwd_key = ((obj_id as u64) << 32) | (offset as u64);
        ctx.heap_state.region_vtable_forwards.insert(fwd_key, vtable_expr.clone());
    }
    ctx.heap_state.region_vtable_forward_exprs.insert(format!("{addr}"), vtable_expr);
}

pub(super) fn record_inline_loaded_value_vtable_forward(
    ctx: &mut ChcCtx<'_, '_>,
    addr: &Expr,
    pointee_ty: rustc_public::ty::Ty,
    rhs_vtable: Option<Expr>,
) {
    let Some(vtable_expr) = rhs_vtable else {
        return;
    };
    let Some(loaded) = ctx.load_from_memory(addr.clone(), pointee_ty) else {
        return;
    };
    record_inline_heap_vtable_forward(ctx, &loaded, Some(vtable_expr.clone()));
    if let rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::Adt(def, args)) =
        pointee_ty.kind()
        && let Some(variant) = def.variants().first()
        && variant.fields().len() == 1
    {
        let field_ty = ctx.resolve_body_ty(variant.fields()[0].ty_with_args(&args));
        if let Some(field_loaded) = ctx.load_from_memory(addr.clone(), field_ty) {
            record_inline_heap_vtable_forward(ctx, &field_loaded, Some(vtable_expr.clone()));
        }
    }
    if let Some(ptr_expr) = ctx.extract_pointer_storage_expr(&loaded) {
        record_inline_heap_vtable_forward(ctx, &ptr_expr, Some(vtable_expr));
    }
}

/// If `addr` matches a known static variable's address, emit a pending update
/// constraining that static's output state variable to equal `value`.
///
/// Part of #3793: Bridges the data path mismatch between inline walker
/// memory stores (typed heap arrays) and outer-function static reads
/// (CHC state variables). Without this, drop bodies that write to `static mut`
/// via `*ptr = val` update the heap array but leave the state variable at its
/// initial value, causing Genuine CTREX.
pub(super) fn mirror_static_state_var_update(ctx: &mut ChcCtx<'_, '_>, addr: &Expr, value: &Expr) {
    // Scan static_address_exprs for a matching address.
    // Static addresses are BV64 constants (obj_id ++ offset), so structural
    // equality on Expr is sufficient -- no symbolic comparison needed.
    let addr_str = format!("{addr}");
    for static_addr in ctx.ref_resolution.static_address_exprs.values() {
        let static_str = format!("{static_addr}");
        if static_str != addr_str {
            continue;
        }
        // Found matching static. Find the mutable static state var whose sort
        // matches. Each mutable static has a unique sort in practice (i32 for
        // CELL, etc.), so sort matching is sufficient to identify the target.
        // Part of #3793: avoids adding a new field to RefResolution by scanning
        // existing mutable_static_state_idxs.
        for &vec_idx in &ctx.ref_resolution.mutable_static_state_idxs {
            let Some((out_name, out_sort)) = ctx.state_var_mgr.output_state_vars.get(vec_idx)
            else {
                continue;
            };
            let coerced = coerce_bitvec_width_safe(
                value.clone(),
                out_sort.bitvec_width().unwrap_or(POINTER_WIDTH),
                SignExtension::ZeroExtend,
            );
            if coerced.sort() == out_sort {
                let out_var = Expr::var(&**out_name, out_sort.clone());
                ctx.heap_state.pending_updates.push(out_var.eq(coerced));
                ctx.mark_state_var_modified(vec_idx);
                return;
            }
        }
        return;
    }
}
