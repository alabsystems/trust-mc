// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! ADT reconstruction from per-scalar memory loads.
//!
//! Part of #1739: When `try_decompose_struct_store` decomposes a struct into
//! per-scalar stores, `load_from_memory` reads from the struct's typed array
//! which was never written. This module reconstructs ADT values by loading
//! each scalar field individually and wrapping them in a Datatype constructor.
//!
//! Split from `inline_field_map.rs` to stay under the 500-line limit.

use crate::codegen_ay::shared::mono_ty;
#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use ay_bindings::{Expr, Sort};
use rustc_public::ty::{FloatTy, IntTy, RigidTy, TyKind, UintTy};
use tracing::debug;

use super::ChcCtx;
use super::codegen_types::CodegenTypes;
use crate::codegen_ay::types::POINTER_WIDTH;

/// Get the type key string for a scalar type (for heap memory array lookup).
///
/// Returns the type key matching the convention in `type_key_for_ty` for
/// scalar types. Returns None for non-scalar types.
pub(in crate::codegen_ay::chc) fn scalar_type_key(
    ty: rustc_public::ty::Ty,
) -> Option<&'static str> {
    let key = match ty.kind() {
        TyKind::RigidTy(RigidTy::Bool) => "bool",
        TyKind::RigidTy(RigidTy::Char) => "u32",
        TyKind::RigidTy(RigidTy::Uint(UintTy::U8)) => "u8",
        TyKind::RigidTy(RigidTy::Uint(UintTy::U16)) => "u16",
        TyKind::RigidTy(RigidTy::Uint(UintTy::U32)) => "u32",
        TyKind::RigidTy(RigidTy::Uint(UintTy::U64)) => "u64",
        TyKind::RigidTy(RigidTy::Uint(UintTy::U128)) => "u128",
        TyKind::RigidTy(RigidTy::Uint(UintTy::Usize)) => "u64",
        TyKind::RigidTy(RigidTy::Int(IntTy::I8)) => "i8",
        TyKind::RigidTy(RigidTy::Int(IntTy::I16)) => "i16",
        TyKind::RigidTy(RigidTy::Int(IntTy::I32)) => "i32",
        TyKind::RigidTy(RigidTy::Int(IntTy::I64)) => "i64",
        TyKind::RigidTy(RigidTy::Int(IntTy::I128)) => "i128",
        TyKind::RigidTy(RigidTy::Int(IntTy::Isize)) => "i64",
        TyKind::RigidTy(RigidTy::Float(FloatTy::F16)) => "f16",
        TyKind::RigidTy(RigidTy::Float(FloatTy::F32)) => "f32",
        TyKind::RigidTy(RigidTy::Float(FloatTy::F64)) => "f64",
        TyKind::RigidTy(RigidTy::Float(FloatTy::F128)) => "f128",
        TyKind::RigidTy(RigidTy::Ref(..)) | TyKind::RigidTy(RigidTy::RawPtr(..)) => "ptr",
        _ => return None,
    };
    Some(key)
}

/// Reconstruct an ADT value from per-scalar memory loads.
///
/// Part of #1739: When `try_decompose_struct_store` decomposes a struct into
/// per-scalar stores (e.g., `mem_u128[addr] = field_val`), the inline walker's
/// `load_from_memory` reads from the struct's typed array (e.g., `mem_defs_DummyImpl`)
/// which was never written. This function reconstructs the struct value by loading
/// each scalar field individually and wrapping them in a Datatype constructor.
///
/// Handles single-constructor ADTs and tuples whose every leaf has a scalar type
/// key, nested up to [`MAX_RECONSTRUCT_DEPTH`] levels. A nested struct or tuple
/// field is rebuilt from ITS leaves too, the cells every store of a leaf writes.
/// It used to answer `None` for a tuple, or a struct with an aggregate field,
/// so the field map loaded that field from its own type-indexed array, which a
/// store of one of its leaves never writes: after `d.x.0 = 255` on a
/// `Box<N2 { x: (u8, u8), .. }>`, a walked `self.x.0` read the constructor's
/// byte (review of fix/chc-lost-writes, 2026-09-27: `bug_depth2_tuple_box_dyn`,
/// `bug_depth3_box_dyn` and the depth-4 payload were missed or proved clean).
/// A shape it cannot rebuild completely answers `None` before any load, so the
/// caller's fallback is unchanged.
pub(in crate::codegen_ay::chc) fn try_reconstruct_adt_from_scalar_loads(
    ctx: &mut ChcCtx<'_, '_>,
    base_addr: &Expr,
    adt_ty: rustc_public::ty::Ty,
) -> Option<Expr> {
    let adt_ty = ctx.resolve_body_ty(adt_ty);
    // Decide first, load second: a partial reconstruction must not leave
    // arrays marked read for a value the caller then loads another way.
    reconstructible(ctx, adt_ty, 0)?;
    let value = reconstruct_at(ctx, base_addr, adt_ty, 0)?;
    debug!(ty = ?adt_ty, "inline_field_map: reconstructed aggregate from per-scalar loads (#1739)");
    Some(value)
}

/// Aggregate nesting the reconstruction follows.
const MAX_RECONSTRUCT_DEPTH: usize = 4;

/// The fields of a single-constructor struct or tuple `ty`: each field's type
/// and byte offset. `None` for any other shape.
fn aggregate_fields(
    ctx: &ChcCtx<'_, '_>,
    ty: rustc_public::ty::Ty,
) -> Option<Vec<(rustc_public::ty::Ty, u64)>> {
    let field_tys: Vec<rustc_public::ty::Ty> = match ty.kind() {
        TyKind::RigidTy(RigidTy::Adt(def, args)) => {
            let variants = def.variants();
            let [variant] = variants.as_slice() else { return None };
            variant
                .fields()
                .iter()
                .map(|f| mono_ty::field_ty(f, &args).map(|t| ctx.resolve_body_ty(t)))
                .collect::<Option<Vec<_>>>()?
        }
        TyKind::RigidTy(RigidTy::Tuple(elems)) => {
            elems.iter().map(|elem| ctx.resolve_body_ty(*elem)).collect()
        }
        _ => return None,
    };
    let layout = ty.layout().ok()?;
    let rustc_public::abi::FieldsShape::Arbitrary { offsets } = layout.shape().fields else {
        return None;
    };
    if offsets.len() != field_tys.len() {
        return None;
    }
    Some(field_tys.into_iter().zip(offsets.iter().map(|o| o.bytes() as u64)).collect())
}

/// Whether `ty` can be rebuilt from scalar leaf loads: a single-constructor
/// datatype sort whose fields match the type's fields one to one, each a
/// scalar (with a type key and its own sort) or itself reconstructible.
fn reconstructible(ctx: &ChcCtx<'_, '_>, ty: rustc_public::ty::Ty, depth: usize) -> Option<()> {
    if depth >= MAX_RECONSTRUCT_DEPTH {
        return None;
    }
    let sort = ChcCtx::translate_ty(ty)?;
    let dt = sort.datatype_sort()?;
    let [cons] = dt.constructors.as_slice() else { return None };
    let fields = aggregate_fields(ctx, ty)?;
    if fields.is_empty() || fields.len() != cons.fields.len() {
        return None;
    }
    for ((field_ty, _), ay_field) in fields.iter().zip(cons.fields.iter()) {
        if scalar_type_key(*field_ty).is_some() {
            if ChcCtx::translate_ty(*field_ty).as_ref() != Some(&ay_field.sort) {
                return None;
            }
            continue;
        }
        reconstructible(ctx, *field_ty, depth + 1)?;
        if ChcCtx::translate_ty(*field_ty).as_ref() != Some(&ay_field.sort) {
            return None;
        }
    }
    Some(())
}

fn reconstruct_at(
    ctx: &mut ChcCtx<'_, '_>,
    base_addr: &Expr,
    ty: rustc_public::ty::Ty,
    depth: usize,
) -> Option<Expr> {
    let sort = ChcCtx::translate_ty(ty)?;
    let dt = sort.datatype_sort()?;
    let [cons] = dt.constructors.as_slice() else { return None };
    let fields = aggregate_fields(ctx, ty)?;
    let mut field_exprs = Vec::with_capacity(fields.len());
    for (field_ty, byte_offset) in fields {
        let field_addr = if byte_offset > 0 {
            base_addr.clone().bvadd(Expr::bitvec_const(byte_offset as i64, POINTER_WIDTH))
        } else {
            base_addr.clone()
        };
        let Some(type_key) = scalar_type_key(field_ty) else {
            field_exprs.push(reconstruct_at(ctx, &field_addr, field_ty, depth + 1)?);
            continue;
        };
        let elem_sort = ctx.elem_sort_for_memory_array(field_ty);
        let (arr_name, arr_out_name, declared_elem_sort, is_new) =
            ctx.heap_state.get_or_create_type_array(type_key, elem_sort, &ctx.fn_name);
        if is_new {
            let arr_sort = Sort::array(Sort::bitvec(POINTER_WIDTH), declared_elem_sort.clone());
            ctx.push_late_state_var_pair(std::sync::Arc::clone(&arr_name), &arr_out_name, arr_sort);
        }
        ctx.heap_state.mark_type_array_read(&arr_name, ctx.current_encode_bb);
        let arr_sort = Sort::array(Sort::bitvec(POINTER_WIDTH), declared_elem_sort);
        let arr_expr = if let Some(chain_expr) = ctx.heap_state.get_store_chain(type_key) {
            chain_expr.clone()
        } else {
            Expr::var(&*arr_name, arr_sort)
        };
        field_exprs.push(arr_expr.select(field_addr));
    }
    if field_exprs.iter().zip(cons.fields.iter()).any(|(value, field)| *value.sort() != field.sort)
    {
        return None;
    }
    Some(Expr::datatype_constructor(&dt.name, &cons.name, field_exprs, sort.clone()))
}

/// Whether the inline field map rebuilds a field of type `ty` from its scalar
/// leaves (`try_reconstruct_adt_from_scalar_loads`) instead of loading it from
/// its own type-indexed array.
pub(in crate::codegen_ay::chc) fn field_map_rebuilds_from_leaves(
    ctx: &ChcCtx<'_, '_>,
    ty: rustc_public::ty::Ty,
) -> bool {
    let ty = ctx.resolve_body_ty(ty);
    reconstructible(ctx, ty, 0).is_some()
}
