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
/// Only handles single-constructor ADTs where every field has a scalar type key.
pub(in crate::codegen_ay::chc) fn try_reconstruct_adt_from_scalar_loads(
    ctx: &mut ChcCtx<'_, '_>,
    base_addr: &Expr,
    adt_ty: rustc_public::ty::Ty,
) -> Option<Expr> {
    let adt_ty = ctx.resolve_body_ty(adt_ty);
    let sort = ChcCtx::translate_ty(adt_ty)?;
    let dt = sort.datatype_sort()?;
    if dt.constructors.len() != 1 {
        return None;
    }
    let cons = &dt.constructors[0];
    if cons.fields.is_empty() {
        return None;
    }

    // Get field types and offsets from rustc
    let (field_tys, offsets) = match adt_ty.kind() {
        TyKind::RigidTy(RigidTy::Adt(def, args)) => {
            let variants = def.variants();
            if variants.is_empty() {
                return None;
            }
            let tys: Vec<_> = variants[0]
                .fields()
                .iter()
                .map(|f| ctx.resolve_body_ty(f.ty_with_args(&args)))
                .collect();
            let layout = adt_ty.layout().ok()?;
            let offsets = match layout.shape().fields {
                rustc_public::abi::FieldsShape::Arbitrary { offsets } => offsets,
                _ => return None,
            };
            (tys, offsets)
        }
        _ => return None,
    };

    if field_tys.len() != cons.fields.len() {
        return None;
    }

    // Check all fields have scalar type keys — bail if any is non-scalar
    let all_scalar = field_tys.iter().all(|ty| scalar_type_key(*ty).is_some());
    if !all_scalar {
        return None;
    }

    // Load each scalar field from memory
    let mut field_exprs = Vec::with_capacity(cons.fields.len());
    for (i, field_ty) in field_tys.iter().enumerate() {
        let byte_offset = offsets.get(i)?.bytes() as u64;
        let field_addr = if byte_offset > 0 {
            base_addr.clone().bvadd(Expr::bitvec_const(byte_offset as i64, POINTER_WIDTH))
        } else {
            base_addr.clone()
        };

        let type_key = scalar_type_key(*field_ty)?;
        let elem_sort = ctx.elem_sort_for_memory_array(*field_ty);
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

    debug!(
        dt_name = %dt.name,
        field_count = field_exprs.len(),
        "inline_field_map: reconstructed ADT from per-scalar loads (#1739)"
    );

    Some(Expr::datatype_constructor(&dt.name, &cons.name, field_exprs, sort.clone()))
}
