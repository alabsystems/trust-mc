// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Canonical zero-sized value helpers for Kani model dispatch.

use crate::codegen_ay::shared::mono_ty;
#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use ay_bindings::{Expr, Sort};
use rustc_public::abi::VariantsShape;
use rustc_public::ty::{AdtKind, RigidTy, TyKind};
use rustc_public_bridge::IndexedVal;

use super::ChcCtx;
use super::codegen_call_kani_model_dst::is_zst_ty;
use super::codegen_types::CodegenTypes;

/// Canonical deterministic expression for a zero-sized type.
///
/// `kani::any()` on a ZST must still assign the destination local. An identity
/// goto leaves the local carrying its uninitialized input value, which is wrong
/// for array-typed ZSTs like `[u8; 0]` and `[(); N]` that later flow through
/// fixed-array equality. This helper reuses the same canonical sentinels used by
/// aggregate/constant lowering:
/// - `()` / empty tuple / never -> `true`
/// - fieldless structs -> `false`
/// - zero-sized arrays -> `const_array(default_elem)`
/// - zero-sized enums (`Option<Infallible>`) -> their one inhabited variant
pub(in crate::codegen_ay::chc) fn canonical_zst_expr(ty: rustc_public::ty::Ty) -> Option<Expr> {
    let sort = ChcCtx::translate_ty(ty)?;
    canonical_zst_expr_for_sort(ty, &sort)
}

pub(in crate::codegen_ay::chc) fn canonical_zst_expr_for_sort(
    ty: rustc_public::ty::Ty,
    sort: &Sort,
) -> Option<Expr> {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Tuple(tys)) if tys.is_empty() => Some(Expr::bool_const(true)),
        TyKind::RigidTy(RigidTy::Never) => Some(Expr::bool_const(true)),
        TyKind::RigidTy(RigidTy::Adt(def, _))
            if def.kind() == AdtKind::Struct
                && def.variants().first().is_some_and(|variant| variant.fields().is_empty()) =>
        {
            Some(Expr::bool_const(false))
        }
        // Part of #4090: ZST structs with non-empty fields (e.g., CharTryFromError(()))
        // are encoded as Datatype sorts. When the sort IS a Datatype, construct the
        // canonical ZST expression by wrapping field defaults in the constructor.
        // Without this, the fallback produces Bool(true) which causes sort mismatches
        // when the value is used in an enum constructor (e.g., Err(CharTryFromError)).
        TyKind::RigidTy(RigidTy::Adt(def, args))
            if def.kind() == AdtKind::Struct && sort.is_datatype() =>
        {
            let dt = sort.datatype_sort()?;
            let cons = dt.constructors.first()?;
            let variants = def.variants();
            let variant = variants.first()?;
            let fields = variant.fields();
            if cons.fields.len() != fields.len() {
                return None;
            }
            let mut field_exprs = Vec::with_capacity(cons.fields.len());
            for (i, field) in fields.iter().enumerate() {
                let field_sort = &cons.fields[i].sort;
                let field_ty = mono_ty::field_ty(field, &args)?;
                let expr = if is_zst_ty(field_ty) {
                    canonical_zst_expr_for_sort(field_ty, field_sort)
                        .or_else(|| ChcCtx::sort_default_expr(field_sort))
                } else {
                    ChcCtx::sort_default_expr(field_sort)
                }?;
                field_exprs.push(expr);
            }
            Some(Expr::datatype_constructor(&dt.name, &cons.name, field_exprs, sort.clone()))
        }
        // A zero-sized ENUM has exactly one inhabited variant, and rustc's
        // layout names it (`VariantsShape::Single`): `Option<Infallible>` is
        // always `None`. Its fields are zero-sized in turn, so the value is fully
        // determined. `?` on an `Option` moves exactly this value out of
        // `ControlFlow::Break` (the `Try::branch` residual); without it the
        // flattened destination fell to `flatten_self_loop_fallback` and demoted
        // `prusti/Fibonacci_sequence` and `FunctionSymbols/issue1243`.
        TyKind::RigidTy(RigidTy::Adt(def, args))
            if def.kind() == AdtKind::Enum && sort.is_datatype() && is_zst_ty(ty) =>
        {
            let VariantsShape::Single { index } = ty.layout().ok()?.shape().variants else {
                return None;
            };
            let dt = sort.datatype_sort()?;
            let variants = def.variants();
            if dt.constructors.len() != variants.len() {
                return None;
            }
            let variant_idx = index.to_index();
            let cons = dt.constructors.get(variant_idx)?;
            let fields = variants.get(variant_idx)?.fields();
            if cons.fields.len() != fields.len() {
                return None;
            }
            let mut field_exprs = Vec::with_capacity(fields.len());
            for (field, field_decl) in fields.iter().zip(cons.fields.iter()) {
                let field_ty = mono_ty::field_ty(field, &args)?;
                if !is_zst_ty(field_ty) {
                    return None;
                }
                let expr = canonical_zst_expr_for_sort(field_ty, &field_decl.sort)?;
                if *expr.sort() != field_decl.sort {
                    return None;
                }
                field_exprs.push(expr);
            }
            Expr::try_datatype_constructor(&*dt.name, &*cons.name, field_exprs, sort.clone()).ok()
        }
        TyKind::RigidTy(RigidTy::Array(elem_ty, _)) => {
            // ZST arrays ([T; 0] or [(); N]) are encoded as Bool by translate_ty.
            // Return canonical Bool value directly instead of trying to decompose
            // as an SMT array.
            if sort.is_bool() {
                return Some(Expr::bool_const(true));
            }
            let arr = sort.array_sort()?;
            let elem_expr = if is_zst_ty(elem_ty) {
                canonical_zst_expr_for_sort(elem_ty, &arr.element_sort)
                    .or_else(|| ChcCtx::sort_default_expr(&arr.element_sort))
            } else {
                ChcCtx::sort_default_expr(&arr.element_sort)
            }?;
            Some(Expr::const_array(arr.index_sort.clone(), elem_expr))
        }
        _ => ChcCtx::sort_default_expr(sort)
            .or_else(|| if sort.is_bool() { Some(Expr::bool_const(true)) } else { None }),
    }
}
