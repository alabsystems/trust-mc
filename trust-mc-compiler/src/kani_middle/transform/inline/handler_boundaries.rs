// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Handler-boundary predicates for the function inline pass.

use rustc_public::ty::{FloatTy, GenericArgKind, GenericArgs, IntTy, RigidTy, TyKind, UintTy};

pub(super) fn is_handler_backed_slice_contains(fn_name: &str) -> bool {
    if !fn_name.ends_with("::contains") {
        return false;
    }

    (fn_name.contains("slice::") || fn_name.contains("<["))
        && !fn_name.contains("HashMap")
        && !fn_name.contains("BTreeMap")
        && !fn_name.contains("BTreeSet")
        && !fn_name.contains("HashSet")
        && !fn_name.contains("Vec")
        && !fn_name.contains("String")
}

pub(super) fn is_handler_backed_range_contains(fn_name: &str) -> bool {
    if !fn_name.contains("::contains") {
        return false;
    }

    fn_name.contains("RangeBounds")
        || fn_name.contains("RangeInclusive")
        || fn_name.contains("ops::range::Range")
}

/// Check if a function is a slice accessor method with a dedicated CHC stub.
///
/// `slice::first()` has a semantic CHC stub (`SliceFirst`) that produces
/// canonical encodings. If inlined, the body produces representations that
/// diverge from promoted constant encodings (e.g., ZST `&()` address mismatch).
/// Part of #4113.
pub(super) fn is_handler_backed_slice_accessor(fn_name: &str) -> bool {
    if !fn_name.ends_with("::first") {
        return false;
    }
    (fn_name.contains("slice::") || fn_name.contains("<["))
        && !fn_name.contains("HashMap")
        && !fn_name.contains("BTreeMap")
        && !fn_name.contains("BTreeSet")
        && !fn_name.contains("HashSet")
        && !fn_name.contains("Vec")
        && !fn_name.contains("String")
}

pub(super) fn any_model_raw_compatible_array(fn_args: &GenericArgs) -> bool {
    fn_args
        .0
        .iter()
        .find_map(|arg| match arg {
            GenericArgKind::Type(ty) => Some(*ty),
            _ => None,
        })
        .is_some_and(is_raw_compatible_any_array_ty)
}

fn is_raw_compatible_any_array_ty(ty: rustc_public::ty::Ty) -> bool {
    let TyKind::RigidTy(RigidTy::Array(elem_ty, _)) = ty.kind() else {
        return false;
    };
    is_raw_compatible_any_elem_ty(elem_ty)
}

fn is_raw_compatible_any_elem_ty(ty: rustc_public::ty::Ty) -> bool {
    matches!(
        ty.kind(),
        TyKind::RigidTy(RigidTy::Bool)
            | TyKind::RigidTy(RigidTy::Int(
                IntTy::I8 | IntTy::I16 | IntTy::I32 | IntTy::I64 | IntTy::I128 | IntTy::Isize
            ))
            | TyKind::RigidTy(RigidTy::Uint(
                UintTy::U8 | UintTy::U16 | UintTy::U32 | UintTy::U64 | UintTy::U128 | UintTy::Usize
            ))
            | TyKind::RigidTy(RigidTy::Float(
                FloatTy::F16 | FloatTy::F32 | FloatTy::F64 | FloatTy::F128
            ))
    )
}
