// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Shared transmute layout-compatibility check for CHC and BMC backends.
//!
//! Part of #3809: extracted from the CHC-only implementation in
//! `codegen_stmt_rvalue_ref.rs` so that both backends use the same contract
//! for layout-sensitive cross-ADT transmutes.

use rustc_public::CrateDef;
use rustc_public::ty::{AdtDef, AdtKind, GenericArgs, RigidTy, Ty, TyKind};

/// Returns `true` if a `CastKind::Transmute` between two types requires a
/// layout-aware fallback (i.e., structural field-by-field coercion is unsound).
///
/// A transmute requires layout fallback when:
/// 1. Both source and target are multi-field ADT structs
/// 2. They have different `DefId`s (different struct definitions)
/// 3. Their rustc layouts do NOT match (field offsets or field types differ)
///
/// When this returns `true`, the caller must NOT use structural DT→DT coercion.
pub(in crate::codegen_ay) fn transmute_requires_layout_fallback(
    src_ty: Ty,
    target_ty: Ty,
    src_sort: &ay_bindings::Sort,
    target_sort: &ay_bindings::Sort,
    resolve_ty: impl Fn(Ty) -> Ty,
) -> bool {
    let (Some(src_dt), Some(target_dt)) = (src_sort.datatype_sort(), target_sort.datatype_sort())
    else {
        return false;
    };
    let src_multi_field = src_dt.constructors.first().is_some_and(|ctor| ctor.fields.len() > 1);
    let target_multi_field =
        target_dt.constructors.first().is_some_and(|ctor| ctor.fields.len() > 1);
    if !src_multi_field || !target_multi_field {
        return false;
    }

    match (src_ty.kind(), target_ty.kind()) {
        (
            TyKind::RigidTy(RigidTy::Adt(src_def, ref src_args)),
            TyKind::RigidTy(RigidTy::Adt(target_def, ref target_args)),
        ) if src_def.kind() == AdtKind::Struct && target_def.kind() == AdtKind::Struct => {
            if src_def.def_id() == target_def.def_id() {
                return false;
            }
            !cross_adt_transmute_layout_matches(
                src_ty,
                src_def,
                src_args,
                target_ty,
                target_def,
                target_args,
                &resolve_ty,
            )
        }
        _ => false,
    }
}

/// Checks whether two cross-ADT struct types have identical rustc layouts
/// (same total size, same field offsets, same resolved field types).
fn cross_adt_transmute_layout_matches(
    src_ty: Ty,
    src_def: AdtDef,
    src_args: &GenericArgs,
    target_ty: Ty,
    target_def: AdtDef,
    target_args: &GenericArgs,
    resolve_ty: &impl Fn(Ty) -> Ty,
) -> bool {
    let src_variants = src_def.variants();
    let Some(src_variant) = src_variants.first() else {
        return false;
    };
    let target_variants = target_def.variants();
    let Some(target_variant) = target_variants.first() else {
        return false;
    };
    let src_fields = src_variant.fields();
    let target_fields = target_variant.fields();
    if src_fields.len() <= 1 || target_fields.len() <= 1 || src_fields.len() != target_fields.len()
    {
        return false;
    }

    let (Ok(src_layout), Ok(target_layout)) = (src_ty.layout(), target_ty.layout()) else {
        return false;
    };
    let src_shape = src_layout.shape();
    let target_shape = target_layout.shape();
    if src_shape.size.bytes() != target_shape.size.bytes() {
        return false;
    }
    let (
        rustc_public::abi::FieldsShape::Arbitrary { offsets: src_offsets },
        rustc_public::abi::FieldsShape::Arbitrary { offsets: target_offsets },
    ) = (&src_shape.fields, &target_shape.fields)
    else {
        return false;
    };
    if src_offsets.len() != src_fields.len() || target_offsets.len() != target_fields.len() {
        return false;
    }

    src_fields.iter().zip(target_fields.iter()).enumerate().all(
        |(field_idx, (src_field, target_field))| {
            let src_field_ty = resolve_ty(src_field.ty_with_args(src_args));
            let target_field_ty = resolve_ty(target_field.ty_with_args(target_args));
            src_offsets.get(field_idx).map(|off| off.bytes())
                == target_offsets.get(field_idx).map(|off| off.bytes())
                && src_field_ty == target_field_ty
        },
    )
}
