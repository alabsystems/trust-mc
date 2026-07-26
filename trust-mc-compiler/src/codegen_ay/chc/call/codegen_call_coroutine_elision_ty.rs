// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use rustc_public::CrateDef;
use rustc_public::ty::{RigidTy, TyKind};

use super::ChcCtx;
use crate::codegen_ay::chc::rules::codegen_rules::transition_drop::{
    coroutine_drop_fields_trivially_no_drop, pin_box_coroutine_inner_ty,
};
use crate::codegen_ay::chc::rules::codegen_rules_helpers::CodegenRulesHelpers;

pub(super) fn box_coroutine_inner_ty(
    ctx: &ChcCtx<'_, '_>,
    ty: rustc_public::ty::Ty,
) -> Option<rustc_public::ty::Ty> {
    use rustc_public::ty::GenericArgKind;

    if !ChcCtx::is_box_ty(ty) {
        return None;
    }

    let TyKind::RigidTy(RigidTy::Adt(_, args)) = ty.kind() else {
        return None;
    };
    let inner_ty = match args.0.first()? {
        GenericArgKind::Type(ty) => ctx.resolve_body_ty(*ty),
        _ => return None,
    };

    is_coroutine_ty(inner_ty).then_some(inner_ty)
}

pub(super) fn is_box_pin_path(path: &str) -> bool {
    path.contains("boxed::Box") && (path.ends_with(">::pin") || path.ends_with("::pin"))
}

pub(super) fn is_box_into_pin_path(path: &str) -> bool {
    path.contains("boxed::Box") && (path.ends_with(">::into_pin") || path.ends_with("::into_pin"))
}

pub(super) fn is_dealloc_like_path(path: &str) -> bool {
    path.contains("dealloc") || path.contains("__rust_dealloc")
}

pub(super) fn is_coroutine_ty(ty: rustc_public::ty::Ty) -> bool {
    matches!(ty.kind(), TyKind::RigidTy(RigidTy::Coroutine(..)))
}

pub(super) fn ref_or_raw_ptr_pointee_ty(
    ctx: &ChcCtx<'_, '_>,
    ty: rustc_public::ty::Ty,
) -> Option<rustc_public::ty::Ty> {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Ref(_, pointee, _))
        | TyKind::RigidTy(RigidTy::RawPtr(pointee, _)) => Some(ctx.resolve_body_ty(pointee)),
        _ => None,
    }
}

pub(super) fn drop_ref_pointee_elidable(ctx: &ChcCtx<'_, '_>, ty: rustc_public::ty::Ty) -> bool {
    if let Some(coroutine_ty) = pin_box_coroutine_inner_ty(ty) {
        return coroutine_drop_fields_trivially_no_drop(ctx, coroutine_ty);
    }
    if let Some(coroutine_ty) = box_coroutine_inner_ty(ctx, ty) {
        return coroutine_drop_fields_trivially_no_drop(ctx, coroutine_ty);
    }
    is_coroutine_ty(ty) && coroutine_drop_fields_trivially_no_drop(ctx, ty)
}

pub(super) fn drop_derived_local_ty_elidable(
    ctx: &ChcCtx<'_, '_>,
    ty: rustc_public::ty::Ty,
) -> bool {
    if let Some(pointee_ty) = ref_or_raw_ptr_pointee_ty(ctx, ty) {
        return drop_ref_pointee_elidable(ctx, pointee_ty)
            || drop_derived_owned_ty_elidable(ctx, pointee_ty);
    }
    drop_derived_owned_ty_elidable(ctx, ty)
}

fn drop_derived_owned_ty_elidable(ctx: &ChcCtx<'_, '_>, ty: rustc_public::ty::Ty) -> bool {
    use rustc_public::ty::GenericArgKind;

    if matches!(ty.kind(), TyKind::RigidTy(RigidTy::Uint(_))) {
        return true;
    }

    let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() else {
        return false;
    };
    let name = def.trimmed_name();
    if name == "Global" || name == "Layout" {
        return true;
    }
    if name != "Unique" && name != "NonNull" {
        return false;
    }
    let Some(GenericArgKind::Type(inner_ty)) = args.0.first() else {
        return false;
    };
    let inner_ty = ctx.resolve_body_ty(*inner_ty);
    drop_ref_pointee_elidable(ctx, inner_ty) || drop_derived_owned_ty_elidable(ctx, inner_ty)
}
