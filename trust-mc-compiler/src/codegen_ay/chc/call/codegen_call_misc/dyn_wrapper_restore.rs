// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Custom dyn-wrapper restoration helpers shared by referent resolution.

use ay_bindings::Expr;
use rustc_public::CrateDef;
use rustc_public::ty::{GenericArgKind, RigidTy, TyKind};

use crate::codegen_ay::types::CtorFieldExt;

fn first_type_arg_ty(args: &rustc_public::ty::GenericArgs) -> Option<rustc_public::ty::Ty> {
    args.0.iter().find_map(|arg| match arg {
        GenericArgKind::Type(ty) => Some(*ty),
        _ => None,
    })
}

fn single_field_storage_ty(
    adt_def: rustc_public::ty::AdtDef,
    args: &rustc_public::ty::GenericArgs,
) -> Option<rustc_public::ty::Ty> {
    let variants = adt_def.variants();
    if variants.len() != 1 || variants[0].fields().len() != 1 {
        return None;
    }
    Some(variants[0].fields()[0].ty_with_args(args))
}

fn peel_pointer_like_storage_ty(ty: rustc_public::ty::Ty) -> Option<rustc_public::ty::Ty> {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Ref(_, inner, _)) | TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => {
            Some(inner)
        }
        TyKind::RigidTy(RigidTy::Adt(def, args))
            if crate::codegen_ay::shared::is_pointer_wrapper_adt(&def.trimmed_name()) =>
        {
            first_type_arg_ty(&args)
        }
        _ => None,
    }
}

fn peel_pointer_like_wrapper_ty(ty: rustc_public::ty::Ty) -> rustc_public::ty::Ty {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Ref(_, inner, _)) | TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => {
            inner
        }
        TyKind::RigidTy(RigidTy::Adt(def, args))
            if crate::codegen_ay::shared::is_pointer_wrapper_adt(&def.trimmed_name()) =>
        {
            first_type_arg_ty(&args).unwrap_or(ty)
        }
        TyKind::RigidTy(RigidTy::Adt(def, args)) => {
            single_field_storage_ty(def, &args).and_then(peel_pointer_like_storage_ty).unwrap_or(ty)
        }
        _ => ty,
    }
}

fn try_extract_single_field_without_accessor(container: &Expr) -> Option<Expr> {
    use ay_bindings::ExprValue;

    match container.value() {
        ExprValue::DatatypeConstructor { args, .. } => args.first().cloned(),
        ExprValue::Ite { cond, then_expr, else_expr } => {
            let then_value = try_extract_single_field_without_accessor(then_expr)?;
            let else_value = try_extract_single_field_without_accessor(else_expr)?;
            Some(Expr::ite(cond.clone(), then_value, else_value))
        }
        _ => None,
    }
}

pub(super) fn peel_pointer_like_dyn_wrapper_expr(
    local_ty: rustc_public::ty::Ty,
    expr: &Expr,
) -> Option<Expr> {
    let peeled_ty = peel_pointer_like_wrapper_ty(local_ty);
    if peeled_ty == local_ty {
        return None;
    }

    let dt = expr.sort().datatype_sort()?;
    let constructor = dt.constructors.first()?;
    if constructor.fields.len() != 1 {
        return None;
    }
    let field = constructor.fields.first()?;
    let inner_dt = field.sort.datatype_sort()?;
    let inner_ctor = inner_dt.constructors.first()?;
    if !inner_ctor.has_field("fld_vtable") {
        return None;
    }

    Some(
        try_extract_single_field_without_accessor(expr).unwrap_or_else(|| {
            expr.clone().field_select(&dt.name, &field.name, field.sort.clone())
        }),
    )
}
