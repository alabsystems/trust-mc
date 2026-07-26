// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Exact nested-inline handling for `Result::copied` / `Result::cloned`.
//!
//! Part of #3979: preserve the `Ok` / `Err` wrapper when the inline walker
//! encounters the stdlib `Result::copied` helper inside other inlined bodies
//! such as `[T; N]::try_from(&[T])`.

use ay_bindings::{Expr, Sort, SortInner};
use rustc_public::mir::{Body, Place};

use super::super::ChcCtx;
use super::super::codegen_types::CodegenTypes;
use super::InlineReturn;
use crate::codegen_ay::chc::stub_codegen::stubs_option_helpers::OptionHelpers;

struct ResultShape {
    dt_name: String,
    ok_ctor_name: String,
    ok_field_name: String,
    ok_field_sort: Sort,
    err_ctor_name: String,
    err_field_name: String,
    err_field_sort: Sort,
}

fn is_result_copied_path(callee_path: &str) -> bool {
    matches!(callee_path.rsplit("::").next(), Some("copied" | "cloned"))
        && (callee_path.contains("core::result")
            || callee_path.contains("std::result")
            || callee_path.contains("Result<"))
}

fn result_shape(result_sort: &Sort) -> Option<ResultShape> {
    let SortInner::Datatype(dt) = result_sort.inner() else {
        return None;
    };
    let ok_ctor = dt.constructors.iter().find(|ctor| {
        ctor.fields.len() == 1 && crate::codegen_ay::names::is_ok_constructor(&ctor.name)
    })?;
    let err_ctor = dt.constructors.iter().find(|ctor| {
        ctor.fields.len() == 1 && crate::codegen_ay::names::is_err_constructor(&ctor.name)
    })?;
    let ok_field = ok_ctor.fields.first()?;
    let err_field = err_ctor.fields.first()?;
    Some(ResultShape {
        dt_name: dt.name.clone(),
        ok_ctor_name: ok_ctor.name.clone(),
        ok_field_name: ok_field.name.clone(),
        ok_field_sort: ok_field.sort.clone(),
        err_ctor_name: err_ctor.name.clone(),
        err_field_name: err_field.name.clone(),
        err_field_sort: err_field.sort.clone(),
    })
}

pub(in crate::codegen_ay::chc) fn try_inline_result_copied_call(
    ctx: &ChcCtx<'_, '_>,
    callee_path: &str,
    translated_args: &[Expr],
    outer_body: &Body,
    destination: &Place,
) -> Option<InlineReturn> {
    if !is_result_copied_path(callee_path) || translated_args.len() != 1 {
        return None;
    }

    let receiver = translated_args.first()?.clone();
    let dest_ty = ctx
        .resolve_inline_local_ty(outer_body, destination.local)
        .or_else(|| destination.ty(outer_body.locals()).ok().map(|ty| ctx.resolve_body_ty(ty)))?;
    let dest_sort = ChcCtx::translate_ty(dest_ty)?;
    if receiver.sort() == &dest_sort {
        return Some(InlineReturn::value_only(receiver));
    }

    let src_shape = result_shape(receiver.sort())?;
    let dest_shape = result_shape(&dest_sort)?;
    let is_ok = receiver.clone().is_constructor(&src_shape.dt_name, &src_shape.ok_ctor_name);
    let ok_payload = receiver.clone().field_select(
        &src_shape.dt_name,
        &src_shape.ok_field_name,
        src_shape.ok_field_sort.clone(),
    );
    let err_payload = receiver.field_select(
        &src_shape.dt_name,
        &src_shape.err_field_name,
        src_shape.err_field_sort.clone(),
    );
    let ok_payload = if ok_payload.sort() == &dest_shape.ok_field_sort {
        ok_payload
    } else {
        ctx.coerce_value_to_sort(ok_payload, &dest_shape.ok_field_sort, false)?
    };
    let err_payload = if err_payload.sort() == &dest_shape.err_field_sort {
        err_payload
    } else {
        ctx.coerce_value_to_sort(err_payload, &dest_shape.err_field_sort, false)?
    };
    let ok_result = Expr::datatype_constructor(
        &dest_shape.dt_name,
        &dest_shape.ok_ctor_name,
        vec![ok_payload],
        dest_sort.clone(),
    );
    let err_result = Expr::datatype_constructor(
        &dest_shape.dt_name,
        &dest_shape.err_ctor_name,
        vec![err_payload],
        dest_sort,
    );
    Some(InlineReturn::value_only(Expr::ite(is_ok, ok_result, err_result)))
}
