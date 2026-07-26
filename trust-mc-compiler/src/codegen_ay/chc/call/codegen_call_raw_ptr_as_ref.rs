// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Raw pointer `as_ref`/`as_mut` Option construction for CHC call dispatch.

use std::collections::HashSet;

use ay_bindings::{Expr, Sort};
use rustc_public::mir::Operand;

use crate::codegen_ay::chc::stub_codegen::stubs_option_helpers::{
    OptionHelpers, option_value_sort,
};

use super::ChcCtx;
use super::chc_call_context::DispatchCallContext;
use super::codegen_call_coerce::CallCoerce;
use super::codegen_call_ptr_identity::{propagate_alloc_id, propagate_ref_target};
use super::codegen_rules::CodegenRules;
use super::codegen_types::CodegenTypes;
use super::dyn_coercion::extract_pointer_expr;

/// Raw pointer `{as_ref,as_mut}` returns `Option<&T>`, not pointer identity.
///
/// The stub registry intentionally does not map these to `PtrCast`: null must
/// become `None`, while non-null becomes `Some(ptr)`. Handling that here avoids
/// falling through to MIR inlining for core raw-pointer helpers and keeps fat
/// pointer / dyn-pointer paths on the precise CHC lane.
pub(super) fn try_dispatch_raw_ptr_as_ref(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
) -> bool {
    let Some(target) = *dcx.target else {
        return false;
    };
    if dcx.args.len() != 1 {
        return false;
    }

    let fallback_callee_path;
    let callee_path = if let Some(path) = dcx.callee_path.as_deref() {
        path
    } else {
        fallback_callee_path =
            ctx.resolve_callee_path(dcx.func).or_else(|| ctx.resolve_fn_def_name(dcx.func));
        let Some(path) = fallback_callee_path.as_deref() else {
            return false;
        };
        path
    };
    if !is_raw_ptr_as_ref_path(callee_path) {
        return false;
    }

    let Some(ptr_expr) = ctx
        .translate_operand_with_modified(&dcx.args[0], dcx.modified_locals)
        .or_else(|| ctx.resolve_ref_operand(&dcx.args[0], dcx.modified_locals))
    else {
        return false;
    };
    let Some(data_ptr) = extract_pointer_expr(&ptr_expr) else {
        return false;
    };
    let Some(width) = data_ptr.sort().bitvec_width() else {
        return false;
    };

    let dest_local = dcx.destination.local;
    let Some(dest_sort) = dcx
        .destination
        .ty(ctx.body.locals())
        .ok()
        .map(|ty| ctx.resolve_body_ty(ty))
        .and_then(ChcCtx::translate_ty)
    else {
        return false;
    };
    let src_local = dcx.args.first().and_then(|arg| match arg {
        Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
            Some(place.local)
        }
        _ => None,
    });
    let Some((some_expr, vtable_expr)) = raw_ptr_as_ref_some_expr(
        ctx,
        &dcx.args[0],
        dcx.modified_locals,
        ptr_expr,
        data_ptr.clone(),
        &dest_sort,
        src_local,
    ) else {
        return false;
    };
    let Some(none_expr) = ctx.make_none_expr_for_option(&dest_sort) else {
        return false;
    };
    let result =
        Expr::ite(data_ptr.clone().eq(Expr::bitvec_const(0u64, width)), none_expr, some_expr);

    let ptr_obj_id = ChcCtx::try_extract_obj_id(&data_ptr);
    propagate_alloc_id(ctx, dest_local, src_local);
    propagate_ref_target(ctx, dest_local, src_local, ptr_obj_id);
    let vtable_constraint =
        vtable_expr.and_then(|vtable| ctx.capture_known_vtable_discriminant(dest_local, vtable));

    if let Some(mut flat_constraints) =
        ctx.build_flattened_destination_constraints(dest_local, result.clone())
    {
        flat_constraints.extend(vtable_constraint.clone());
        let new_output_args = ctx.build_output_args(dcx.modified_locals, &[dest_local]);
        ctx.emit_goto_rule_extra(
            dcx.from_app,
            target,
            &new_output_args,
            dcx.stmt_constraints,
            flat_constraints,
        );
        return true;
    }

    let Some((_, dest_var)) = ctx.resolve_destination(dest_local) else {
        return false;
    };
    let Some(eq) = ctx.make_coerced_eq_constraint(
        &dest_var,
        result,
        dest_var.sort(),
        dest_local,
        "raw_ptr_as_ref",
    ) else {
        return false;
    };
    let mut extra = Vec::with_capacity(1 + usize::from(vtable_constraint.is_some()));
    extra.push(eq);
    extra.extend(vtable_constraint);
    let new_output_args = ctx.build_output_args(dcx.modified_locals, &[dest_local]);
    ctx.emit_goto_rule_extra(dcx.from_app, target, &new_output_args, dcx.stmt_constraints, extra);
    true
}

fn raw_ptr_as_ref_some_expr(
    ctx: &mut ChcCtx<'_, '_>,
    operand: &Operand,
    modified_locals: &HashSet<usize>,
    ptr_expr: Expr,
    data_ptr: Expr,
    dest_sort: &Sort,
    src_local: Option<usize>,
) -> Option<(Expr, Option<Expr>)> {
    let dyn_payload_sort = dyn_option_payload_sort(dest_sort);
    if let Some(some_expr) = ctx.make_some_expr_for_option(ptr_expr.clone(), dest_sort) {
        let vtable_expr = dyn_payload_sort
            .is_some()
            .then(|| {
                raw_ptr_as_ref_vtable_expr(ctx, operand, modified_locals, &ptr_expr, src_local)
            })
            .flatten();
        return Some((some_expr, vtable_expr));
    }

    let payload_sort = dyn_payload_sort?;
    let vtable_expr =
        raw_ptr_as_ref_vtable_expr(ctx, operand, modified_locals, &ptr_expr, src_local)?;
    let dyn_payload =
        make_dyn_payload_for_raw_ptr(ctx, data_ptr, vtable_expr.clone(), payload_sort)?;
    let some_expr = ctx.make_some_expr_for_option(dyn_payload, dest_sort)?;
    Some((some_expr, Some(vtable_expr)))
}

fn dyn_option_payload_sort(option_sort: &Sort) -> Option<Sort> {
    let payload_sort = option_value_sort(option_sort)?;
    is_dyn_payload_sort(&payload_sort).then_some(payload_sort)
}

fn is_dyn_payload_sort(sort: &Sort) -> bool {
    let Some(dt) = sort.datatype_sort() else {
        return false;
    };
    let Some(ctor) = dt.constructors.first() else {
        return false;
    };
    ctor.fields.iter().any(|field| field.name == "fld_ptr")
        && ctor.fields.iter().any(|field| field.name == "fld_vtable")
}

fn raw_ptr_as_ref_vtable_expr(
    ctx: &ChcCtx<'_, '_>,
    operand: &Operand,
    modified_locals: &HashSet<usize>,
    ptr_expr: &Expr,
    src_local: Option<usize>,
) -> Option<Expr> {
    ctx.extract_embedded_vtable_expr(ptr_expr)
        .or_else(|| src_local.and_then(|local| ctx.known_vtable_expr_for_local(local)))
        .or_else(|| ctx.translate_ptr_metadata(operand, modified_locals))
}

fn make_dyn_payload_for_raw_ptr(
    ctx: &mut ChcCtx<'_, '_>,
    data_ptr: Expr,
    vtable_expr: Expr,
    payload_sort: Sort,
) -> Option<Expr> {
    let dt = payload_sort.datatype_sort()?;
    let ctor = dt.constructors.first()?;
    let dt_name = dt.name.clone();
    let ctor_name = ctor.name.clone();
    let fields = ctor
        .fields
        .iter()
        .map(|field| {
            if field.name == "fld_ptr" {
                ctx.coerce_value_to_sort(data_ptr.clone(), &field.sort, false)
            } else if field.name == "fld_vtable" {
                ctx.coerce_value_to_sort(vtable_expr.clone(), &field.sort, false)
            } else {
                None
            }
        })
        .collect::<Option<Vec<_>>>()?;
    ctx.declare_datatype_sort_if_needed(&payload_sort);
    Some(Expr::datatype_constructor(&dt_name, &ctor_name, fields, payload_sort))
}

fn is_raw_ptr_as_ref_path(callee_path: &str) -> bool {
    (callee_path.ends_with("::as_ref") || callee_path.ends_with("::as_mut"))
        && (callee_path.contains("ptr::const_ptr")
            || callee_path.contains("ptr::mut_ptr")
            || callee_path.contains("*const")
            || callee_path.contains("*mut"))
}
