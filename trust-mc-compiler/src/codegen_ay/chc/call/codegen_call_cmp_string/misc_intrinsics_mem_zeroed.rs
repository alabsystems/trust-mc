// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Precise CHC `mem::zeroed()` handler for direct call form.
//!
//! `std::mem::zeroed::<T>()` may appear as a direct function call in MIR
//! (rather than being lowered to `write_bytes(dst, 0u8, 1)` intrinsic).
//! This module handles the direct call form by building a typed zero
//! expression for the destination's actual AY sort.
//!
//! Sort-based zero construction handles flattened struct destinations
//! correctly — when a struct is flattened to scalar fields, the destination
//! local has a BV sort (first field) instead of a Datatype sort.
//!
//! Part of #3702.

use ay_bindings::{Expr, Sort};
use rustc_public::mir::BasicBlockIdx;
use tracing::debug;

use super::super::ChcCtx;
use super::super::chc_call_context::DispatchCallContext;
use super::super::codegen_call_coerce::{CallCoerce, emit_sound_fallback_goto};
use super::super::codegen_rules::CodegenRules;

/// Handle `std::mem::zeroed::<T>() -> T` — produce typed zero for destination.
///
/// Gets the destination sort from the resolved state variable, builds a zero
/// expression, and constrains the destination. Falls back to type-based zero
/// or unconstrained if the sort cannot be zero-filled.
pub(in crate::codegen_ay::chc) fn codegen_mem_zeroed(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    target: BasicBlockIdx,
) {
    let dest_local: usize = dcx.destination.local;
    let dest_ty = ctx.body.locals().get(dest_local).map(|l| l.ty);

    if let Some(dest_ty) = dest_ty
        && let Some(zero_expr) = super::misc_intrinsics_write_bytes::zero_expr_for_ty(dest_ty)
        && let Some(flat_constraints) =
            ctx.build_flattened_destination_constraints(dest_local, zero_expr)
    {
        let out = ctx.build_output_args(dcx.modified_locals, &[dest_local]);
        if flat_constraints.is_empty() {
            ctx.emit_goto_rule(dcx.from_app, target, &out, dcx.stmt_constraints);
        } else {
            ctx.emit_goto_rule_extra(
                dcx.from_app,
                target,
                &out,
                dcx.stmt_constraints,
                flat_constraints,
            );
        }
        debug!(
            dest_local,
            "CHC: mem::zeroed() encoded via flattened destination constraints (Part of #3702)"
        );
        return;
    }

    // Resolve destination and build zero for its actual sort (handles flattening).
    if let Some((_, dest_var)) = ctx.resolve_destination(dest_local) {
        let dest_sort = dest_var.sort().clone();
        if let Some(zero) = zero_expr_for_sort(&dest_sort) {
            let eq = dest_var.eq(zero);
            let out = ctx.build_output_args(dcx.modified_locals, &[dest_local]);
            ctx.emit_goto_rule_extra(dcx.from_app, target, &out, dcx.stmt_constraints, [eq]);
            debug!("CHC: mem::zeroed() encoded precisely (Part of #3702)");
            return;
        }
    }

    // Fall back: try type-based zero for non-flattened destinations.
    let zero_expr = dest_ty.and_then(super::misc_intrinsics_write_bytes::zero_expr_for_ty);
    if let Some(zero) = zero_expr {
        if let Some((_, dest_var)) = ctx.resolve_destination(dest_local) {
            let dest_sort = dest_var.sort().clone();
            let mut extra = Vec::new();
            if let Some(eq) = ctx.make_coerced_eq_constraint(
                &dest_var,
                zero,
                &dest_sort,
                dest_local,
                "mem_zeroed",
            ) {
                extra.push(eq);
            }
            let out = ctx.build_output_args(dcx.modified_locals, &[dest_local]);
            if extra.is_empty() {
                ctx.emit_goto_rule(dcx.from_app, target, &out, dcx.stmt_constraints);
            } else {
                ctx.emit_goto_rule_extra(dcx.from_app, target, &out, dcx.stmt_constraints, extra);
            }
            debug!("CHC: mem::zeroed() encoded via type-based zero (Part of #3702)");
            return;
        }
    }

    // Fall back to unconstrained if zero_expr cannot be built.
    debug!(?dest_ty, "CHC: mem::zeroed() fallback — type not zero-fillable");
    emit_sound_fallback_goto(
        ctx,
        dcx.from_app,
        target,
        dcx.modified_locals,
        &[dest_local],
        dcx.stmt_constraints,
    );
}

/// Build a typed zero expression from a AY sort.
///
/// Handles scalar sorts: BV → 0, Bool → false, Int → 0.
/// For Datatype sorts, constructs the zero value field by field recursively.
fn zero_expr_for_sort(sort: &Sort) -> Option<Expr> {
    if sort.is_bool() {
        return Some(Expr::bool_const(false));
    }
    if let Some(width) = sort.bitvec_width() {
        return Some(Expr::bitvec_const(0u128, width));
    }
    if sort.is_int() {
        return Some(Expr::int_const(0));
    }
    // Datatype: construct zero for each field recursively.
    if let Some(dt) = sort.datatype_sort() {
        let ctor = dt.constructors.first()?;
        let mut field_zeros = Vec::with_capacity(ctor.fields.len());
        for field in &ctor.fields {
            let fz = zero_expr_for_sort(&field.sort)?;
            field_zeros.push(fz);
        }
        return Some(Expr::datatype_constructor(&dt.name, &ctor.name, field_zeros, sort.clone()));
    }
    None
}
