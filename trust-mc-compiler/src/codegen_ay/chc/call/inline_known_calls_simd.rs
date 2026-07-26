// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! SIMD intrinsic inlining for inline known calls.
//!
//! Extracted from `inline_known_calls.rs` — Part of #4206.

use ay_bindings::Expr;
use rustc_public::mir::{BinOp, LocalDecl, Operand};

use crate::codegen_ay::types::POINTER_WIDTH;

pub(super) fn inline_simd_intrinsic_expr(
    callee_path: &str,
    translated_args: &[Expr],
    first_arg: Option<&Operand>,
    caller_locals: &[LocalDecl],
) -> Option<Expr> {
    if !callee_path.contains("simd") {
        return None;
    }
    let method = callee_path.rsplit("::").next()?;
    let op = match method {
        "simd_add" => BinOp::Add,
        "simd_sub" => BinOp::Sub,
        "simd_mul" => BinOp::Mul,
        _ => return None,
    };
    if translated_args.len() != 2 {
        return None;
    }
    let lhs = unwrap_inline_simd_to_array(&translated_args[0]);
    let rhs = unwrap_inline_simd_to_array(&translated_args[1]);
    if !lhs.sort().is_array() || !rhs.sort().is_array() {
        return None;
    }
    let lane_count = extract_inline_simd_lane_count(first_arg, caller_locals)?;
    let elem_width = lhs.sort().array_sort()?.element_sort.bitvec_width()?;
    let is_float = is_float_elem_width_from_type(first_arg, caller_locals);
    let mut result = lhs.clone();
    for i in 0..lane_count {
        let idx = Expr::bitvec_const(i as u64, POINTER_WIDTH);
        let a = lhs.clone().select(idx.clone());
        let b = rhs.clone().select(idx.clone());
        let val = if is_float {
            // Fail closed on symbolic float lanes: `bv_float_binop_chc`
            // constant-folds when both lanes are concrete, otherwise returns
            // None. Falling back to `apply_bv_binop` would do integer BV
            // arithmetic on IEEE 754 bit patterns, which is unsound.
            // Bubble the None up so the inline SIMD path gives up rather
            // than synthesizing wrong values (Part of ay#6370).
            crate::codegen_ay::float_arithmetic::bv_float_binop_chc(
                op,
                a.clone(),
                b.clone(),
                elem_width,
            )?
        } else {
            apply_bv_binop(a, b, op)
        };
        result = result.store(idx, val);
    }
    Some(result)
}

fn apply_bv_binop(a: Expr, b: Expr, op: BinOp) -> Expr {
    match op {
        BinOp::Add | BinOp::AddUnchecked => a.bvadd(b),
        BinOp::Sub | BinOp::SubUnchecked => a.bvsub(b),
        BinOp::Mul | BinOp::MulUnchecked => a.bvmul(b),
        _ => a.bvadd(b),
    }
}

/// Unwrap Datatype(single Array field) to bare Array, same as `unwrap_simd_to_array`
/// in `codegen_call_simd.rs` but without requiring `ChcCtx`.
fn unwrap_inline_simd_to_array(expr: &Expr) -> Expr {
    if expr.sort().is_array() {
        return expr.clone();
    }
    if let Some(dt) = expr.sort().datatype_sort() {
        if dt.constructors.len() == 1 && dt.constructors[0].fields.len() == 1 {
            let field = &dt.constructors[0].fields[0];
            if field.sort.is_array() {
                return expr.clone().field_select(
                    dt.name.clone(),
                    field.name.clone(),
                    field.sort.clone(),
                );
            }
        }
    }
    expr.clone()
}

/// Extract lane count from the MIR type of the first SIMD operand.
fn extract_inline_simd_lane_count(
    first_arg: Option<&Operand>,
    caller_locals: &[LocalDecl],
) -> Option<usize> {
    use super::codegen_call_simd::extract_simd_layout;
    let arg = first_arg?;
    let ty = arg.ty(caller_locals).ok()?;
    let layout = extract_simd_layout(ty)?;
    Some(layout.lane_count)
}

/// Check whether the element type is float from the MIR type.
fn is_float_elem_width_from_type(first_arg: Option<&Operand>, caller_locals: &[LocalDecl]) -> bool {
    use super::codegen_call_simd::extract_simd_layout;
    first_arg
        .and_then(|arg| arg.ty(caller_locals).ok())
        .and_then(|ty| extract_simd_layout(ty))
        .is_some_and(|layout| layout.is_float)
}
