// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! CHC-only float solver-efficiency patterns for finite checks and fast-math equality.

use super::ChcCtx;
use super::float_assertion_patterns::{
    LocalDef, find_local_def, follow_passthrough_uses, is_float_abs_mask, normalize_math_path,
    operand_local, same_local_operand, trace_passthrough_local,
};
use crate::codegen_ay::chc::call::codegen_call_cmp_string::float_predicates::{
    FloatPredicateKind, build_float_predicate_expr,
};
use crate::codegen_ay::chc::call::codegen_call_cmp_string::math_const::{
    try_extract_const_f32, try_extract_const_f64,
};
use ay_bindings::Expr;
use rustc_public::mir::{BinOp, Body, Operand, Rvalue};
use std::collections::HashSet;

pub(in crate::codegen_ay) fn try_build_float_finite_comparison<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    op: BinOp,
    lhs_op: &Operand,
    rhs_op: &Operand,
    modified_locals: &HashSet<usize>,
) -> Option<Expr> {
    let input = detect_finite_abs_lt_infinity(ctx, op, lhs_op, rhs_op)?;
    let input = ctx.translate_operand_with_modified(input, modified_locals)?;
    // AUDIT (task #65, rounding_assertion_bypass): the `|x| < +inf` →
    // `is_finite(x)` rewrite is PROVABLY EXACT for every input, including NaN:
    //   - x finite      → |x| finite → |x| < +inf TRUE;  exp(x) ≠ all-ones TRUE
    //   - x = ±inf      → |x| = +inf → +inf < +inf FALSE; Finite bit-pred FALSE
    //   - x = NaN       → |x| = NaN  → NaN < +inf  FALSE (IEEE unordered);
    //                     Finite bit-pred FALSE (exp all-ones)
    // IEEE abs (sign-mask bitand or fabs call, both matched by
    // detect_plain_abs_input) is exact and maps NaN→NaN, so the abs step never
    // perturbs the classification. `build_float_predicate_expr(Finite)` is the
    // bit-exact exponent test. No behavior is added or dropped, so this site
    // does NOT count as a rounding-assertion bypass (previously incremented
    // `rounding_assertion_bypass`, which now demotes PROOFs when plumbed).
    build_float_predicate_expr(&input, FloatPredicateKind::Finite)
}

pub(in crate::codegen_ay::chc) fn float_finite_condition_matches_operand<'tcx, 'body>(
    ctx: &ChcCtx<'tcx, 'body>,
    cond: &'body Operand,
    operand: &'body Operand,
) -> bool {
    detect_float_finite_condition_input(ctx, cond)
        .is_some_and(|input| same_local_operand(ctx.body, input, operand))
}

pub(in crate::codegen_ay) fn try_build_float_fast_math_equiv_comparison<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    op: BinOp,
    lhs_op: &Operand,
    rhs_op: &Operand,
) -> Option<Expr> {
    if !matches!(op, BinOp::Eq | BinOp::Ne) {
        return None;
    }

    let equivalent = detect_fast_math_regular_binop_equiv(ctx, lhs_op, rhs_op)
        || detect_fast_math_regular_binop_equiv(ctx, rhs_op, lhs_op);
    equivalent.then(|| Expr::bool_const(matches!(op, BinOp::Eq)))
}

fn detect_float_finite_condition_input<'tcx, 'body>(
    ctx: &ChcCtx<'tcx, 'body>,
    cond: &'body Operand,
) -> Option<&'body Operand> {
    let cond = follow_passthrough_uses(ctx.body, cond)?;
    let local = operand_local(cond)?;
    let LocalDef::Assign(rvalue) = find_local_def(ctx.body, local)? else {
        return None;
    };
    let (Rvalue::BinaryOp(op, lhs, rhs) | Rvalue::CheckedBinaryOp(op, lhs, rhs)) = rvalue else {
        return None;
    };
    detect_finite_abs_lt_infinity(ctx, *op, lhs, rhs)
}

fn detect_fast_math_regular_binop_equiv<'tcx, 'body>(
    ctx: &ChcCtx<'tcx, 'body>,
    fast_side: &'body Operand,
    regular_side: &'body Operand,
) -> bool {
    let Some(fast_local) = trace_passthrough_local(ctx.body, fast_side) else {
        return false;
    };
    let Some(LocalDef::Call { func, args }) = find_local_def(ctx.body, fast_local) else {
        return false;
    };
    let Some(callee) = ctx.resolve_callee_path(func) else {
        return false;
    };
    let Some(fast_op) = detect_fast_math_binop(&callee) else {
        return false;
    };
    let (Some(fast_lhs), Some(fast_rhs)) = (args.first(), args.get(1)) else {
        return false;
    };
    let Some(fast_lhs) = follow_passthrough_uses(ctx.body, fast_lhs) else {
        return false;
    };
    let Some(fast_rhs) = follow_passthrough_uses(ctx.body, fast_rhs) else {
        return false;
    };

    let Some(regular_local) = trace_passthrough_local(ctx.body, regular_side) else {
        return false;
    };
    let Some(LocalDef::Assign(regular_rvalue)) = find_local_def(ctx.body, regular_local) else {
        return false;
    };
    let (Rvalue::BinaryOp(regular_op, regular_lhs, regular_rhs)
    | Rvalue::CheckedBinaryOp(regular_op, regular_lhs, regular_rhs)) = regular_rvalue
    else {
        return false;
    };
    if *regular_op != fast_op {
        return false;
    }
    let Some(regular_lhs) = follow_passthrough_uses(ctx.body, regular_lhs) else {
        return false;
    };
    let Some(regular_rhs) = follow_passthrough_uses(ctx.body, regular_rhs) else {
        return false;
    };

    same_order_operands(ctx.body, fast_lhs, fast_rhs, regular_lhs, regular_rhs)
        || (is_commutative_float_fast_op(fast_op)
            && same_order_operands(ctx.body, fast_lhs, fast_rhs, regular_rhs, regular_lhs))
}

fn detect_fast_math_binop(callee: &str) -> Option<BinOp> {
    if callee.contains("fadd_fast") {
        Some(BinOp::Add)
    } else if callee.contains("fsub_fast") {
        Some(BinOp::Sub)
    } else if callee.contains("fmul_fast") {
        Some(BinOp::Mul)
    } else if callee.contains("fdiv_fast") {
        Some(BinOp::Div)
    } else {
        None
    }
}

fn is_commutative_float_fast_op(op: BinOp) -> bool {
    matches!(op, BinOp::Add | BinOp::Mul)
}

fn same_order_operands(
    body: &Body,
    lhs_a: &Operand,
    rhs_a: &Operand,
    lhs_b: &Operand,
    rhs_b: &Operand,
) -> bool {
    same_local_operand(body, lhs_a, lhs_b) && same_local_operand(body, rhs_a, rhs_b)
}

fn detect_finite_abs_lt_infinity<'tcx, 'body>(
    ctx: &ChcCtx<'tcx, 'body>,
    op: BinOp,
    lhs_op: &'body Operand,
    rhs_op: &'body Operand,
) -> Option<&'body Operand> {
    if matches!(op, BinOp::Lt) && is_positive_infinity(ctx.body, rhs_op) {
        return detect_plain_abs_input(ctx, lhs_op);
    }

    if matches!(op, BinOp::Gt) && is_positive_infinity(ctx.body, lhs_op) {
        return detect_plain_abs_input(ctx, rhs_op);
    }

    None
}

fn is_positive_infinity(body: &Body, operand: &Operand) -> bool {
    matches!(try_extract_const_f32(operand, body), Some(0x7F80_0000))
        || matches!(try_extract_const_f64(operand, body), Some(0x7FF0_0000_0000_0000))
}

fn detect_plain_abs_input<'tcx, 'body>(
    ctx: &ChcCtx<'tcx, 'body>,
    operand: &'body Operand,
) -> Option<&'body Operand> {
    let operand = follow_passthrough_uses(ctx.body, operand)?;
    if let Some(input) = detect_plain_masked_abs_input(ctx, operand) {
        return Some(input);
    }
    detect_plain_call_abs_input(ctx, operand)
}

fn detect_plain_masked_abs_input<'tcx, 'body>(
    ctx: &ChcCtx<'tcx, 'body>,
    operand: &'body Operand,
) -> Option<&'body Operand> {
    let local = operand_local(operand)?;
    let LocalDef::Assign(rvalue) = find_local_def(ctx.body, local)? else {
        return None;
    };
    let (Rvalue::BinaryOp(op, lhs, rhs) | Rvalue::CheckedBinaryOp(op, lhs, rhs)) = rvalue else {
        return None;
    };
    if !matches!(op, BinOp::BitAnd) {
        return None;
    }

    if is_float_abs_mask(ctx.body, lhs) {
        follow_passthrough_uses(ctx.body, rhs)
    } else if is_float_abs_mask(ctx.body, rhs) {
        follow_passthrough_uses(ctx.body, lhs)
    } else {
        None
    }
}

fn detect_plain_call_abs_input<'tcx, 'body>(
    ctx: &ChcCtx<'tcx, 'body>,
    operand: &'body Operand,
) -> Option<&'body Operand> {
    let local = trace_passthrough_local(ctx.body, operand)?;
    let LocalDef::Call { func, args } = find_local_def(ctx.body, local)? else {
        return None;
    };

    let callee = normalize_math_path(ctx.resolve_callee_path(func)?);
    is_abs_call(&callee).then(|| follow_passthrough_uses(ctx.body, args.first()?))?
}

fn is_abs_call(path: &str) -> bool {
    path.ends_with("fabsf32")
        || path.ends_with("fabsf64")
        || (path.ends_with("abs") && (path.contains("f32") || path.contains("f64")))
}
