// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! CHC-only lowering for direct floor direction assertions.

use super::ChcCtx;
use super::float_assertion_patterns::{
    LocalDef, find_local_def, follow_passthrough_uses, normalize_math_path, same_local_operand,
    trace_passthrough_local,
};
use crate::codegen_ay::chc::call::codegen_call_cmp_string::float_predicates::{
    FloatPredicateKind, build_float_predicate_expr,
};
use ay_bindings::Expr;
use rustc_public::mir::{BinOp, Operand};
use std::collections::HashSet;

pub(super) fn try_build_floorf64_direction_comparison<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    op: BinOp,
    lhs_op: &Operand,
    rhs_op: &Operand,
    modified_locals: &HashSet<usize>,
) -> Option<Expr> {
    let input = match op {
        BinOp::Le if detect_floorf64_call_with_input(ctx, lhs_op, rhs_op) => rhs_op,
        BinOp::Ge if detect_floorf64_call_with_input(ctx, rhs_op, lhs_op) => lhs_op,
        _ => return None,
    };
    let input_expr = ctx.translate_operand_with_modified(input, modified_locals)?;
    build_float_predicate_expr(&input_expr, FloatPredicateKind::Nan).map(Expr::not)
}

fn detect_floorf64_call_with_input(
    ctx: &ChcCtx<'_, '_>,
    call_operand: &Operand,
    input_operand: &Operand,
) -> bool {
    let Some(call_local) = trace_passthrough_local(ctx.body, call_operand) else {
        return false;
    };
    let Some(LocalDef::Call { func, args }) = find_local_def(ctx.body, call_local) else {
        return false;
    };
    let Some(callee) = ctx.resolve_callee_path(func).map(normalize_math_path) else {
        return false;
    };
    if !callee.ends_with("floorf64") {
        return false;
    }
    let Some(call_input) = args.first().and_then(|arg| follow_passthrough_uses(ctx.body, arg))
    else {
        return false;
    };
    same_local_operand(ctx.body, call_input, input_operand)
}
