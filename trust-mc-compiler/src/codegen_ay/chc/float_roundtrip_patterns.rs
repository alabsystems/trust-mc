// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Part of #4110: float-to-int round-trip assertion bypass.
//!
//! Detects `(float_to_int_unchecked(f) as Float) == f.trunc()` and replaces
//! the full IntToFloat + trunc + float Eq encoding with `is_finite(f)`.
//! The round-trip is correct by construction for finite, in-range inputs,
//! and the harness preconditions constrain exactly that domain.

use std::collections::HashSet;

use ay_bindings::Expr;
use rustc_public::mir::{BinOp, CastKind, Operand, Rvalue};

use super::ChcCtx;
use super::codegen_ctx::diagnostics::CellCounter;
use super::float_assertion_patterns::{
    LocalDef, RoundingKind, detect_rounding_kind, find_local_def, follow_passthrough_uses,
    normalize_math_path, same_local_operand, trace_passthrough_local,
};
use crate::codegen_ay::chc::call::codegen_call_cmp_string::float_predicates::{
    FloatPredicateKind, build_float_predicate_expr,
};

struct RoundtripPattern<'body> {
    float_input: &'body Operand,
}

pub(in crate::codegen_ay) fn try_build_float_roundtrip_comparison<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    op: BinOp,
    lhs_op: &Operand,
    rhs_op: &Operand,
    modified_locals: &HashSet<usize>,
) -> Option<Expr> {
    let pattern = detect_float_roundtrip_comparison(ctx, op, lhs_op, rhs_op)?;
    let input = ctx.translate_operand_with_modified(pattern.float_input, modified_locals)?;
    let finite = build_float_predicate_expr(&input, FloatPredicateKind::Finite)?;
    let result = match op {
        BinOp::Eq => finite,
        BinOp::Ne => finite.not(),
        _ => return None,
    };
    // AUDIT (task #65, rounding_assertion_bypass): GENUINELY WEAKENING — keep
    // counting. On the DEFINED domain (f finite AND trunc(f) in the target
    // int's range) the equality is a tautology (truncation is exact, and the
    // IntToFloat cast of a value that came from a float is exact), so there
    // `is_finite(f)` matches it. But `is_finite(f)` is also TRUE for finite
    // OUT-OF-RANGE f, where `float_to_int_unchecked` is UB. That domain is
    // normally fail-closed by the intrinsic handler's own UB error rule
    // (codegen_float_to_int_unchecked emits a NaN/inf/range check), yet the
    // exactness of THIS rewrite then rests on a cross-site invariant: if the
    // call-site handler falls back (untranslatable operand → unconstrained
    // havoc, no UB rule) while this comparison rewrite still fires, the
    // bypassed equality can mask the UB. Not provably exact by local
    // reasoning → counted, and the plumbed DEMOTED category fail-closes any
    // PROOF that used it.
    ctx.diagnostics.rounding_assertion_bypass.inc();
    Some(result)
}

fn detect_float_roundtrip_comparison<'tcx, 'body>(
    ctx: &ChcCtx<'tcx, 'body>,
    op: BinOp,
    lhs_op: &'body Operand,
    rhs_op: &'body Operand,
) -> Option<RoundtripPattern<'body>> {
    if !matches!(op, BinOp::Eq | BinOp::Ne) {
        return None;
    }
    detect_roundtrip_ordered(ctx, lhs_op, rhs_op)
        .or_else(|| detect_roundtrip_ordered(ctx, rhs_op, lhs_op))
}

/// Check if `cast_side` is `IntToFloat(float_to_int_unchecked(f))` and
/// `trunc_side` is `trunc(f)` with the same float input `f`.
fn detect_roundtrip_ordered<'tcx, 'body>(
    ctx: &ChcCtx<'tcx, 'body>,
    cast_side: &'body Operand,
    trunc_side: &'body Operand,
) -> Option<RoundtripPattern<'body>> {
    let cast_local = trace_passthrough_local(ctx.body, cast_side)?;
    let LocalDef::Assign(rvalue) = find_local_def(ctx.body, cast_local)? else {
        return None;
    };
    let Rvalue::Cast(CastKind::IntToFloat, int_operand, _target_ty) = rvalue else {
        return None;
    };

    let int_local = trace_passthrough_local(ctx.body, int_operand)?;
    let LocalDef::Call { func, args } = find_local_def(ctx.body, int_local)? else {
        return None;
    };
    let callee_path = ctx.resolve_callee_path(func)?;
    if !callee_path.contains("float_to_int_unchecked") {
        return None;
    }
    let fti_input = follow_passthrough_uses(ctx.body, args.first()?)?;

    let trunc_local = trace_passthrough_local(ctx.body, trunc_side)?;
    let LocalDef::Call { func: trunc_func, args: trunc_args } =
        find_local_def(ctx.body, trunc_local)?
    else {
        return None;
    };
    let trunc_path = normalize_math_path(ctx.resolve_callee_path(trunc_func)?);
    if !matches!(detect_rounding_kind(&trunc_path), Some(RoundingKind::Trunc)) {
        return None;
    }
    let trunc_input = follow_passthrough_uses(ctx.body, trunc_args.first()?)?;

    if !same_local_operand(ctx.body, fti_input, trunc_input) {
        return None;
    }

    Some(RoundtripPattern { float_input: fti_input })
}
