// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Sound range axioms for transcendental math intrinsics (Part of #3609).
//!
//! Unlike the exact BV encodings in `math_axioms.rs`, these do NOT define the
//! result precisely. They constrain the unconstrained symbolic result to a valid
//! range, eliminating spurious counterexamples where e.g. sin(x) = 1000.0.
//!
//! Sound because: every concrete execution satisfies these bounds.
//!
//! Handles:
//! - sin/cos: result in [-1.0, 1.0], NaN propagation
//! - sqrt: result >= 0 for non-negative input
//! - exp/exp2: result > 0 for finite input
//! - powf/powi with even exponent: result >= 0

use ay_bindings::Expr;

use super::float_predicates::{FloatPredicateKind, build_float_predicate_expr};
use crate::codegen_ay::float_compare::{bv_float_le, bv_float_lt};

/// Create a BV constant representing the given f64 value in the specified float width.
///
/// Used for encoding IEEE 754 constant values (0.0, 1.0, -1.0) in range axioms.
fn float_const_bv(val: f64, width: u32) -> Expr {
    match width {
        32 => Expr::bitvec_const((val as f32).to_bits() as u64, 32),
        64 => Expr::bitvec_const(val.to_bits(), 64),
        _ => unreachable!("float_const_bv: unsupported width {width}"),
    }
}

/// Emit sound range axioms for transcendental math intrinsics.
///
/// Constrains the unconstrained symbolic result to a mathematically valid range:
/// - sin/cos: result in [-1.0, 1.0] + NaN propagation (D1+D6)
/// - sqrt: result >= 0 for non-negative input (D1)
/// - exp/exp2: result > 0 for finite input (D1)
pub(in crate::codegen_ay::chc) fn emit_range_axioms(
    intrinsic_name: &str,
    input: &Expr,
    result: &Expr,
    width: u32,
) -> Vec<Expr> {
    let mut axioms = Vec::new();

    // sin/cos: result in [-1.0, 1.0]
    let is_sin = intrinsic_name.ends_with("sinf32") || intrinsic_name.ends_with("sinf64");
    let is_cos = intrinsic_name.ends_with("cosf32") || intrinsic_name.ends_with("cosf64");
    if is_sin || is_cos {
        // Range axioms are CONDITIONAL on finite input (soundness).
        // sin(inf) = NaN, cos(inf) = NaN — unconditional `-1 <= result <= 1`
        // would eliminate these valid paths since bv_float_le(NaN, 1.0) = false.
        if let Some(fin) = build_float_predicate_expr(input, FloatPredicateKind::Finite) {
            let neg_one = float_const_bv(-1.0, width);
            let pos_one = float_const_bv(1.0, width);
            axioms.push(fin.clone().implies(bv_float_le(&neg_one, result, width)));
            axioms.push(fin.implies(bv_float_le(result, &pos_one, width)));
        }
        // NaN propagation: sin(NaN) = NaN, cos(NaN) = NaN (D6 soundness guard).
        if let (Some(in_nan), Some(res_nan)) = (
            build_float_predicate_expr(input, FloatPredicateKind::Nan),
            build_float_predicate_expr(result, FloatPredicateKind::Nan),
        ) {
            axioms.push(in_nan.implies(res_nan));
        }
    }

    // sqrt: result >= 0 for non-negative input
    if intrinsic_name.ends_with("sqrtf32") || intrinsic_name.ends_with("sqrtf64") {
        let zero = float_const_bv(0.0, width);
        let input_nonneg = bv_float_le(&zero, input, width);
        let result_nonneg = bv_float_le(&zero, result, width);
        axioms.push(input_nonneg.implies(result_nonneg));
    }

    // exp/exp2: result > 0 for finite input
    let is_exp = intrinsic_name.ends_with("expf32")
        || intrinsic_name.ends_with("expf64")
        || intrinsic_name.ends_with("exp2f32")
        || intrinsic_name.ends_with("exp2f64");
    if is_exp {
        let zero = float_const_bv(0.0, width);
        if let Some(fin) = build_float_predicate_expr(input, FloatPredicateKind::Finite) {
            let result_pos = bv_float_lt(&zero, result, width);
            axioms.push(fin.implies(result_pos));
        }
    }

    axioms
}

/// Emit even-power non-negativity axiom: finite(x) implies x^(2n) >= 0 (D2).
///
/// For powf(x, 2.0) and powi(x, 2), the result is always non-negative when
/// the input is finite. The caller must verify the exponent is a constant even
/// integer before calling this function.
pub(in crate::codegen_ay::chc) fn emit_power_nonneg_axiom(
    input: &Expr,
    result: &Expr,
    width: u32,
) -> Vec<Expr> {
    let zero = float_const_bv(0.0, width);
    let result_nonneg = bv_float_le(&zero, result, width);
    // Condition on finite input: pow(NaN, 2) = NaN is not >= 0.
    if let Some(fin) = build_float_predicate_expr(input, FloatPredicateKind::Finite) {
        vec![fin.implies(result_nonneg)]
    } else {
        Vec::new()
    }
}
