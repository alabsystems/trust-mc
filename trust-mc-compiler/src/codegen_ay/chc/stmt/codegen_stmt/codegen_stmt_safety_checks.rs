// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Arithmetic safety check conditions for CHC encoding.
//!
//! Extracted from codegen_stmt.rs to keep that file under the 500-line limit.
//! Mirrors `statement::arithmetic_checks` for the CHC path.
//!
//! Part of #3363: CHC path had no shift distance or division safety checks,
//! producing false PROOF verdicts on intentionally buggy harnesses.
//!
//! Also hosts the NaN-generation obligation for symbolic float binops (Kani
//! `--nan-check` parity) — the fail-closed companion of the congruent
//! float-binop table lane (see float_binop_table.rs).

use ay_bindings::{Expr, ExprValue};
use rustc_public::mir::{BinOp, Operand};

use crate::codegen_ay::chc::call::codegen_call_cmp_string::fast_math::has_dominating_finite_assume;
use crate::codegen_ay::float_arithmetic::is_float_arithmetic_op;

use super::super::ChcCtx;

/// Compute the "valid shift distance" condition for unchecked shift ops.
///
/// Returns a boolean expression that is `true` when the shift distance is
/// valid (not excessive and not negative). The caller pushes this to
/// `safety_checks` so the rule generator emits `¬valid → error()`.
///
/// Mirrors `statement::arithmetic_checks::emit_shift_distance_check` for CHC.
/// Part of #3363. Visibility widened to `crate::codegen_ay::chc` so the SIMD
/// call path can reuse it for per-lane `simd_shl`/`simd_shr` UB checks.
pub(in crate::codegen_ay::chc) fn unchecked_shift_distance_condition(
    value: &Expr,
    distance: &Expr,
    distance_signed: bool,
) -> Option<Expr> {
    let value_width = value.sort().bitvec_width()?;
    let distance_width = distance.sort().bitvec_width()?;

    // Compare in the wider of the two widths to avoid truncation.
    let compare_width = std::cmp::max(value_width, distance_width);
    let distance_coerced = if distance_width < compare_width {
        distance.clone().zero_extend(compare_width - distance_width)
    } else {
        distance.clone()
    };
    let width_const = Expr::bitvec_const(value_width as u64, compare_width);

    // Condition: distance < value_width (unsigned) — catches excessive shifts
    let valid_distance = distance_coerced.clone().bvult(width_const);

    if distance_signed {
        // Also check: distance >= 0 (signed) — catches negative shift amounts
        let zero = Expr::bitvec_const(0u64, compare_width);
        let non_negative = distance_coerced.bvsge(zero);
        Some(valid_distance.and(non_negative))
    } else {
        Some(valid_distance)
    }
}

/// Compute the "divisor is nonzero" condition for div/rem operations.
///
/// Returns `divisor != 0`. Division by zero is UB in Rust.
/// Mirrors `statement::arithmetic_checks::emit_division_by_zero_check`.
/// Part of #3363.
pub(in crate::codegen_ay::chc) fn division_by_zero_condition(divisor: &Expr) -> Option<Expr> {
    let width = divisor.sort().bitvec_width()?;
    let zero = Expr::bitvec_const(0u64, width);
    Some(divisor.clone().eq(zero).not())
}

/// Compute the "no signed overflow" condition for signed div/rem.
///
/// Returns `!(lhs == INT_MIN && rhs == -1)`, i.e., `lhs != INT_MIN || rhs != -1`.
/// INT_MIN / -1 overflows because |INT_MIN| > INT_MAX.
/// Mirrors `statement::arithmetic_checks::overflow_check` for Div/Rem.
/// Part of #3363.
pub(in crate::codegen_ay::chc) fn signed_div_overflow_condition(
    lhs: &Expr,
    rhs: &Expr,
) -> Option<Expr> {
    let width = lhs.sort().bitvec_width()?;
    // INT_MIN: 1 followed by (width-1) zeros
    let int_min = Expr::bitvec_const(1u128 << (width - 1), width);
    // -1: all ones
    let neg_one = Expr::bitvec_const(!0u128, width);
    // no_overflow = (lhs != INT_MIN) || (rhs != -1)
    let lhs_not_min = lhs.clone().eq(int_min).not();
    let rhs_not_neg_one = rhs.clone().eq(neg_one).not();
    Some(lhs_not_min.or(rhs_not_neg_one))
}

/// Compute the "no negation overflow" condition for signed UnOp::Neg.
///
/// Returns `bvneg_no_overflow(operand)`, which is `true` when negation does
/// NOT overflow. Only signed INT_MIN produces overflow (e.g., -(-128i8)).
/// Mirrors `statement::arithmetic_checks::emit_neg_overflow_check`.
/// Part of #3363 Phase 2+.
pub(super) fn signed_neg_overflow_condition(operand: &Expr) -> Option<Expr> {
    let _width = operand.sort().bitvec_width()?;
    Some(operand.clone().bvneg_no_overflow())
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Compute the NaN-generation obligation for a symbolic float value binop
    /// (Kani `--nan-check` parity).
    ///
    /// The congruent table lane (float_binop_table.rs) leaves the result term
    /// unconstrained, so the solver cannot itself rule NaN out — the decision
    /// is made here, at compile time, and fails CLOSED: the obligation is
    /// emitted unless both operands are provably non-NaN sources. Before the
    /// table lane existed, every such binop was FAILED via the `chc_fallback`
    /// demotion; the obligation keeps NaN-generating programs (e.g.
    /// `INFINITY + NEG_INFINITY`) FAILED while letting finite-operand proofs
    /// stand.
    ///
    /// Returns the condition that must HOLD (result is not NaN); the caller
    /// pushes it to `safety_checks` so the rule generator emits the
    /// per-property error rule on its negation, like every other UB check.
    ///
    /// `None` means no obligation: constant-folded results (pre-existing
    /// behavior kept), values produced by a different lane (e.g. the
    /// float-assertion Sub bypass), or a discharged obligation.
    pub(in crate::codegen_ay::chc) fn float_nan_check_condition(
        &self,
        op: BinOp,
        lhs_op: &'body Operand,
        rhs_op: &'body Operand,
        le: &Expr,
        re: &Expr,
        rhs_expr: &Expr,
        bb_idx: usize,
    ) -> Option<Expr> {
        if !is_float_arithmetic_op(op) {
            return None;
        }
        let width = le.sort().bitvec_width()?;
        // Both operands concrete → the constant-fold lane produced the value.
        // Scope the obligation to the symbolic congruent lane.
        if float_const_value(le).is_some() && float_const_value(re).is_some() {
            return None;
        }
        // Scope strictly to values produced by the congruent table lane:
        // recompute the term (deterministic helper — identical inputs yield
        // an identical Expr) and require it to be what translation stored.
        let term = self.float_binop_chc_term(op, le.clone(), re.clone(), width)?;
        if term != *rhs_expr {
            return None;
        }
        // Non-NaN-source discharge: finite float constant, or covered by the
        // dominating `assume(is_finite(..))` matcher shared with the
        // fast-math operand checks. Cheap constant test first.
        let lhs_non_nan =
            float_expr_is_finite_const(le) || has_dominating_finite_assume(self, bb_idx, lhs_op);
        let rhs_non_nan =
            float_expr_is_finite_const(re) || has_dominating_finite_assume(self, bb_idx, rhs_op);
        if float_nan_obligation_discharged(
            op,
            lhs_non_nan,
            rhs_non_nan,
            float_expr_is_nonzero_finite_const(re),
        ) {
            return None;
        }
        float_is_not_nan_condition(&term, width)
    }
}

/// Decide whether the NaN-generation obligation is discharged for a float
/// binop with the given operand facts. Pure — the syntactic decision core of
/// `float_nan_check_condition` (Kani `--nan-check` parity).
pub(in crate::codegen_ay::chc) fn float_nan_obligation_discharged(
    op: BinOp,
    lhs_non_nan_source: bool,
    rhs_non_nan_source: bool,
    divisor_nonzero_finite_const: bool,
) -> bool {
    if !(lhs_non_nan_source && rhs_non_nan_source) {
        return false;
    }
    match op {
        // finite ⊕ finite can overflow to ±inf but can NEVER produce NaN, so
        // finite operands fully discharge Add/Sub/Mul — non-overflow is NOT
        // required. (NaN needs a NaN operand, ∞ − ∞, or 0 · ∞.)
        BinOp::Add
        | BinOp::AddUnchecked
        | BinOp::Sub
        | BinOp::SubUnchecked
        | BinOp::Mul
        | BinOp::MulUnchecked => true,
        // Div/Rem also produce NaN from 0/0 (resp. x % 0) — finite operands
        // do NOT exclude a zero divisor. inf/inf (resp. inf % y) is already
        // excluded by operand finiteness. Fail closed unless the divisor is
        // a nonzero finite constant.
        BinOp::Div | BinOp::Rem => divisor_nonzero_finite_const,
        // Non-arithmetic ops never reach here (is_float_arithmetic_op gate).
        _ => false,
    }
}

/// The "result is not NaN" condition: NaN ⇔ exponent all-ones ∧ mantissa ≠ 0.
pub(in crate::codegen_ay::chc) fn float_is_not_nan_condition(
    value: &Expr,
    width: u32,
) -> Option<Expr> {
    let (exp_hi, exp_lo, exp_all_ones) = match width {
        32 => (30u32, 23u32, 0xFFu64),
        64 => (62u32, 52u32, 0x7FFu64),
        _ => return None,
    };
    let exp_width = exp_hi - exp_lo + 1;
    let exp = value.clone().extract(exp_hi, exp_lo);
    let mantissa = value.clone().extract(exp_lo - 1, 0);
    let exp_is_all_ones = exp.eq(Expr::bitvec_const(exp_all_ones, exp_width));
    let mantissa_nonzero = mantissa.eq(Expr::bitvec_const(0u64, exp_lo)).not();
    Some(exp_is_all_ones.and(mantissa_nonzero).not())
}

/// Decode an f32/f64 constant expression (NaN payloads decode as NaN; the
/// f32→f64 widening is exact for the finite/zero classification used here).
fn float_const_value(expr: &Expr) -> Option<f64> {
    let ExprValue::BitVecConst { value, width } = expr.value() else {
        return None;
    };
    let bits = u64::try_from(value).ok()?;
    match width {
        32 => Some(f32::from_bits(bits as u32) as f64),
        64 => Some(f64::from_bits(bits)),
        _ => None,
    }
}

/// True when `expr` is a finite f32/f64 constant (a non-NaN source).
pub(in crate::codegen_ay::chc) fn float_expr_is_finite_const(expr: &Expr) -> bool {
    float_const_value(expr).is_some_and(|f| f.is_finite())
}

/// True when `expr` is a finite, nonzero f32/f64 constant. IEEE equality
/// makes `f != 0.0` reject both +0.0 and -0.0, as required for the Div/Rem
/// zero-divisor discharge.
pub(in crate::codegen_ay::chc) fn float_expr_is_nonzero_finite_const(expr: &Expr) -> bool {
    float_const_value(expr).is_some_and(|f| f.is_finite() && f != 0.0)
}

#[cfg(test)]
mod nan_check_tests {
    use super::*;

    fn f32_const(f: f32) -> Expr {
        Expr::bitvec_const(f.to_bits() as u64, 32)
    }

    #[test]
    fn test_nan_discharge_add_sub_mul_with_finite_operands() {
        // finite ⊕ finite may overflow to ±inf but never yields NaN.
        for op in [BinOp::Add, BinOp::Sub, BinOp::Mul, BinOp::MulUnchecked] {
            assert!(float_nan_obligation_discharged(op, true, true, false));
        }
    }

    #[test]
    fn test_nan_discharge_requires_both_operands_non_nan() {
        for op in [BinOp::Add, BinOp::Sub, BinOp::Mul, BinOp::Div, BinOp::Rem] {
            assert!(!float_nan_obligation_discharged(op, false, true, true));
            assert!(!float_nan_obligation_discharged(op, true, false, true));
        }
    }

    #[test]
    fn test_nan_discharge_div_rem_needs_nonzero_const_divisor() {
        // finite/finite still allows 0/0 → NaN; finite operands alone do NOT
        // discharge Div/Rem (fail closed).
        assert!(!float_nan_obligation_discharged(BinOp::Div, true, true, false));
        assert!(!float_nan_obligation_discharged(BinOp::Rem, true, true, false));
        assert!(float_nan_obligation_discharged(BinOp::Div, true, true, true));
        assert!(float_nan_obligation_discharged(BinOp::Rem, true, true, true));
    }

    #[test]
    fn test_float_const_classification() {
        assert!(float_expr_is_finite_const(&f32_const(1.5)));
        assert!(float_expr_is_finite_const(&f32_const(f32::MAX)));
        assert!(!float_expr_is_finite_const(&f32_const(f32::INFINITY)));
        assert!(!float_expr_is_finite_const(&f32_const(f32::NEG_INFINITY)));
        assert!(!float_expr_is_finite_const(&f32_const(f32::NAN)));
        // Symbolic operands are never constant sources.
        assert!(!float_expr_is_finite_const(&Expr::var("x", ay_bindings::Sort::bitvec(32))));
    }

    #[test]
    fn test_float_nonzero_const_rejects_both_zero_patterns() {
        assert!(float_expr_is_nonzero_finite_const(&f32_const(2.0)));
        assert!(!float_expr_is_nonzero_finite_const(&f32_const(0.0)));
        assert!(!float_expr_is_nonzero_finite_const(&f32_const(-0.0)));
        assert!(!float_expr_is_nonzero_finite_const(&f32_const(f32::INFINITY)));
    }

    #[test]
    fn test_not_nan_condition_folds_on_constants() {
        use ay_bindings::ExprValue;
        // NaN constant → condition must be definitely violated (or at least
        // not fold to true); finite constant → must not be definitely false.
        let on_nan = float_is_not_nan_condition(&f32_const(f32::NAN), 32).unwrap();
        assert!(!matches!(on_nan.value(), ExprValue::BoolConst(true)));
        let on_one = float_is_not_nan_condition(&f32_const(1.0), 32).unwrap();
        assert!(!matches!(on_one.value(), ExprValue::BoolConst(false)));
        // Unsupported widths fail closed at the caller (no condition built).
        assert!(float_is_not_nan_condition(&f32_const(1.0), 16).is_none());
    }
}
