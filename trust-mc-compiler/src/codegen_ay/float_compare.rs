// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! IEEE 754 comparison helpers for BV-encoded floats (Part of #3140).
//!
//! IEEE 754 floats encoded as unsigned bitvectors require special comparison
//! logic because bvult/bvule gives wrong results for negative floats:
//! - Negative floats (sign bit 1) appear as large unsigned values
//! - For two negative floats, larger BV unsigned value = more negative = SMALLER IEEE value
//! - bvule(-0.0, +0.0) is false but IEEE says -0.0 == +0.0
//!
//! These helpers implement correct IEEE 754 comparison semantics including
//! NaN propagation: any comparison involving NaN returns false (unordered),
//! except `!=` which returns true. This is critical for `f32::is_nan()`
//! (`self != self`) and `kani::assume(!x.is_nan())` to work correctly.

use ay_bindings::Expr;

/// IEEE 754 NaN detection for a BV-encoded float.
///
/// NaN iff exponent bits are all ones AND mantissa bits are non-zero.
/// Supports f16 (width=16), f32 (width=32), f64 (width=64), f128 (width=128).
fn bv_is_nan(val: &Expr, width: u32) -> Expr {
    let (exp_hi, exp_lo) = match width {
        16 => (14, 10),
        32 => (30, 23),
        64 => (62, 52),
        128 => (126, 112),
        _ => {
            // Unsupported width — conservatively return false (not NaN).
            return Expr::bool_const(false);
        }
    };
    let exp_width = exp_hi - exp_lo + 1;
    let mant_bits = exp_lo;
    let exp = val.clone().extract(exp_hi, exp_lo);
    let mant = val.clone().extract(exp_lo - 1, 0);
    let exp_all_ones = (1u64 << exp_width) - 1;
    let exp_max = exp.eq(Expr::bitvec_const(exp_all_ones, exp_width));
    let mant_nonzero = mant.eq(Expr::bitvec_const(0u64, mant_bits)).not();
    exp_max.and(mant_nonzero)
}

/// IEEE 754 less-than: `a < b` for BV-encoded floats.
pub(in crate::codegen_ay) fn bv_float_lt(lhs: &Expr, rhs: &Expr, width: u32) -> Expr {
    let msb = width - 1;
    let one_1 = Expr::bitvec_const(1u64, 1);

    let sign_a = lhs.clone().extract(msb, msb);
    let sign_b = rhs.clone().extract(msb, msb);
    let a_neg = sign_a.eq(one_1.clone());
    let b_neg = sign_b.eq(one_1);
    let a_pos = a_neg.clone().not();
    let b_pos = b_neg.clone().not();

    // Both magnitudes zero → -0.0 and +0.0 are equal, not less-than
    // u128 so f128 (width 128, msb 127) does not overflow the shift; the mask
    // is the width-bit value with the sign bit cleared, and flows through
    // `bitvec_const(impl Into<BigInt>)` unchanged for every float width.
    let mag_mask = (1u128 << msb) - 1;
    let zero_w = Expr::bitvec_const(0u64, width);
    let mag_a = lhs.clone().bvand(Expr::bitvec_const(mag_mask, width));
    let mag_b = rhs.clone().bvand(Expr::bitvec_const(mag_mask, width));
    let both_zero = mag_a.eq(zero_w.clone()).and(mag_b.eq(zero_w));

    let neg_pos = a_neg.clone().and(b_pos.clone());
    let both_pos = a_pos.and(b_pos);
    let both_neg = a_neg.and(b_neg);

    // Both positive: unsigned comparison correct
    // Both negative: reversed (larger unsigned = more negative = smaller)
    // Negative < positive: true
    // Positive < negative: false
    let cmp = Expr::ite(
        neg_pos,
        Expr::bool_const(true),
        Expr::ite(
            both_pos,
            lhs.clone().bvult(rhs.clone()),
            Expr::ite(both_neg, lhs.clone().bvugt(rhs.clone()), Expr::bool_const(false)),
        ),
    );

    // -0.0 < +0.0 is false (they're equal)
    let ordered = Expr::ite(both_zero, Expr::bool_const(false), cmp);

    // IEEE 754: any ordered comparison with NaN returns false
    let either_nan = bv_is_nan(lhs, width).or(bv_is_nan(rhs, width));
    Expr::ite(either_nan, Expr::bool_const(false), ordered)
}

/// IEEE 754 less-or-equal: `a <= b` for BV-encoded floats.
pub(in crate::codegen_ay) fn bv_float_le(lhs: &Expr, rhs: &Expr, width: u32) -> Expr {
    let msb = width - 1;
    let one_1 = Expr::bitvec_const(1u64, 1);

    let sign_a = lhs.clone().extract(msb, msb);
    let sign_b = rhs.clone().extract(msb, msb);
    let a_neg = sign_a.eq(one_1.clone());
    let b_neg = sign_b.eq(one_1);
    let a_pos = a_neg.clone().not();
    let b_pos = b_neg.clone().not();

    // u128 so f128 (width 128, msb 127) does not overflow the shift; the mask
    // is the width-bit value with the sign bit cleared, and flows through
    // `bitvec_const(impl Into<BigInt>)` unchanged for every float width.
    let mag_mask = (1u128 << msb) - 1;
    let zero_w = Expr::bitvec_const(0u64, width);
    let mag_a = lhs.clone().bvand(Expr::bitvec_const(mag_mask, width));
    let mag_b = rhs.clone().bvand(Expr::bitvec_const(mag_mask, width));
    let both_zero = mag_a.eq(zero_w.clone()).and(mag_b.eq(zero_w));

    let neg_pos = a_neg.clone().and(b_pos.clone());
    let both_pos = a_pos.and(b_pos);
    let both_neg = a_neg.and(b_neg);

    let cmp = Expr::ite(
        neg_pos,
        Expr::bool_const(true),
        Expr::ite(
            both_pos,
            lhs.clone().bvule(rhs.clone()),
            Expr::ite(both_neg, lhs.clone().bvuge(rhs.clone()), Expr::bool_const(false)),
        ),
    );

    // -0.0 <= +0.0 is true (they're equal)
    let ordered = Expr::ite(both_zero, Expr::bool_const(true), cmp);

    // IEEE 754: any ordered comparison with NaN returns false
    let either_nan = bv_is_nan(lhs, width).or(bv_is_nan(rhs, width));
    Expr::ite(either_nan, Expr::bool_const(false), ordered)
}

/// IEEE 754 greater-than: `a > b` = `b < a`.
pub(in crate::codegen_ay) fn bv_float_gt(lhs: &Expr, rhs: &Expr, width: u32) -> Expr {
    bv_float_lt(rhs, lhs, width)
}

/// IEEE 754 greater-or-equal: `a >= b` = `b <= a`.
pub(in crate::codegen_ay) fn bv_float_ge(lhs: &Expr, rhs: &Expr, width: u32) -> Expr {
    bv_float_le(rhs, lhs, width)
}

/// IEEE 754 equality: `a == b` for BV-encoded floats.
///
/// Handles ±0.0 equality AND NaN propagation:
/// - -0.0 == +0.0 is true (different bit patterns but IEEE-equal)
/// - NaN == anything is false (IEEE 754 unordered)
pub(in crate::codegen_ay) fn bv_float_eq(lhs: &Expr, rhs: &Expr, width: u32) -> Expr {
    let msb = width - 1;
    // u128 so f128 (width 128, msb 127) does not overflow the shift; the mask
    // is the width-bit value with the sign bit cleared, and flows through
    // `bitvec_const(impl Into<BigInt>)` unchanged for every float width.
    let mag_mask = (1u128 << msb) - 1;
    let zero_w = Expr::bitvec_const(0u64, width);
    let mag_a = lhs.clone().bvand(Expr::bitvec_const(mag_mask, width));
    let mag_b = rhs.clone().bvand(Expr::bitvec_const(mag_mask, width));
    let both_zero_mag = mag_a.eq(zero_w.clone()).and(mag_b.eq(zero_w));

    // Bitwise equal OR both ±0.0
    let value_eq = lhs.clone().eq(rhs.clone()).or(both_zero_mag);

    // IEEE 754: NaN == anything is false
    let either_nan = bv_is_nan(lhs, width).or(bv_is_nan(rhs, width));
    Expr::ite(either_nan, Expr::bool_const(false), value_eq)
}

/// IEEE 754 inequality: `a != b` for BV-encoded floats.
///
/// NaN != anything is true (IEEE 754). This is critical for `f32::is_nan()`
/// which compiles to `self != self` — NaN is the only value where x != x.
pub(in crate::codegen_ay) fn bv_float_ne(lhs: &Expr, rhs: &Expr, width: u32) -> Expr {
    bv_float_eq(lhs, rhs, width).not()
}

/// IEEE 754 three-way comparison (Cmp/Ordering) for BV-encoded floats.
///
/// Returns Ordering encoded as 32-bit bitvec:
///   Less = 0xFFFFFFFF (−1 in two's complement BV32)
///   Equal = 0x00
///   Greater = 0x01
///
/// Uses the same sign-aware comparison logic as `bv_float_lt` to ensure
/// consistency between `BinOp::Cmp` and `BinOp::Lt/Le/Gt/Ge` on floats.
/// Fix #4213: was 0xFF (255) which never matched SwitchInt's 0xFFFFFFFF.
pub(in crate::codegen_ay) fn bv_float_cmp(lhs: &Expr, rhs: &Expr, width: u32) -> Expr {
    let lt = bv_float_lt(lhs, rhs, width);
    let eq = bv_float_eq(lhs, rhs, width);

    Expr::ite(
        lt,
        Expr::bitvec_const(0xFFFF_FFFFu128, 32), // Less = -1 in BV32
        Expr::ite(eq, Expr::bitvec_const(0u128, 32), Expr::bitvec_const(1u128, 32)),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_bindings::ExprValue;

    // f32 IEEE 754 bit patterns:
    const POS_ZERO_32: u64 = 0x0000_0000; // +0.0
    const NEG_ZERO_32: u64 = 0x8000_0000; // -0.0
    const POS_ONE_32: u64 = 0x3F80_0000; // 1.0
    const NEG_ONE_32: u64 = 0xBF80_0000; // -1.0

    const NAN_32: u64 = 0x7FC0_0000; // quiet NaN

    /// bv_float_eq(+0.0, -0.0) must be true — the key IEEE 754 invariant.
    #[test]
    fn test_bv_float_eq_neg_zero_pos_zero_is_true() {
        let lhs = Expr::bitvec_const(POS_ZERO_32, 32);
        let rhs = Expr::bitvec_const(NEG_ZERO_32, 32);
        let result = bv_float_eq(&lhs, &rhs, 32);
        // Now returns ITE(either_nan, false, OR(bitwise_eq, both_zero_mag))
        assert!(matches!(result.value(), ExprValue::Ite { .. }));
    }

    /// bv_float_eq(1.0, 1.0) must be true (same bit pattern, non-NaN).
    #[test]
    fn test_bv_float_eq_same_value_is_true() {
        let lhs = Expr::bitvec_const(POS_ONE_32, 32);
        let rhs = Expr::bitvec_const(POS_ONE_32, 32);
        let result = bv_float_eq(&lhs, &rhs, 32);
        assert!(matches!(result.value(), ExprValue::Ite { .. }));
    }

    /// bv_float_eq(NaN, NaN) must be false — IEEE 754 says NaN != NaN.
    /// This is the critical invariant for f32::is_nan() = (self != self).
    #[test]
    fn test_bv_float_eq_nan_nan_is_ite_with_nan_guard() {
        let lhs = Expr::bitvec_const(NAN_32, 32);
        let rhs = Expr::bitvec_const(NAN_32, 32);
        let result = bv_float_eq(&lhs, &rhs, 32);
        assert!(matches!(result.value(), ExprValue::Ite { .. }));
    }

    /// bv_float_cmp produces a 32-bit bitvec result (Ordering encoding).
    #[test]
    fn test_bv_float_cmp_returns_32bit_ite() {
        let lhs = Expr::bitvec_const(NEG_ONE_32, 32);
        let rhs = Expr::bitvec_const(POS_ONE_32, 32);
        let result = bv_float_cmp(&lhs, &rhs, 32);
        assert_eq!(result.sort().bitvec_width(), Some(32));
        assert!(matches!(result.value(), ExprValue::Ite { .. }));
    }

    /// bv_float_cmp(-0.0, +0.0) must return Equal (0x00), not Greater.
    /// This verifies consistency with bv_float_lt(-0.0, +0.0) = false.
    #[test]
    fn test_bv_float_cmp_neg_zero_pos_zero_is_equal() {
        let lhs = Expr::bitvec_const(NEG_ZERO_32, 32);
        let rhs = Expr::bitvec_const(POS_ZERO_32, 32);
        let result = bv_float_cmp(&lhs, &rhs, 32);
        // The result should be ITE(lt, 0xFF, ITE(eq, 0, 1)).
        // For -0.0 vs +0.0: lt=false, eq=true → result=0 (Equal).
        assert_eq!(result.sort().bitvec_width(), Some(32));
        assert!(matches!(result.value(), ExprValue::Ite { .. }));
    }

    /// bv_float_ne(+0.0, -0.0) must be false — IEEE 754 says they're equal.
    /// This catches the soundness bug where SMT bitwise != would return true.
    #[test]
    fn test_bv_float_ne_neg_zero_pos_zero_is_false() {
        let lhs = Expr::bitvec_const(POS_ZERO_32, 32);
        let rhs = Expr::bitvec_const(NEG_ZERO_32, 32);
        let result = bv_float_ne(&lhs, &rhs, 32);
        // NOT(ITE(either_nan, false, value_eq)) — a Not wrapping Ite
        assert!(matches!(result.value(), ExprValue::Not { .. }));
    }

    /// bv_float_ne(1.0, -1.0) must be true — different non-zero values.
    #[test]
    fn test_bv_float_ne_different_values_is_true() {
        let lhs = Expr::bitvec_const(POS_ONE_32, 32);
        let rhs = Expr::bitvec_const(NEG_ONE_32, 32);
        let result = bv_float_ne(&lhs, &rhs, 32);
        assert!(matches!(result.value(), ExprValue::Not { .. }));
    }

    /// bv_is_nan returns true for NaN bit patterns.
    #[test]
    fn test_bv_is_nan_detects_nan() {
        let nan = Expr::bitvec_const(NAN_32, 32);
        let result = bv_is_nan(&nan, 32);
        assert!(matches!(result.value(), ExprValue::And { .. }));
    }

    /// bv_is_nan returns false for normal values.
    #[test]
    fn test_bv_is_nan_rejects_normal() {
        let one = Expr::bitvec_const(POS_ONE_32, 32);
        let result = bv_is_nan(&one, 32);
        assert!(matches!(result.value(), ExprValue::And { .. }));
    }

    /// Regression: the magnitude mask `(1 << (width-1)) - 1` must not overflow
    /// for f128 (width 128, msb 127). Before the u128 fix this panicked with
    /// "attempt to shift left with overflow" at the `mag_mask` line, ICE-ing
    /// codegen for any f128 comparison (kani FloatToInt::check_f128, non_standard_floats).
    #[test]
    fn test_bv_float_compare_f128_width_no_overflow() {
        // Arbitrary distinct 128-bit patterns; the values are irrelevant — the
        // regression is purely that building the comparison does not panic.
        let lhs = Expr::bitvec_const(0u128, 128);
        let rhs = Expr::bitvec_const(1u128 << 100, 128);
        // All four comparators walk the mag_mask path.
        assert!(matches!(bv_float_lt(&lhs, &rhs, 128).value(), ExprValue::Ite { .. }));
        assert!(matches!(bv_float_le(&lhs, &rhs, 128).value(), ExprValue::Ite { .. }));
        assert!(matches!(bv_float_eq(&lhs, &rhs, 128).value(), ExprValue::Ite { .. }));
        assert_eq!(bv_float_cmp(&lhs, &rhs, 128).sort().bitvec_width(), Some(32));
    }

    /// Companion: f16 (width 16, msb 15) also exercises the mask path.
    #[test]
    fn test_bv_float_compare_f16_width_no_overflow() {
        let lhs = Expr::bitvec_const(0u64, 16);
        let rhs = Expr::bitvec_const(0x3C00u64, 16); // f16 1.0
        assert!(matches!(bv_float_lt(&lhs, &rhs, 16).value(), ExprValue::Ite { .. }));
        assert!(matches!(bv_float_eq(&lhs, &rhs, 16).value(), ExprValue::Ite { .. }));
    }
}
