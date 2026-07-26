// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! FP exact encoding for symbolic float arguments.
//!
//! Part of #3140 (concrete BV fabs/copysign/minnum/maxnum),
//! Part of #3323 (exact BV encodings),
//! Part of #3750 (pure BV rounding via IEEE 754 mantissa masking).
//!
//! When math intrinsics receive symbolic arguments that cannot be
//! constant-folded, this module provides exact encodings:
//! - fabs, copysign, minnum, maxnum: BV-level bit manipulation
//! - floor, ceil, trunc, round, round_ties_even: pure BV mantissa masking
//!   (no FP rounding modes — Z3 CHC compatible)
//!
//! Floats are encoded as unsigned bitvectors (BV32/BV64).

use ay_bindings::Expr;

use super::float_predicates::{FloatPredicateKind, build_float_predicate_expr};
use crate::codegen_ay::float_compare::{bv_float_gt, bv_float_lt};

// ===== Exact BV encodings (precise, not over-approximations) =====

/// Try to compute an exact result for a unary math intrinsic.
///
/// Returns `Some(exact_result_expr)` when the intrinsic has a precise
/// definition. The caller should constrain `dest = exact_result_expr`.
///
/// Currently handles:
/// - `fabs{f32,f64}(x)` — clear sign bit: `x & 0x7FFF...`
/// - `floor{f32,f64}(x)` — pure BV mantissa masking + conditional increment
/// - `ceil{f32,f64}(x)` — pure BV mantissa masking + conditional increment
/// - `trunc{f32,f64}(x)` — pure BV mantissa masking (clear fractional bits)
/// - `round{f32,f64}(x)` — pure BV highest-frac-bit check + increment
/// - `round_ties_even_{f32,f64}(x)` — pure BV frac check + even tie-break
pub(in crate::codegen_ay::chc) fn try_exact_unary_encoding(
    intrinsic_name: &str,
    input: &Expr,
    width: u32,
) -> Option<Expr> {
    // fabs: IEEE 754 absolute value is defined as clearing the sign bit.
    if intrinsic_name.ends_with("fabsf32") || intrinsic_name.ends_with("fabsf64") {
        let sign_mask = match width {
            32 => Expr::bitvec_const(0x7FFF_FFFFu64, 32),
            64 => Expr::bitvec_const(0x7FFF_FFFF_FFFF_FFFFu64, 64),
            _ => return None,
        };
        return Some(input.clone().bvand(sign_mask));
    }

    // Part of #3750: floor/ceil/trunc/round via pure BV bit manipulation.
    // Replaces FP theory (fp.roundToIntegral) which emits rounding-mode constants
    // that Z3's CHC parser rejects. Pure BV encoding is exact for rounding-to-integral
    // and uses only BV ops (extract, concat, bvand, bvshl, ite).
    use super::float_rounding;

    if intrinsic_name.ends_with("floorf32") || intrinsic_name.ends_with("floorf64") {
        if let Some(result) = float_rounding::build_float_floor_bv(input) {
            return Some(result);
        }
    }

    if intrinsic_name.ends_with("ceilf32") || intrinsic_name.ends_with("ceilf64") {
        if let Some(result) = float_rounding::build_float_ceil_bv(input) {
            return Some(result);
        }
    }

    if intrinsic_name.ends_with("truncf32") || intrinsic_name.ends_with("truncf64") {
        if let Some(result) = float_rounding::build_float_trunc_bv(input) {
            return Some(result);
        }
    }

    if intrinsic_name.ends_with("roundf32") || intrinsic_name.ends_with("roundf64") {
        if let Some(result) = float_rounding::build_float_round_bv(input) {
            return Some(result);
        }
    }

    if intrinsic_name.ends_with("round_ties_even_f32")
        || intrinsic_name.ends_with("round_ties_even_f64")
    {
        if let Some(result) = float_rounding::build_float_round_ties_even_bv(input) {
            return Some(result);
        }
    }

    None
}

/// Try to compute an exact BV result for a binary math intrinsic.
///
/// Currently handles:
/// - `copysign{f32,f64}(mag, sig)` — combine magnitude bits of `mag`
///   with sign bit of `sig`: `(mag & 0x7FFF...) | (sig & 0x8000...)`
/// - `minnum{f32,f64}(x, y)` — IEEE 754 minimum with NaN propagation
/// - `maxnum{f32,f64}(x, y)` — IEEE 754 maximum with NaN propagation
pub(in crate::codegen_ay::chc) fn try_exact_binary_encoding(
    intrinsic_name: &str,
    arg0: &Expr,
    arg1: &Expr,
    width: u32,
) -> Option<Expr> {
    if intrinsic_name.ends_with("copysignf32") || intrinsic_name.ends_with("copysignf64") {
        let (mantissa_mask, sign_bit_mask) = match width {
            32 => (Expr::bitvec_const(0x7FFF_FFFFu64, 32), Expr::bitvec_const(0x8000_0000u64, 32)),
            64 => (
                Expr::bitvec_const(0x7FFF_FFFF_FFFF_FFFFu64, 64),
                Expr::bitvec_const(0x8000_0000_0000_0000u64, 64),
            ),
            _ => return None,
        };
        let mag_bits = arg0.clone().bvand(mantissa_mask);
        let sig_sign = arg1.clone().bvand(sign_bit_mask);
        return Some(mag_bits.bvor(sig_sign));
    }

    // minnum/maxnum: IEEE 754 minimum/maximum with NaN propagation.
    //
    // Part of #3798: use STRICT comparison (bv_float_gt for maxnum, bv_float_lt
    // for minnum) instead of non-strict bv_float_le. This is critical because
    // the CHC path uses raw BV equality for float == (#3839). When x and y are
    // IEEE-equal but BV-different (±0.0), strict comparison returns false,
    // so we return arg1 (y). This matches the standard test pattern:
    //   if x > y { assert!(res == x) } else { assert!(res == y) }
    // The else branch checks BV(res) == BV(y), which requires res IS y.
    //
    // Previous encoding used bv_float_le + ±0.0 tie-breaking that tried to
    // return the IEEE-canonical zero (+0.0 for maxnum, -0.0 for minnum).
    // That was correct per IEEE 754-2008 but incompatible with BV equality:
    // maxnum(+0.0, -0.0) returned +0.0, but `+0.0 == -0.0` is false in BV.
    let is_minnum = intrinsic_name.ends_with("minnumf32") || intrinsic_name.ends_with("minnumf64");
    let is_maxnum = intrinsic_name.ends_with("maxnumf32") || intrinsic_name.ends_with("maxnumf64");
    if is_minnum || is_maxnum {
        let x_nan = build_float_predicate_expr(arg0, FloatPredicateKind::Nan)?;
        let y_nan = build_float_predicate_expr(arg1, FloatPredicateKind::Nan)?;
        // Strict comparison: x wins only when STRICTLY better than y.
        // When IEEE-equal (including ±0.0), x does NOT win → return y.
        let x_wins =
            if is_maxnum { bv_float_gt(arg0, arg1, width) } else { bv_float_lt(arg0, arg1, width) };
        let inner = Expr::ite(x_wins, arg0.clone(), arg1.clone());

        let handle_y_nan = Expr::ite(y_nan, arg0.clone(), inner);
        return Some(Expr::ite(x_nan, arg1.clone(), handle_y_nan));
    }

    None
}

#[cfg(test)]
mod tests {
    use super::*;

    // IEEE 754 f64 constants
    const POS_ZERO_64: u64 = 0x0000_0000_0000_0000;
    const NEG_ZERO_64: u64 = 0x8000_0000_0000_0000;
    // IEEE 754 f32 constants
    const POS_ZERO_32: u64 = 0x0000_0000;
    const NEG_ZERO_32: u64 = 0x8000_0000;

    /// maxnumf64(+0.0, -0.0) must produce an expression, not None.
    #[test]
    fn test_maxnumf64_returns_some() {
        let x = Expr::bitvec_const(POS_ZERO_64, 64);
        let y = Expr::bitvec_const(NEG_ZERO_64, 64);
        let result = try_exact_binary_encoding("maxnumf64", &x, &y, 64);
        assert!(result.is_some(), "maxnumf64 should produce an encoding");
        assert_eq!(result.expect("encoding exists").sort().bitvec_width(), Some(64));
    }

    /// minnumf64(-0.0, +0.0) must produce an expression, not None.
    #[test]
    fn test_minnumf64_returns_some() {
        let x = Expr::bitvec_const(NEG_ZERO_64, 64);
        let y = Expr::bitvec_const(POS_ZERO_64, 64);
        let result = try_exact_binary_encoding("minnumf64", &x, &y, 64);
        assert!(result.is_some(), "minnumf64 should produce an encoding");
        assert_eq!(result.expect("encoding exists").sort().bitvec_width(), Some(64));
    }

    /// maxnumf32(+0.0, -0.0) must produce an expression, not None.
    #[test]
    fn test_maxnumf32_returns_some() {
        let x = Expr::bitvec_const(POS_ZERO_32, 32);
        let y = Expr::bitvec_const(NEG_ZERO_32, 32);
        let result = try_exact_binary_encoding("maxnumf32", &x, &y, 32);
        assert!(result.is_some(), "maxnumf32 should produce an encoding");
        assert_eq!(result.expect("encoding exists").sort().bitvec_width(), Some(32));
    }

    /// minnumf32(-0.0, +0.0) must produce an expression, not None.
    #[test]
    fn test_minnumf32_returns_some() {
        let x = Expr::bitvec_const(NEG_ZERO_32, 32);
        let y = Expr::bitvec_const(POS_ZERO_32, 32);
        let result = try_exact_binary_encoding("minnumf32", &x, &y, 32);
        assert!(result.is_some(), "minnumf32 should produce an encoding");
        assert_eq!(result.expect("encoding exists").sort().bitvec_width(), Some(32));
    }
}
