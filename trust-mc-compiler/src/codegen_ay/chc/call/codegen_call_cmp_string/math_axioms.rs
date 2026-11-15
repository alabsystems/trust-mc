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
///
/// `minnum` / `maxnum` are NOT functions of their arguments and are not encoded here: see
/// [`minmax_num_result_constraint`].
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

    None
}

/// Which of `minnum` (`true`) / `maxnum` (`false`) `intrinsic_name` names, at `f32` or `f64`.
///
/// On Trust these are `minimum_number_nsz_f*` / `maximum_number_nsz_f*`, which reach here
/// under their nightly spelling (`intrinsics::nightly_float_intrinsic_name`).
pub(in crate::codegen_ay::chc) fn minmax_num_kind(intrinsic_name: &str) -> Option<bool> {
    if intrinsic_name.ends_with("minnumf32") || intrinsic_name.ends_with("minnumf64") {
        Some(true)
    } else if intrinsic_name.ends_with("maxnumf32") || intrinsic_name.ends_with("maxnumf64") {
        Some(false)
    } else {
        None
    }
}

/// The relation `dest ∈ minnum(x, y)` (`is_min`) or `dest ∈ maxnum(x, y)` over IEEE 754
/// bitvectors of `width` bits. `None` when a sort is not a `width`-bit bitvector.
///
/// The Rust contract of `f32::min` / `f32::max` and of the intrinsics under them (nightly
/// `minnumf*` / `maxnumf*`, Trust `minimum_number_nsz_f*` / `maximum_number_nsz_f*`) is a
/// relation, not a function:
///
/// - exactly one argument NaN: the other argument, bit for bit;
/// - both NaN: a NaN, whose sign and payload Rust leaves unspecified;
/// - arguments that compare equal: EITHER argument ("If the inputs compare equal (such as
///   for the case of +0.0 and -0.0), either input may be returned non-deterministically").
///   Equal non-zero values have identical bits, so only zeros of opposite sign differ;
/// - otherwise the smaller (larger) argument.
///
/// Measured on arm64 with trust 8571 and nightly-2025-12-03: at run time `min(+0, -0)` is
/// `-0`, while const evaluation of the same expression in the same toolchain is `+0`. The
/// previous encoding returned `y` for every equal pair, so CHC proved sign properties that
/// fail in one of the two. The constraint below admits both results and nothing else.
pub(in crate::codegen_ay::chc) fn minmax_num_result_constraint(
    is_min: bool,
    arg0: &Expr,
    arg1: &Expr,
    dest: &Expr,
    width: u32,
) -> Option<Expr> {
    if arg0.sort().bitvec_width() != Some(width)
        || arg1.sort().bitvec_width() != Some(width)
        || dest.sort().bitvec_width() != Some(width)
    {
        return None;
    }
    let magnitude_mask = match width {
        32 => Expr::bitvec_const(0x7FFF_FFFFu64, 32),
        64 => Expr::bitvec_const(0x7FFF_FFFF_FFFF_FFFFu64, 64),
        _ => return None,
    };
    let zero = Expr::bitvec_const(0u64, width);
    let x_nan = build_float_predicate_expr(arg0, FloatPredicateKind::Nan)?;
    let y_nan = build_float_predicate_expr(arg1, FloatPredicateKind::Nan)?;
    let dest_nan = build_float_predicate_expr(dest, FloatPredicateKind::Nan)?;
    let x_zero = arg0.clone().bvand(magnitude_mask.clone()).eq(zero.clone());
    let y_zero = arg1.clone().bvand(magnitude_mask).eq(zero);
    // Strict IEEE comparison: x is the result only when it is strictly smaller (larger);
    // NaN operands are handled before this is consulted.
    let x_wins =
        if is_min { bv_float_lt(arg0, arg1, width) } else { bv_float_gt(arg0, arg1, width) };
    let ordered = Expr::ite(x_wins, arg0.clone(), arg1.clone());
    let one_nan =
        Expr::ite(x_nan.clone(), arg1.clone(), Expr::ite(y_nan.clone(), arg0.clone(), ordered));
    let either_argument = dest.clone().eq(arg0.clone()).or(dest.clone().eq(arg1.clone()));
    Some(Expr::ite(
        x_nan.and(y_nan),
        dest_nan,
        Expr::ite(x_zero.and(y_zero), either_argument, dest.clone().eq(one_nan)),
    ))
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

    /// minnum/maxnum are relations: the exact functional encoding no longer claims them.
    #[test]
    fn test_minmax_num_is_not_a_functional_encoding() {
        let x = Expr::bitvec_const(POS_ZERO_64, 64);
        let y = Expr::bitvec_const(NEG_ZERO_64, 64);
        for name in ["minnumf64", "maxnumf64"] {
            assert!(try_exact_binary_encoding(name, &x, &y, 64).is_none(), "{name}");
        }
        assert_eq!(minmax_num_kind("std::intrinsics::minnumf32"), Some(true));
        assert_eq!(minmax_num_kind("std::intrinsics::maxnumf64"), Some(false));
        assert_eq!(minmax_num_kind("std::intrinsics::copysignf64"), None);
    }

    /// The relation is built at both widths and refuses a mismatched destination sort.
    #[test]
    fn test_minmax_num_result_constraint_sorts() {
        for (width, pz, nz) in [(32u32, POS_ZERO_32, NEG_ZERO_32), (64, POS_ZERO_64, NEG_ZERO_64)] {
            let x = Expr::bitvec_const(pz, width);
            let y = Expr::bitvec_const(nz, width);
            let dest = Expr::var("dest", ay_bindings::Sort::bitvec(width));
            for is_min in [true, false] {
                let c =
                    minmax_num_result_constraint(is_min, &x, &y, &dest, width).expect("constraint");
                assert!(c.sort().is_bool(), "width {width} is_min {is_min}");
            }
            let narrow = Expr::var("narrow", ay_bindings::Sort::bitvec(16));
            assert!(minmax_num_result_constraint(true, &x, &y, &narrow, width).is_none());
        }
    }
}
