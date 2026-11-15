// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The non-determinism in `minnum` / `maxnum`, shared by the BMC and CHC encodings.
//!
//! `f32::min` / `f32::max` (and `f64`) reach the `minnumf*` / `maxnumf*` intrinsics, which
//! Trust core spells `minimum_number_nsz_f*` / `maximum_number_nsz_f*`. Their contract is a
//! relation, not a function: arguments that compare equal may return EITHER argument ("such
//! as for the case of +0.0 and -0.0, either input may be returned non-deterministically"),
//! and two NaNs return a NaN whose sign and payload Rust does not specify. Equal non-zero
//! values have identical bits, so the only equal pair with two distinct results is a pair of
//! zeros of opposite sign.
//!
//! Measured on arm64 (trust 8571 and nightly-2025-12-03, O0 and O3): at run time
//! `min(+0, -0)` and `min(-0, +0)` are `-0` and `max` of the same pairs is `+0`, while const
//! evaluation in the same toolchains returns `min(+0, -0) = +0` and `max(-0, +0) = -0`. A
//! model that returns one fixed zero therefore proves a sign property that fails in one of the
//! two, and folding with the host's `f32::min` bakes in whatever the verifier's host does.
//!
//! A signalling NaN argument is a third case. The documented contract returns the other
//! argument for any NaN, and that is what Trust 8590 does at run time and in const evaluation
//! and what nightly-2025-12-03 does in const evaluation; but the nightly's RUN TIME `f32::min`
//! lowers to an instruction that quiets the signalling NaN instead (measured on arm64, O0 and
//! O3: `min(sNaN, 1.0)` is `0x7fc00001`). An engine built by that nightly therefore folded
//! `min(sNaN, 2.0)` to a NaN while the same engine's symbolic relation, and the Trust-built
//! engine, returned `2.0`: the two routes gave opposite clean verdicts on one harness. No fold
//! here ever calls the host's `min`/`max`: [`minmax_num_fold_f32`] decides by IEEE comparison
//! and refuses a signalling NaN, so the relation decides it, identically on both routes.

use ay_bindings::Expr;

/// Whether `minnum` / `maxnum` of these constants has more than one allowed result, so that
/// no single constant may stand for it.
pub(in crate::codegen_ay) fn minmax_num_result_is_nondeterministic_f32(a: f32, b: f32) -> bool {
    (a == 0.0 && b == 0.0 && a.to_bits() != b.to_bits()) || (a.is_nan() && b.is_nan())
}

/// See [`minmax_num_result_is_nondeterministic_f32`].
pub(in crate::codegen_ay) fn minmax_num_result_is_nondeterministic_f64(a: f64, b: f64) -> bool {
    (a == 0.0 && b == 0.0 && a.to_bits() != b.to_bits()) || (a.is_nan() && b.is_nan())
}

/// A NaN whose quiet bit is clear: the case the nightly's run time and its const evaluation
/// decide differently (module doc), so no constant may stand for `min`/`max` of it.
pub(in crate::codegen_ay) fn is_signalling_nan_f32(x: f32) -> bool {
    x.is_nan() && x.to_bits() & 0x0040_0000 == 0
}

/// See [`is_signalling_nan_f32`].
pub(in crate::codegen_ay) fn is_signalling_nan_f64(x: f64) -> bool {
    x.is_nan() && x.to_bits() & 0x0008_0000_0000_0000 == 0
}

/// The one result of `minnum` (`is_min`) / `maxnum` of two constants, when IEEE 754 and the
/// Rust contract determine it on every toolchain: one quiet NaN returns the other argument,
/// unequal values the strictly smaller (larger), identical bits themselves. `None` where more
/// than one result is allowed (opposite zeros, two NaNs) or where the toolchains' run times
/// differ (a signalling NaN); the caller then emits the relation instead of a constant.
///
/// Decided by comparison, never by the host's `f32::min` / `f32::max`: what those return for
/// a signalling NaN depends on how the verifier itself was compiled.
pub(in crate::codegen_ay) fn minmax_num_fold_f32(is_min: bool, a: f32, b: f32) -> Option<f32> {
    if minmax_num_result_is_nondeterministic_f32(a, b)
        || is_signalling_nan_f32(a)
        || is_signalling_nan_f32(b)
    {
        return None;
    }
    if a.is_nan() {
        return Some(b);
    }
    if b.is_nan() {
        return Some(a);
    }
    let a_wins = if is_min { a < b } else { a > b };
    Some(if a_wins || a.to_bits() == b.to_bits() { a } else { b })
}

/// See [`minmax_num_fold_f32`].
pub(in crate::codegen_ay) fn minmax_num_fold_f64(is_min: bool, a: f64, b: f64) -> Option<f64> {
    if minmax_num_result_is_nondeterministic_f64(a, b)
        || is_signalling_nan_f64(a)
        || is_signalling_nan_f64(b)
    {
        return None;
    }
    if a.is_nan() {
        return Some(b);
    }
    if b.is_nan() {
        return Some(a);
    }
    let a_wins = if is_min { a < b } else { a > b };
    Some(if a_wins || a.to_bits() == b.to_bits() { a } else { b })
}

/// `x` is a NaN, for an IEEE 754 bitvector of `width` bits (32 or 64).
pub(in crate::codegen_ay) fn ieee_is_nan_bv(x: &Expr, width: u32) -> Option<Expr> {
    let (exp_hi, exp_lo, all_ones, mant_hi) = match width {
        32 => (30u32, 23u32, 0xFFu64, 22u32),
        64 => (62u32, 52u32, 0x7FFu64, 51u32),
        _ => return None,
    };
    let exponent_all_ones =
        x.clone().extract(exp_hi, exp_lo).eq(Expr::bitvec_const(all_ones, exp_hi - exp_lo + 1));
    let mantissa_nonzero =
        x.clone().extract(mant_hi, 0).eq(Expr::bitvec_const(0u64, mant_hi + 1)).not();
    Some(exponent_all_ones.and(mantissa_nonzero))
}

/// `x` is `+0` or `-0`, for an IEEE 754 bitvector of `width` bits (32 or 64).
pub(in crate::codegen_ay) fn ieee_is_zero_bv(x: &Expr, width: u32) -> Option<Expr> {
    let magnitude_mask = match width {
        32 => Expr::bitvec_const(0x7FFF_FFFFu64, 32),
        64 => Expr::bitvec_const(0x7FFF_FFFF_FFFF_FFFFu64, 64),
        _ => return None,
    };
    Some(x.clone().bvand(magnitude_mask).eq(Expr::bitvec_const(0u64, width)))
}

/// The `minnum` (`is_min`) / `maxnum` result as a pure-bitvector term over fresh choices, for
/// encodings that bind a value rather than emit a relation (BMC).
///
/// `choice` is a fresh `Bool` and `nan_result` a fresh `width`-bit bitvector; the caller must
/// assert the returned constraint, which says `nan_result` is a NaN. The term is `nan_result`
/// for two NaNs, `a` or `b` (by `choice`) for two zeros, the other argument when exactly one is
/// NaN, and otherwise the strictly smaller (larger) argument — the same case split as the CHC
/// relation `minmax_num_result_constraint`, with IEEE comparison in bitvector form. No FP-theory
/// term: the solver decided `fp.min` of ground constants, but reported a model it could not
/// confirm once `fp.min` sat under an `ite` with free choices.
pub(in crate::codegen_ay) fn minmax_num_bv_term(
    is_min: bool,
    a: &Expr,
    b: &Expr,
    choice: Expr,
    nan_result: Expr,
    width: u32,
) -> Option<(Expr, Expr)> {
    let a_nan = ieee_is_nan_bv(a, width)?;
    let b_nan = ieee_is_nan_bv(b, width)?;
    let both_zero = ieee_is_zero_bv(a, width)?.and(ieee_is_zero_bv(b, width)?);
    let nan_result_is_nan = ieee_is_nan_bv(&nan_result, width)?;
    let a_wins = if is_min {
        crate::codegen_ay::float_compare::bv_float_lt(a, b, width)
    } else {
        crate::codegen_ay::float_compare::bv_float_gt(a, b, width)
    };
    let determined = Expr::ite(
        a_nan.clone(),
        b.clone(),
        Expr::ite(b_nan.clone(), a.clone(), Expr::ite(a_wins, a.clone(), b.clone())),
    );
    let term = Expr::ite(
        a_nan.and(b_nan),
        nan_result,
        Expr::ite(both_zero, Expr::ite(choice, a.clone(), b.clone()), determined),
    );
    Some((term, nan_result_is_nan))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn opposite_zeros_and_two_nans_have_no_single_result() {
        assert!(minmax_num_result_is_nondeterministic_f32(0.0, -0.0));
        assert!(minmax_num_result_is_nondeterministic_f32(-0.0, 0.0));
        assert!(minmax_num_result_is_nondeterministic_f64(-0.0, 0.0));
        assert!(minmax_num_result_is_nondeterministic_f32(f32::NAN, -f32::NAN));
        assert!(minmax_num_result_is_nondeterministic_f64(f64::NAN, f64::NAN));
        // Determined: identical zeros, one NaN, unequal values.
        assert!(!minmax_num_result_is_nondeterministic_f32(0.0, 0.0));
        assert!(!minmax_num_result_is_nondeterministic_f32(-0.0, -0.0));
        assert!(!minmax_num_result_is_nondeterministic_f32(f32::NAN, 1.0));
        assert!(!minmax_num_result_is_nondeterministic_f64(1.0, f64::NAN));
        assert!(!minmax_num_result_is_nondeterministic_f64(2.5, -1.0));
    }

    #[test]
    fn nondeterministic_term_is_built_at_both_widths_only() {
        for width in [32u32, 64] {
            for is_min in [true, false] {
                let a = Expr::var("a", ay_bindings::Sort::bitvec(width));
                let b = Expr::var("b", ay_bindings::Sort::bitvec(width));
                let c = Expr::var("c", ay_bindings::Sort::bool());
                let n = Expr::var("n", ay_bindings::Sort::bitvec(width));
                let (term, nan) = minmax_num_bv_term(is_min, &a, &b, c, n, width).expect("term");
                assert_eq!(term.sort().bitvec_width(), Some(width));
                assert!(nan.sort().is_bool());
            }
        }
        let a = Expr::var("a16", ay_bindings::Sort::bitvec(16));
        assert!(ieee_is_nan_bv(&a, 16).is_none());
    }

    const SNAN_32: u32 = 0x7f80_0001;
    const NEG_SNAN_32: u32 = 0xff80_0001;
    const SNAN_64: u64 = 0x7ff0_0000_0000_0001;

    #[test]
    fn signalling_nans_are_told_from_quiet_ones() {
        assert!(is_signalling_nan_f32(f32::from_bits(SNAN_32)));
        assert!(is_signalling_nan_f32(f32::from_bits(NEG_SNAN_32)));
        assert!(!is_signalling_nan_f32(f32::NAN));
        assert!(!is_signalling_nan_f32(f32::from_bits(0x7fc0_0001)));
        assert!(!is_signalling_nan_f32(f32::INFINITY));
        assert!(!is_signalling_nan_f32(1.0));
        assert!(is_signalling_nan_f64(f64::from_bits(SNAN_64)));
        assert!(!is_signalling_nan_f64(f64::NAN));
        assert!(!is_signalling_nan_f64(-0.0));
    }

    /// The fold decides exactly the cases both toolchains decide alike, by IEEE comparison.
    #[test]
    fn fold_decides_ordered_values_and_one_quiet_nan() {
        assert_eq!(minmax_num_fold_f32(true, 1.0, 2.0), Some(1.0));
        assert_eq!(minmax_num_fold_f32(false, 1.0, 2.0), Some(2.0));
        assert_eq!(minmax_num_fold_f32(true, 3.0, -1.0), Some(-1.0));
        assert_eq!(minmax_num_fold_f32(false, -2.5, -1.0), Some(-1.0));
        assert_eq!(
            minmax_num_fold_f32(true, f32::NAN, 1.5).map(f32::to_bits),
            Some(1.5f32.to_bits())
        );
        assert_eq!(
            minmax_num_fold_f32(false, -2.5, f32::NAN).map(f32::to_bits),
            Some((-2.5f32).to_bits())
        );
        // A quiet NaN with a payload is still a quiet NaN: the other argument, bit for bit.
        let payload_nan = f32::from_bits(0xffc0_0123);
        assert_eq!(
            minmax_num_fold_f32(true, payload_nan, -0.0).map(f32::to_bits),
            Some(0x8000_0000)
        );
        // Identical zeros and identical values are themselves.
        assert_eq!(minmax_num_fold_f32(true, -0.0, -0.0).map(f32::to_bits), Some(0x8000_0000));
        assert_eq!(minmax_num_fold_f32(false, 0.0, 0.0).map(f32::to_bits), Some(0));
        assert_eq!(minmax_num_fold_f32(true, 7.0, 7.0), Some(7.0));
        // Subnormals against zeros are ordered.
        let sub = f32::from_bits(1);
        assert_eq!(minmax_num_fold_f32(true, sub, 0.0).map(f32::to_bits), Some(0));
        assert_eq!(minmax_num_fold_f32(false, sub, -0.0).map(f32::to_bits), Some(1));
        assert_eq!(minmax_num_fold_f32(true, f32::NEG_INFINITY, f32::MIN), Some(f32::NEG_INFINITY));
        assert_eq!(minmax_num_fold_f64(true, 1.0, 2.0), Some(1.0));
        assert_eq!(minmax_num_fold_f64(false, f64::NAN, -4.0), Some(-4.0));
        assert_eq!(minmax_num_fold_f64(false, 2.0, 2.0), Some(2.0));
    }

    /// Opposite zeros, two NaNs and any signalling NaN are left to the relation.
    #[test]
    fn fold_refuses_every_case_the_toolchains_may_decide_differently() {
        for is_min in [true, false] {
            assert_eq!(minmax_num_fold_f32(is_min, 0.0, -0.0), None);
            assert_eq!(minmax_num_fold_f32(is_min, -0.0, 0.0), None);
            assert_eq!(minmax_num_fold_f32(is_min, f32::NAN, -f32::NAN), None);
            assert_eq!(minmax_num_fold_f32(is_min, f32::from_bits(SNAN_32), 2.0), None);
            assert_eq!(minmax_num_fold_f32(is_min, 2.0, f32::from_bits(SNAN_32)), None);
            assert_eq!(minmax_num_fold_f32(is_min, f32::from_bits(NEG_SNAN_32), 0.0), None);
            assert_eq!(minmax_num_fold_f32(is_min, f32::from_bits(SNAN_32), f32::NAN), None);
            assert_eq!(minmax_num_fold_f64(is_min, -0.0, 0.0), None);
            assert_eq!(minmax_num_fold_f64(is_min, f64::from_bits(SNAN_64), -2.5), None);
            assert_eq!(minmax_num_fold_f64(is_min, -2.5, f64::from_bits(SNAN_64 | 1 << 63)), None);
            assert_eq!(minmax_num_fold_f64(is_min, f64::NAN, f64::NAN), None);
        }
    }

    /// Whatever the host's `f32::min` does with a signalling NaN, the fold never consults it:
    /// the answer is `None` even where the host happens to agree with the contract.
    #[test]
    fn fold_does_not_depend_on_the_host_min() {
        let snan = f32::from_bits(SNAN_32);
        let _host = snan.min(2.0); // quiet NaN or 2.0, depending on how this test was compiled
        assert_eq!(minmax_num_fold_f32(true, snan, 2.0), None);
        assert_eq!(minmax_num_fold_f32(false, 2.0, snan), None);
    }
}
