// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Pure BV rounding functions for IEEE 754 floats.
//!
//! Implements floor/ceil/trunc/round/round_ties_even using only BV operations
//! (extract, concat, bvand, bvshl, ite). No FP rounding-mode constants are
//! emitted, making these Z3 CHC compatible.
//!
//! Part of #3750 (pure BV rounding to avoid Z3 CHC parser rejection).

use super::float_predicates::ieee754_params;
use ay_bindings::Expr;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(in crate::codegen_ay::chc) enum FractHalfCmp {
    Lt,
    Le,
    Gt,
    Ge,
    Eq,
    Ne,
}

/// Intermediate values shared by all BV rounding functions.
/// Extracted once from the IEEE 754 BV, reused by trunc/floor/ceil/round/round_ties_even.
struct FloatBvParts {
    width: u32,
    mant_bits: u32,
    exp_width: u32,
    sign: Expr,
    exp_raw: Expr,
    mantissa: Expr,
    /// True if NaN or Inf (exponent all-ones).
    is_special: Expr,
    /// True if unbiased exponent >= mant_bits (already an integer).
    is_integer: Expr,
    /// True if unbiased exponent < 0 (|x| < 1 for normalized, or subnormal/zero).
    is_sub_one: Expr,
    /// ±0 with same sign as input.
    signed_zero: Expr,
    /// Integer-preserving mask for mantissa: all_ones << (mant_bits - exp).
    /// Valid only when 0 <= exp < mant_bits.
    integer_mask: Expr,
    /// Mantissa with fractional bits cleared: mantissa & integer_mask.
    masked_mantissa: Expr,
    /// shift_amt = mant_bits - exp (number of fractional bits), in mant_bits width.
    /// Valid only when 0 <= exp < mant_bits.
    shift_amt: Expr,
    /// Unbiased exponent widened to work_width (signed).
    exp_wide: Expr,
    /// Work width used for signed comparisons.
    work_width: u32,
    /// bias value.
    bias: u32,
}

impl FloatBvParts {
    fn extract(value: &Expr) -> Option<Self> {
        let width = value.sort().bitvec_width()?;
        let (exp_hi, exp_lo, mant_bits, bias) = ieee754_params(width)?;
        let exp_width = exp_hi - exp_lo + 1;

        let sign = value.clone().extract(width - 1, width - 1);
        let exp_raw = value.clone().extract(exp_hi, exp_lo);
        let mantissa = value.clone().extract(exp_lo - 1, 0);

        // Special: NaN/Inf (exp all-ones)
        let exp_all_ones = (1u64 << exp_width) - 1;
        let is_special = exp_raw.clone().eq(Expr::bitvec_const(exp_all_ones, exp_width));

        // Unbiased exponent (signed)
        let bias_bv = Expr::bitvec_const(bias as u64, exp_width);
        let exp_unbiased = exp_raw.clone().bvsub(bias_bv);

        // Work in a width big enough for signed comparisons
        let work_width = mant_bits.max(exp_width) + 1;
        let exp_wide = exp_unbiased.sign_extend(work_width - exp_width);
        let mant_bits_bv = Expr::bitvec_const(mant_bits as u64, work_width);
        let zero_wide = Expr::bitvec_const(0u64, work_width);

        let is_integer = exp_wide.clone().bvsge(mant_bits_bv);
        let is_sub_one = exp_wide.clone().bvslt(zero_wide);

        let signed_zero = sign.clone().concat(Expr::bitvec_const(0u64, width - 1));

        // Mask computation for 0 <= exp < mant_bits case.
        // shift_amt = mant_bits - exp (in mant_bits width).
        let mant_bits_bv_m = Expr::bitvec_const(mant_bits as u64, mant_bits);
        let exp_in_mant_width = exp_wide.clone().extract(mant_bits - 1, 0);
        let shift_amt = mant_bits_bv_m.bvsub(exp_in_mant_width);

        // integer_mask = all_ones << shift_amt (mant_bits-wide)
        let all_ones = Expr::bitvec_const(0u64, mant_bits).bvnot();
        let integer_mask = all_ones.bvshl(shift_amt.clone());
        let masked_mantissa = mantissa.clone().bvand(integer_mask.clone());

        Some(FloatBvParts {
            width,
            mant_bits,
            exp_width,
            sign,
            exp_raw,
            mantissa,
            is_special,
            is_integer,
            is_sub_one,
            signed_zero,
            integer_mask,
            masked_mantissa,
            shift_amt,
            exp_wide,
            work_width,
            bias,
        })
    }

    /// Reassemble sign ++ exp_raw ++ mantissa_bits into a full-width BV.
    fn reassemble(&self, mantissa_bits: Expr) -> Expr {
        self.sign.clone().concat(self.exp_raw.clone()).concat(mantissa_bits)
    }

    /// Build the truncated value for the normal case (0 <= exp < mant_bits).
    fn truncated(&self) -> Expr {
        self.reassemble(self.masked_mantissa.clone())
    }

    /// True if the value is ±0.0 (exp_raw == 0 AND mantissa == 0).
    /// Used to distinguish ±0 from subnormals in the sub_one branch.
    fn is_zero(&self) -> Expr {
        self.exp_raw
            .clone()
            .eq(Expr::bitvec_const(0u64, self.exp_width))
            .and(self.mantissa.clone().eq(Expr::bitvec_const(0u64, self.mant_bits)))
    }

    /// True if the input has non-zero fractional bits (in the normal case).
    fn has_fractional_bits(&self) -> Expr {
        let frac_mask = self.integer_mask.clone().bvnot();
        let frac_bits = self.mantissa.clone().bvand(frac_mask);
        frac_bits.eq(Expr::bitvec_const(0u64, self.mant_bits)).not()
    }

    /// Increment the magnitude of the truncated value by 1 integer ULP.
    /// Adds 1 at bit position shift_amt in the (exp_raw ++ mantissa) field,
    /// with carry propagation through BV addition.
    fn magnitude_incremented(&self) -> Expr {
        let unsigned_width = self.width - 1;
        let unsigned_trunc = self.exp_raw.clone().concat(self.masked_mantissa.clone());
        // ULP = 1 << shift_amt, in unsigned_width bits.
        // shift_amt is mant_bits-wide; widen to unsigned_width.
        let shift_wide = self.shift_amt.clone().zero_extend(unsigned_width - self.mant_bits);
        let one = Expr::bitvec_const(1u64, unsigned_width);
        let ulp = one.bvshl(shift_wide);
        let incremented = unsigned_trunc.bvadd(ulp);
        self.sign.clone().concat(incremented)
    }

    /// Build ±1.0 constant with the same sign as input.
    /// IEEE 754: sign ++ bias_encoding ++ zero_mantissa
    fn signed_one(&self) -> Expr {
        let bias_bv = Expr::bitvec_const(self.bias as u64, self.exp_width);
        self.sign.clone().concat(bias_bv).concat(Expr::bitvec_const(0u64, self.mant_bits))
    }

    /// Check if the highest fractional bit is set (fraction >= 0.5).
    /// The highest frac bit is at mantissa position (shift_amt - 1).
    fn highest_frac_bit_set(&self) -> Expr {
        // highest_frac_mask = 1 << (shift_amt - 1), in mant_bits width
        let one_m = Expr::bitvec_const(1u64, self.mant_bits);
        let shift_minus_1 = self.shift_amt.clone().bvsub(one_m.clone());
        let highest_frac_mask = one_m.bvshl(shift_minus_1);
        let bit = self.mantissa.clone().bvand(highest_frac_mask);
        bit.eq(Expr::bitvec_const(0u64, self.mant_bits)).not()
    }

    /// Check if there are fractional bits below the highest fractional bit.
    /// I.e., the fraction is strictly > 0.5 (not exactly 0.5).
    fn has_lower_frac_bits(&self) -> Expr {
        // lower_frac_mask = (1 << (shift_amt - 1)) - 1, in mant_bits width
        let one_m = Expr::bitvec_const(1u64, self.mant_bits);
        let shift_minus_1 = self.shift_amt.clone().bvsub(one_m.clone());
        let lower_frac_mask =
            one_m.bvshl(shift_minus_1).bvsub(Expr::bitvec_const(1u64, self.mant_bits));
        let lower_bits = self.mantissa.clone().bvand(lower_frac_mask);
        lower_bits.eq(Expr::bitvec_const(0u64, self.mant_bits)).not()
    }

    /// Check if the lowest integer mantissa bit is odd.
    /// For exp == 0, the only integer bit is the implicit leading 1 (always odd).
    /// For exp >= 1, it's mantissa[shift_amt].
    fn lowest_integer_bit_odd(&self) -> Expr {
        let exp_zero = self.exp_wide.clone().eq(Expr::bitvec_const(0u64, self.work_width));
        // mantissa[shift_amt]: extract via mask (1 << shift_amt)
        let one_m = Expr::bitvec_const(1u64, self.mant_bits);
        let int_bit_mask = one_m.bvshl(self.shift_amt.clone());
        let int_bit = self.mantissa.clone().bvand(int_bit_mask);
        let is_odd = int_bit.eq(Expr::bitvec_const(0u64, self.mant_bits)).not();
        // For exp == 0, implicit leading 1 is always odd
        Expr::ite(exp_zero, Expr::bool_const(true), is_odd)
    }
}

/// Pure BV trunc: clear fractional mantissa bits. No FP rounding modes.
///
/// IEEE 754 `trunc(x)` rounds toward zero by clearing fractional bits in
/// the mantissa. NaN/Inf pass through unchanged. Subnormals and values
/// with |x| < 1 return ±0 (preserving sign).
///
/// Part of #3750.
pub(in crate::codegen_ay::chc) fn build_float_trunc_bv(value: &Expr) -> Option<Expr> {
    let p = FloatBvParts::extract(value)?;

    Some(Expr::ite(
        p.is_special.clone().or(p.is_integer.clone()),
        value.clone(),
        Expr::ite(p.is_sub_one.clone(), p.signed_zero.clone(), p.truncated()),
    ))
}

/// Pure BV floor: round toward negative infinity. No FP rounding modes.
///
/// `floor(x) = trunc(x)` if `x >= 0` or `x` is already an integer.
/// `floor(x) = trunc(x) - 1` (decrement magnitude) if `x < 0` and has fraction.
/// For `|x| < 1` and non-zero: positive → +0.0, negative → -1.0.
/// For ±0: return ±0 unchanged.
///
/// Part of #3750, Part of #3798.
pub(in crate::codegen_ay::chc) fn build_float_floor_bv(value: &Expr) -> Option<Expr> {
    let p = FloatBvParts::extract(value)?;
    let is_negative = p.sign.clone().eq(Expr::bitvec_const(1u64, 1));
    let has_frac = p.has_fractional_bits();
    let neg_with_frac = is_negative.clone().and(has_frac);

    // Sub_one case: ±0 → ±0, negative non-zero → -1.0, positive non-zero → +0.0
    let neg_one = {
        let bias_bv = Expr::bitvec_const(p.bias as u64, p.exp_width);
        Expr::bitvec_const(1u64, 1).concat(bias_bv).concat(Expr::bitvec_const(0u64, p.mant_bits))
    };
    let non_zero_sub = Expr::ite(is_negative, neg_one, p.signed_zero.clone());
    let sub_one_result = Expr::ite(p.is_zero(), value.clone(), non_zero_sub);

    // Normal case with negative + fraction: increment magnitude of trunc
    let normal_result = Expr::ite(neg_with_frac, p.magnitude_incremented(), p.truncated());

    Some(Expr::ite(
        p.is_special.clone().or(p.is_integer.clone()),
        value.clone(),
        Expr::ite(p.is_sub_one, sub_one_result, normal_result),
    ))
}

/// Pure BV ceil: round toward positive infinity. No FP rounding modes.
///
/// `ceil(x) = trunc(x)` if `x <= 0` or `x` is already an integer.
/// `ceil(x) = trunc(x) + 1` (increment magnitude) if `x > 0` and has fraction.
/// For `|x| < 1` and non-zero: positive → +1.0, negative → -0.0.
/// For ±0: return ±0 unchanged.
///
/// Part of #3750, Part of #3798.
pub(in crate::codegen_ay::chc) fn build_float_ceil_bv(value: &Expr) -> Option<Expr> {
    let p = FloatBvParts::extract(value)?;
    let is_positive = p.sign.clone().eq(Expr::bitvec_const(0u64, 1));
    let has_frac = p.has_fractional_bits();
    let pos_with_frac = is_positive.clone().and(has_frac);

    // Sub_one case: ±0 → ±0, positive non-zero → +1.0, negative non-zero → -0.0
    let pos_one = {
        let bias_bv = Expr::bitvec_const(p.bias as u64, p.exp_width);
        Expr::bitvec_const(0u64, 1).concat(bias_bv).concat(Expr::bitvec_const(0u64, p.mant_bits))
    };
    let non_zero_sub = Expr::ite(is_positive, pos_one, p.signed_zero.clone());
    let sub_one_result = Expr::ite(p.is_zero(), value.clone(), non_zero_sub);

    // Normal case with positive + fraction: increment magnitude of trunc
    let normal_result = Expr::ite(pos_with_frac, p.magnitude_incremented(), p.truncated());

    Some(Expr::ite(
        p.is_special.clone().or(p.is_integer.clone()),
        value.clone(),
        Expr::ite(p.is_sub_one, sub_one_result, normal_result),
    ))
}

/// Pure BV round: round to nearest, ties away from zero. No FP rounding modes.
///
/// If fraction >= 0.5: round away from zero (increment magnitude of trunc).
/// If fraction < 0.5: trunc.
/// For `|x| < 1`: exp == -1 means |x| in [0.5, 1) → round to ±1.0.
/// exp < -1 means |x| < 0.5 → round to ±0.
///
/// Part of #3750.
pub(in crate::codegen_ay::chc) fn build_float_round_bv(value: &Expr) -> Option<Expr> {
    let p = FloatBvParts::extract(value)?;

    // Sub_one case: check if exp == -1 (exp_raw == bias - 1), meaning |x| >= 0.5
    let exp_minus_1 = Expr::bitvec_const((p.bias - 1) as u64, p.exp_width);
    let is_half_or_more = p.exp_raw.clone().eq(exp_minus_1);
    let sub_one_result = Expr::ite(is_half_or_more, p.signed_one(), p.signed_zero.clone());

    // Normal case: check highest fractional bit
    let highest_set = p.highest_frac_bit_set();
    let normal_result = Expr::ite(highest_set, p.magnitude_incremented(), p.truncated());

    Some(Expr::ite(
        p.is_special.clone().or(p.is_integer.clone()),
        value.clone(),
        Expr::ite(p.is_sub_one, sub_one_result, normal_result),
    ))
}

/// Pure BV round_ties_even: round to nearest, ties to even (banker's rounding).
/// No FP rounding modes.
///
/// If fraction > 0.5: round away from zero.
/// If fraction < 0.5: trunc.
/// If fraction == 0.5: round to even (check lowest integer bit).
///
/// Part of #3750.
pub(in crate::codegen_ay::chc) fn build_float_round_ties_even_bv(value: &Expr) -> Option<Expr> {
    let p = FloatBvParts::extract(value)?;

    // Sub_one case:
    // exp == -1: |x| in [0.5, 1). Check if exactly 0.5 (mantissa == 0):
    //   exactly 0.5 → tie → nearest even integer is 0 → return ±0
    //   > 0.5 (mantissa != 0) → round to ±1.0
    // exp < -1: |x| < 0.5 → return ±0
    let exp_minus_1 = Expr::bitvec_const((p.bias - 1) as u64, p.exp_width);
    let is_half_range = p.exp_raw.clone().eq(exp_minus_1);
    let mant_nonzero = p.mantissa.clone().eq(Expr::bitvec_const(0u64, p.mant_bits)).not();
    let sub_one_half_gt = is_half_range.and(mant_nonzero);
    let sub_one_result = Expr::ite(sub_one_half_gt, p.signed_one(), p.signed_zero.clone());

    // Normal case:
    // highest_frac_bit AND has_lower_frac → fraction > 0.5 → round away
    // highest_frac_bit AND !has_lower_frac → fraction == 0.5 → tie:
    //   lowest_integer_bit_odd → round away (to make even)
    //   lowest_integer_bit_even → trunc (already even)
    // !highest_frac_bit → fraction < 0.5 → trunc
    let highest_set = p.highest_frac_bit_set();
    let has_lower = p.has_lower_frac_bits();
    let is_odd = p.lowest_integer_bit_odd();

    let frac_gt_half = highest_set.clone().and(has_lower.clone());
    let frac_eq_half_odd = highest_set.and(has_lower.not()).and(is_odd);
    let should_round_away = frac_gt_half.or(frac_eq_half_odd);

    let normal_result = Expr::ite(should_round_away, p.magnitude_incremented(), p.truncated());

    Some(Expr::ite(
        p.is_special.clone().or(p.is_integer.clone()),
        value.clone(),
        Expr::ite(p.is_sub_one, sub_one_result, normal_result),
    ))
}

/// Pure BV comparison for `x.fract().abs()` against `0.5`.
///
/// `fract(x)` lowers to `x - trunc(x)`, and the residual #3763 UNKNOWNs only
/// compare that absolute fractional distance against `0.5` to decide which
/// rounding-side assertion should hold. This helper computes the comparison
/// directly from the original float bits, avoiding the CHC-incompatible FP
/// subtraction path in `bv_float_binop`.
pub(in crate::codegen_ay::chc) fn build_float_abs_fract_cmp_half(
    value: &Expr,
    cmp: FractHalfCmp,
) -> Option<Expr> {
    let p = FloatBvParts::extract(value)?;
    let finite = p.is_special.clone().not();

    let zero = Expr::bool_const(false);
    let one = Expr::bool_const(true);

    let exp_minus_1 = Expr::bitvec_const((p.bias - 1) as u64, p.exp_width);
    let sub_half_range = p.exp_raw.clone().eq(exp_minus_1);
    let sub_mant_nonzero = p.mantissa.clone().eq(Expr::bitvec_const(0u64, p.mant_bits)).not();
    let sub_gt_half = sub_half_range.clone().and(sub_mant_nonzero.clone());
    let sub_eq_half = sub_half_range.and(sub_mant_nonzero.not());

    let normal_gt_half = p.highest_frac_bit_set().and(p.has_lower_frac_bits());
    let normal_eq_half = p.highest_frac_bit_set().and(p.has_lower_frac_bits().not());

    let gt_half = Expr::ite(
        p.is_integer.clone(),
        zero.clone(),
        Expr::ite(p.is_sub_one.clone(), sub_gt_half, normal_gt_half),
    );
    let eq_half =
        Expr::ite(p.is_integer.clone(), zero, Expr::ite(p.is_sub_one, sub_eq_half, normal_eq_half));
    let ge_half = gt_half.clone().or(eq_half.clone());
    let lt_half = finite.clone().and(ge_half.clone().not());
    let le_half = finite.clone().and(gt_half.clone().not());
    let ne_half = eq_half.clone().not();

    Some(match cmp {
        FractHalfCmp::Lt => lt_half,
        FractHalfCmp::Le => le_half,
        FractHalfCmp::Gt => finite.and(gt_half),
        FractHalfCmp::Ge => finite.and(ge_half),
        FractHalfCmp::Eq => finite.and(eq_half),
        FractHalfCmp::Ne => Expr::ite(finite, ne_half, one),
    })
}
