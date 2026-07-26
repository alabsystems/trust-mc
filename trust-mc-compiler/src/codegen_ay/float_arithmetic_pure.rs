// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Pure-BV IEEE 754 cast helpers (CHC-compatible, no FP rounding-mode terms).
//!
//! These functions implement float↔int and float↔float conversions using only
//! BV operations (extract, concat, bvshl, bvlshr, bvand, ite). No FP
//! rounding-mode constants (RNE, RTZ) are emitted, making them Z3 CHC
//! (PDR) compatible.
//!
//! Part of #3870: route around ay#6768 PDR FP rejection.

use super::float_arithmetic::float_width_to_eb_sb;
use ay_bindings::Expr;

/// Pure-BV float→int conversion (CHC-compatible, avoids FP rounding-mode terms).
///
/// IEEE 754 truncation toward zero: extract sign, exponent, mantissa from BV,
/// compute integer value via shift operations, apply sign. Returns None for
/// unsupported widths. Mirrors `build_float_to_int_expr` from `float_predicates.rs`
/// but at the module level for use from any encoding path.
///
/// Part of #3870.
pub(in crate::codegen_ay) fn float_to_int_bv_pure(
    src: Expr,
    target_width: u32,
    signed: bool,
) -> Option<Expr> {
    let width = src.sort().bitvec_width()?;
    let (eb, sb) = float_width_to_eb_sb(width)?;
    let mant_bits = sb - 1;
    let exp_width = eb;
    let bias = (1u64 << (eb - 1)) - 1;

    // Extract IEEE 754 fields.
    let sign = src.clone().extract(width - 1, width - 1);
    let exp_raw = src.clone().extract(width - 2, mant_bits);
    let mantissa = src.extract(mant_bits - 1, 0);

    // Full mantissa with implicit leading 1 (normalized numbers).
    let full_mant = Expr::bitvec_const(1u64, 1).concat(mantissa);
    let full_mant_width = mant_bits + 1;

    // Unbiased exponent (signed): exp = exp_raw - bias.
    let bias_bv = Expr::bitvec_const(bias, exp_width);
    let exp_unbiased = exp_raw.bvsub(bias_bv);

    // Work in a width large enough for all intermediate computations.
    let work_width = target_width.max(full_mant_width).max(exp_width) + 1;

    let mant_wide = full_mant.zero_extend(work_width - full_mant_width);
    let mant_bits_bv = Expr::bitvec_const(mant_bits as u64, work_width);
    let exp_wide = exp_unbiased.sign_extend(work_width - exp_width);
    let zero_wide = Expr::bitvec_const(0u64, work_width);

    // Case 1: exp >= mant_bits → integer = full_mant << (exp - mant_bits)
    // Case 2: 0 <= exp < mant_bits → integer = full_mant >> (mant_bits - exp)
    // Case 3: exp < 0 → integer = 0 (|f| < 1, truncates to 0)
    let shift_left_amt = exp_wide.clone().bvsub(mant_bits_bv.clone());
    let shift_right_amt = mant_bits_bv.bvsub(exp_wide.clone());
    let case1_val = mant_wide.clone().bvshl(shift_left_amt);
    let case2_val = mant_wide.bvlshr(shift_right_amt);

    let exp_ge_mant = exp_wide.clone().bvsge(Expr::bitvec_const(mant_bits as u64, work_width));
    let exp_ge_zero = exp_wide.bvsge(zero_wide.clone());

    let integer_unsigned =
        Expr::ite(exp_ge_mant, case1_val, Expr::ite(exp_ge_zero, case2_val, zero_wide));

    // Apply sign.
    let sign_is_neg = sign.eq(Expr::bitvec_const(1u64, 1));
    let result = if signed {
        Expr::ite(sign_is_neg, integer_unsigned.clone().bvneg(), integer_unsigned)
    } else {
        Expr::ite(sign_is_neg, Expr::bitvec_const(0u64, work_width), integer_unsigned)
    };

    // Truncate or extend to target width.
    let final_result = if work_width > target_width {
        result.extract(target_width - 1, 0)
    } else if work_width < target_width {
        result.zero_extend(target_width - work_width)
    } else {
        result
    };

    Some(final_result)
}

/// Pure-BV float↔float conversion (CHC-compatible, avoids FP rounding-mode terms).
///
/// For same width: identity.
/// For widening (e.g., f32→f64): exact — re-bias exponent, zero-extend mantissa.
///   Subnormal inputs are normalized via ITE cascade for MSB position.
/// For narrowing (e.g., f64→f32): re-bias exponent, truncate mantissa with
///   round-to-nearest-even (guard + sticky bits). Handles overflow (→ Inf) and
///   underflow (→ subnormal/zero).
///
/// Part of #3870.
pub(in crate::codegen_ay) fn float_to_float_bv_pure(
    src: Expr,
    src_width: u32,
    target_width: u32,
) -> Option<Expr> {
    if src_width == target_width {
        return Some(src);
    }

    let (src_eb, src_sb) = float_width_to_eb_sb(src_width)?;
    let (tgt_eb, tgt_sb) = float_width_to_eb_sb(target_width)?;
    let src_mant = src_sb - 1; // stored mantissa bits
    let tgt_mant = tgt_sb - 1;
    let src_bias: u64 = (1u64 << (src_eb - 1)) - 1;
    let tgt_bias: u64 = (1u64 << (tgt_eb - 1)) - 1;

    // Extract source IEEE 754 fields.
    let sign = src.clone().extract(src_width - 1, src_width - 1);
    let src_exp = src.clone().extract(src_width - 2, src_mant);
    let src_mantissa = src.extract(src_mant - 1, 0);

    // Special case detection.
    let exp_all_ones = Expr::bitvec_const((1u64 << src_eb) - 1, src_eb);
    let is_exp_all_ones = src_exp.clone().eq(exp_all_ones);
    let is_exp_zero = src_exp.clone().eq(Expr::bitvec_const(0u64, src_eb));
    let is_mant_zero = src_mantissa.clone().eq(Expr::bitvec_const(0u64, src_mant));

    // Target special values.
    let tgt_exp_all_ones = Expr::bitvec_const((1u64 << tgt_eb) - 1, tgt_eb);
    let tgt_inf =
        sign.clone().concat(tgt_exp_all_ones.clone()).concat(Expr::bitvec_const(0u64, tgt_mant));
    let tgt_nan = sign
        .clone()
        .concat(tgt_exp_all_ones)
        .concat(Expr::bitvec_const(1u64 << (tgt_mant - 1), tgt_mant));
    let tgt_zero = sign.clone().concat(Expr::bitvec_const(0u64, target_width - 1));

    // Each branch produces the final result including special case handling,
    // avoiding double-move of intermediate Expr values.
    let result = if src_width < target_width {
        // ===== WIDENING (e.g., f32 → f64) — exact, no rounding needed =====

        // Normal case: re-bias exponent, zero-extend mantissa.
        let work_exp = tgt_eb.max(src_eb).max(src_mant).max(tgt_mant) + 2;
        let src_exp_wide = src_exp.zero_extend(work_exp - src_eb);
        let new_exp_normal = src_exp_wide
            .bvsub(Expr::bitvec_const(src_bias, work_exp))
            .bvadd(Expr::bitvec_const(tgt_bias, work_exp));
        let new_exp_normal_bits = new_exp_normal.extract(tgt_eb - 1, 0);
        let new_mant_normal =
            src_mantissa.clone().concat(Expr::bitvec_const(0u64, tgt_mant - src_mant));
        let normal = sign.clone().concat(new_exp_normal_bits).concat(new_mant_normal);

        // Subnormal case: exp == 0, mantissa != 0. Normalize via MSB detection.
        let mut msb_pos = Expr::bitvec_const(0u64, src_mant);
        for i in 1..src_mant {
            let bit = src_mantissa.clone().extract(i, i);
            let is_one = bit.eq(Expr::bitvec_const(1u64, 1));
            msb_pos = Expr::ite(is_one, Expr::bitvec_const(i as u64, src_mant), msb_pos);
        }

        // New biased exponent for subnormal:
        // unbiased = k + 1 - src_bias - src_mant
        // biased_target = k + 1 - src_bias - src_mant + tgt_bias
        let exp_offset = 1i64 + tgt_bias as i64 - src_bias as i64 - src_mant as i64;
        let msb_pos_wide = msb_pos.clone().zero_extend(work_exp - src_mant);
        let new_exp_sub = msb_pos_wide.bvadd(Expr::bitvec_const(exp_offset as u64, work_exp));
        let new_exp_sub_bits = new_exp_sub.extract(tgt_eb - 1, 0);

        // New mantissa: shift src_mantissa left so bit k aligns to bit tgt_mant,
        // then mask off the implicit leading 1.
        let mant_work = tgt_mant + 1;
        let src_mant_wide = src_mantissa.zero_extend(mant_work - src_mant);
        let msb_pos_mant = msb_pos.zero_extend(mant_work - src_mant);
        let shift_left = Expr::bitvec_const(tgt_mant as u64, mant_work).bvsub(msb_pos_mant);
        let shifted = src_mant_wide.bvshl(shift_left);
        let mant_mask = Expr::bitvec_const((1u64 << tgt_mant) - 1, mant_work);
        let new_mant_sub = shifted.bvand(mant_mask).extract(tgt_mant - 1, 0);

        let subnormal = sign.concat(new_exp_sub_bits).concat(new_mant_sub);

        // Final assembly for widening: special cases > zero > subnormal > normal.
        Expr::ite(
            is_exp_all_ones,
            Expr::ite(is_mant_zero.clone(), tgt_inf, tgt_nan),
            Expr::ite(is_exp_zero, Expr::ite(is_mant_zero, tgt_zero, subnormal), normal),
        )
    } else {
        // ===== NARROWING (e.g., f64 → f32) — needs RNE rounding =====

        let work_exp = src_eb.max(tgt_eb) + 2;
        let delta = src_bias - tgt_bias; // e.g., 896 for f64→f32

        // New biased exponent = src_exp - delta (signed arithmetic).
        let src_exp_wide = src_exp.zero_extend(work_exp - src_eb);
        let delta_bv = Expr::bitvec_const(delta, work_exp);
        let new_exp = src_exp_wide.bvsub(delta_bv);

        // Full significand with implicit leading 1: (src_mant+1) bits.
        let full_sig = Expr::bitvec_const(1u64, 1).concat(src_mantissa);
        let sig_width = src_mant + 1;

        // Subnormal shift: S = max(0, 1 - new_exp).
        let one_wide = Expr::bitvec_const(1u64, work_exp);
        let s_wide = one_wide.bvsub(new_exp.clone());
        let is_subnormal_output = new_exp.clone().bvsle(Expr::bitvec_const(0u64, work_exp));

        // Convert S to sig_width for BV shift. Clamp to sig_width to avoid overshift.
        let s_sig = if work_exp > sig_width {
            s_wide.extract(sig_width - 1, 0)
        } else {
            s_wide.zero_extend(sig_width - work_exp)
        };
        let zero_shift = Expr::bitvec_const(0u64, sig_width);
        let effective_shift = Expr::ite(is_subnormal_output.clone(), s_sig, zero_shift);

        // Apply subnormal shift to full significand.
        let effective_sig = full_sig.bvlshr(effective_shift);

        // Extract target mantissa, guard bit, and sticky bits.
        let dropped = src_mant - tgt_mant;
        let trunc_mant = effective_sig.clone().extract(src_mant - 1, dropped);
        let guard = effective_sig.clone().extract(dropped - 1, dropped - 1);
        let sticky = if dropped >= 2 {
            let lower = effective_sig.extract(dropped - 2, 0);
            let lower_zero = Expr::bitvec_const(0u64, dropped - 1);
            Expr::ite(
                lower.eq(lower_zero),
                Expr::bitvec_const(0u64, 1),
                Expr::bitvec_const(1u64, 1),
            )
        } else {
            Expr::bitvec_const(0u64, 1)
        };

        // RNE rounding: round up if guard=1 AND (sticky!=0 OR LSB=1).
        let lsb = trunc_mant.clone().extract(0, 0);
        let one_1 = Expr::bitvec_const(1u64, 1);
        let zero_1 = Expr::bitvec_const(0u64, 1);
        let guard_is_one = guard.eq(one_1.clone());
        let sticky_or_lsb = Expr::ite(
            sticky.eq(one_1.clone()),
            one_1.clone(),
            Expr::ite(lsb.eq(one_1.clone()), one_1.clone(), zero_1.clone()),
        );
        let round_up = Expr::ite(guard_is_one, sticky_or_lsb, zero_1).eq(one_1);

        // Apply rounding with overflow detection: widen mantissa by 1 bit.
        let trunc_wide = trunc_mant.zero_extend(1); // tgt_mant+1 bits
        let round_add = Expr::ite(
            round_up,
            Expr::bitvec_const(1u64, tgt_mant + 1),
            Expr::bitvec_const(0u64, tgt_mant + 1),
        );
        let rounded_wide = trunc_wide.bvadd(round_add);
        let carry = rounded_wide.clone().extract(tgt_mant, tgt_mant);
        let final_mant = rounded_wide.extract(tgt_mant - 1, 0);

        // Final exponent: new_exp + carry (for normal), 0 + carry (for subnormal).
        let base_exp = Expr::ite(is_subnormal_output, Expr::bitvec_const(0u64, work_exp), new_exp);
        let carry_wide = carry.zero_extend(work_exp - 1);
        let final_exp = base_exp.bvadd(carry_wide);

        // Overflow check: final_exp >= tgt_exp_max (all-ones reserved for Inf/NaN).
        let tgt_exp_max = (1u64 << tgt_eb) - 1;
        let exp_overflow = final_exp.clone().bvuge(Expr::bitvec_const(tgt_exp_max, work_exp));
        let final_exp_bits = final_exp.extract(tgt_eb - 1, 0);

        let narrow_result = sign.concat(final_exp_bits).concat(final_mant);
        let narrow_or_inf = Expr::ite(exp_overflow, tgt_inf.clone(), narrow_result);

        // Final assembly for narrowing: special cases > source subnormal/zero > narrow.
        Expr::ite(
            is_exp_all_ones,
            Expr::ite(is_mant_zero, tgt_inf, tgt_nan),
            Expr::ite(is_exp_zero, tgt_zero, narrow_or_inf),
        )
    };

    Some(result)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_bindings::Expr;

    // --- float_to_int_bv_pure tests ---

    #[test]
    fn test_float_to_int_bv_pure_f32_to_u32() {
        let bv = Expr::bitvec_const(0x42280000u64, 32); // 42.0f32
        let result = float_to_int_bv_pure(bv, 32, false).expect("f32→u32 supported");
        assert_eq!(result.sort().bitvec_width(), Some(32));
    }

    #[test]
    fn test_float_to_int_bv_pure_f64_to_i64() {
        let bv = Expr::bitvec_const(0x4045000000000000u64, 64); // 42.0f64
        let result = float_to_int_bv_pure(bv, 64, true).expect("f64→i64 supported");
        assert_eq!(result.sort().bitvec_width(), Some(64));
    }

    #[test]
    fn test_float_to_int_bv_pure_unsupported_returns_none() {
        let bv = Expr::bitvec_const(0u64, 80);
        assert!(float_to_int_bv_pure(bv, 32, false).is_none());
    }

    // --- float_to_float_bv_pure tests ---

    #[test]
    fn test_float_to_float_bv_pure_same_width_identity() {
        let bv = Expr::bitvec_const(0x42280000u64, 32); // 42.0f32
        let result = float_to_float_bv_pure(bv, 32, 32).expect("same-width");
        assert_eq!(result.sort().bitvec_width(), Some(32));
    }

    #[test]
    fn test_float_to_float_bv_pure_f32_to_f64() {
        let bv = Expr::bitvec_const(0x42280000u64, 32); // 42.0f32
        let result = float_to_float_bv_pure(bv, 32, 64).expect("f32→f64");
        assert_eq!(result.sort().bitvec_width(), Some(64));
    }

    #[test]
    fn test_float_to_float_bv_pure_f64_to_f32() {
        let bv = Expr::bitvec_const(0x4045000000000000u64, 64); // 42.0f64
        let result = float_to_float_bv_pure(bv, 64, 32).expect("f64→f32");
        assert_eq!(result.sort().bitvec_width(), Some(32));
    }

    #[test]
    fn test_float_to_float_bv_pure_unsupported_returns_none() {
        let bv = Expr::bitvec_const(0u64, 80);
        assert!(float_to_float_bv_pure(bv, 80, 32).is_none());
    }

    #[test]
    fn test_float_to_float_bv_pure_f32_zero_to_f64() {
        let bv = Expr::bitvec_const(0u64, 32); // +0.0f32
        let result = float_to_float_bv_pure(bv, 32, 64).expect("zero widening");
        assert_eq!(result.sort().bitvec_width(), Some(64));
    }

    #[test]
    fn test_float_to_float_bv_pure_f32_neg_zero_to_f64() {
        let bv = Expr::bitvec_const(0x8000_0000u64, 32); // -0.0f32
        let result = float_to_float_bv_pure(bv, 32, 64).expect("neg zero widening");
        assert_eq!(result.sort().bitvec_width(), Some(64));
    }

    #[test]
    fn test_float_to_float_bv_pure_f32_inf_to_f64() {
        let bv = Expr::bitvec_const(0x7F80_0000u64, 32); // +Inf f32
        let result = float_to_float_bv_pure(bv, 32, 64).expect("inf widening");
        assert_eq!(result.sort().bitvec_width(), Some(64));
    }

    #[test]
    fn test_float_to_float_bv_pure_f32_nan_to_f64() {
        let bv = Expr::bitvec_const(0x7FC0_0000u64, 32); // quiet NaN f32
        let result = float_to_float_bv_pure(bv, 32, 64).expect("nan widening");
        assert_eq!(result.sort().bitvec_width(), Some(64));
    }
}
