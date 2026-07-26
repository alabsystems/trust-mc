// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! IEEE 754 arithmetic helpers for BV-encoded floats (Part of #3693).
//! BMC path: BV→FP→op→BV via FP theory. CHC path: constant-fold or BV int ops.

use ay_bindings::{Expr, ExprValue, RoundingMode};
use rustc_public::mir::BinOp;

/// Reinterpret a BV as IEEE 754 FP via `fp_from_bvs` (sign/exponent/significand).
/// NOT `((_ to_fp eb sb) rm bv)` which is signed integer→float conversion.
pub(in crate::codegen_ay) fn bv_to_ieee_fp(bv: Expr, eb: u32, sb: u32) -> Expr {
    let total = eb + sb;
    let sign = bv.clone().extract(total - 1, total - 1); // 1-bit sign
    let exponent = bv.clone().extract(total - 2, sb - 1); // eb-bit exponent
    let significand = bv.extract(sb - 2, 0); // (sb-1)-bit significand
    Expr::fp_from_bvs(sign, exponent, significand)
}

/// Perform IEEE 754 arithmetic on BV-encoded float operands.
///
/// Reinterprets both operands from BV to FP via IEEE 754 bit-level split
/// (`fp_from_bvs`), performs the FP theory operation with Round-to-Nearest-Even,
/// then converts the result back to BV via `fp_to_ieee_bv`.
/// Returns `None` for unsupported widths or non-arithmetic ops.
pub(in crate::codegen_ay) fn bv_float_binop(
    op: BinOp,
    lhs: Expr,
    rhs: Expr,
    width: u32,
) -> Option<Expr> {
    let (eb, sb) = float_width_to_eb_sb(width)?;
    let fp_lhs = bv_to_ieee_fp(lhs, eb, sb);
    let fp_rhs = bv_to_ieee_fp(rhs, eb, sb);
    let fp_result = match op {
        BinOp::Add | BinOp::AddUnchecked => fp_lhs.fp_add(RoundingMode::RNE, fp_rhs),
        BinOp::Sub | BinOp::SubUnchecked => fp_lhs.fp_sub(RoundingMode::RNE, fp_rhs),
        BinOp::Mul | BinOp::MulUnchecked => fp_lhs.fp_mul(RoundingMode::RNE, fp_rhs),
        BinOp::Div => fp_lhs.fp_div(RoundingMode::RNE, fp_rhs),
        BinOp::Rem => fp_lhs.fp_rem(fp_rhs),
        _ => return None,
    };
    Some(fp_result.fp_to_ieee_bv())
}

/// CHC-safe float BinOp: constant-fold when both operands are concrete bit
/// patterns, fail closed otherwise.
///
/// PDR cannot reason about FP theory terms in CHC bodies, so the BMC path's
/// `bv_to_ieee_fp → fp_op → fp_to_ieee_bv` round-trip is unavailable here.
/// The previous behavior was to drop through to BV integer arithmetic for
/// symbolic operands; those BV ops do not respect IEEE 754 semantics and let
/// the solver build false counterexamples (issue 1739, family 2 — six
/// FastMath/SIMD/FloatingPoint harnesses produced spurious CTREX).
///
/// Returning `None` for symbolic operands makes this constant-fold lane fail
/// closed instead of synthesizing definite-but-wrong arithmetic. The main
/// CHC translation sites layer a congruent unconstrained-table lane on top
/// via `ChcCtx::float_binop_chc_term` (chc/float_binop_table.rs, sound for
/// proofs + Kani --nan-check parity obligation); direct callers (SIMD lanes,
/// inline stubs) keep the bare fail-closed behavior.
pub(in crate::codegen_ay) fn bv_float_binop_chc(
    op: BinOp,
    lhs: Expr,
    rhs: Expr,
    width: u32,
) -> Option<Expr> {
    let (ExprValue::BitVecConst { value: l, .. }, ExprValue::BitVecConst { value: r, .. }) =
        (lhs.value(), rhs.value())
    else {
        return None;
    };
    let (lb, rb) = (u64::try_from(l).ok()?, u64::try_from(r).ok()?);

    macro_rules! fold {
        ($a:expr, $b:expr) => {
            match op {
                BinOp::Add | BinOp::AddUnchecked => $a + $b,
                BinOp::Sub | BinOp::SubUnchecked => $a - $b,
                BinOp::Mul | BinOp::MulUnchecked => $a * $b,
                BinOp::Div => $a / $b,
                BinOp::Rem => $a % $b,
                _ => return None,
            }
        };
    }
    // Only f32/f64 widths constant-fold precisely. f16/f128 have no native
    // host representation; fail closed rather than approximate via f32/f64.
    let bits: u64 = match width {
        32 => fold!(f32::from_bits(lb as u32), f32::from_bits(rb as u32)).to_bits() as u64,
        64 => fold!(f64::from_bits(lb), f64::from_bits(rb)).to_bits(),
        _ => return None,
    };
    // Normalize -0.0 to +0.0 so downstream BV equality compares correctly
    // for IEEE float zero (the two patterns are IEEE-equal but BV-distinct).
    let bits = match width {
        32 if bits as u32 == 0x8000_0000 => 0,
        64 if bits == 0x8000_0000_0000_0000 => 0,
        _ => bits,
    };
    Some(Expr::bitvec_const(bits as i128, width))
}

/// Map float BV width to (exponent_bits, significand_bits) per IEEE 754. Part of #3857.
pub(in crate::codegen_ay) fn float_width_to_eb_sb(width: u32) -> Option<(u32, u32)> {
    match width {
        16 => Some((5, 11)),    // f16
        32 => Some((8, 24)),    // f32
        64 => Some((11, 53)),   // f64
        128 => Some((15, 113)), // f128
        _ => None,
    }
}

pub(in crate::codegen_ay) fn unsigned_max_bits(width: u32) -> u128 {
    if width == 128 { u128::MAX } else { (1u128 << width) - 1 }
}

pub(in crate::codegen_ay) fn signed_max_bits(width: u32) -> u128 {
    if width == 128 { i128::MAX as u128 } else { (1u128 << (width - 1)) - 1 }
}

pub(in crate::codegen_ay) fn int_max_bits(width: u32, signed: bool) -> u128 {
    if signed { signed_max_bits(width) } else { unsigned_max_bits(width) }
}

pub(in crate::codegen_ay) fn int_min_bits(width: u32, signed: bool) -> u128 {
    if signed { 1u128 << (width - 1) } else { 0 }
}

/// Int→float conversion via FP theory (Rust `u32 as f32` semantics). Part of #3465.
pub(in crate::codegen_ay) fn int_to_float_bv(
    src: Expr,
    signed: bool,
    target_float_width: u32,
) -> Option<Expr> {
    let (eb, sb) = float_width_to_eb_sb(target_float_width)?;
    let fp = if signed {
        src.bv_to_fp(RoundingMode::RNE, eb, sb)
    } else {
        src.bv_to_fp_unsigned(RoundingMode::RNE, eb, sb)
    };
    Some(fp.fp_to_ieee_bv())
}

/// Pure-BV int→float conversion (CHC-compatible, avoids FP rounding-mode terms). Part of #3465.
pub(in crate::codegen_ay) fn int_to_float_bv_pure(
    src: Expr,
    signed: bool,
    target_float_width: u32,
) -> Option<Expr> {
    let (eb, sb) = float_width_to_eb_sb(target_float_width)?;
    let mant_bits = sb - 1; // stored mantissa bits (23 for f32, 52 for f64)
    let total_width = eb + sb; // 32 for f32, 64 for f64
    let bias = (1u64 << (eb - 1)) - 1; // 127 for f32, 1023 for f64
    let src_width = src.sort().bitvec_width()?;

    // Work in a width large enough for all intermediate computations.
    // Need at least mant_bits+2 for overflow detection after rounding.
    let work_width = src_width.max(total_width).max(mant_bits + 2);

    // Step 1: Handle signed — extract sign, compute unsigned magnitude.
    let (sign_bit, magnitude) = if signed {
        let msb = src.clone().extract(src_width - 1, src_width - 1);
        let is_neg = msb.clone().eq(Expr::bitvec_const(1u64, 1));
        let neg_src = src.clone().bvneg();
        let mag = Expr::ite(is_neg, neg_src, src);
        (msb, mag)
    } else {
        (Expr::bitvec_const(0u64, 1), src)
    };

    // Widen magnitude to work_width.
    let mag_wide = if src_width < work_width {
        magnitude.zero_extend(work_width - src_width)
    } else {
        magnitude
    };

    // Step 2: Handle zero case.
    let zero_wide = Expr::bitvec_const(0u64, work_width);
    let is_zero = mag_wide.clone().eq(zero_wide.clone());

    // Step 3: Find MSB position (0-indexed from LSB) via ITE cascade.
    // Check all src_width bits of the magnitude (handles signed INT_MIN where
    // negation wraps and bit src_width-1 is still set).
    let mut msb_pos = Expr::bitvec_const(0u64, work_width);
    for i in 1..src_width {
        let bit_i = mag_wide.clone().extract(i, i);
        let bit_is_one = bit_i.eq(Expr::bitvec_const(1u64, 1));
        msb_pos = Expr::ite(bit_is_one, Expr::bitvec_const(i as u64, work_width), msb_pos);
    }

    // Step 4: Compute biased exponent.
    let biased_exp = msb_pos.clone().bvadd(Expr::bitvec_const(bias, work_width));

    // Step 5: Compute significand.
    // Shift mag_wide so the hidden 1-bit (at MSB position) lands at bit mant_bits.
    // If msb_pos <= mant_bits: left-shift by (mant_bits - msb_pos), exact
    // If msb_pos > mant_bits: right-shift by (msb_pos - mant_bits), needs rounding
    let mant_bv = Expr::bitvec_const(mant_bits as u64, work_width);
    let one_bv = Expr::bitvec_const(1u64, work_width);
    let needs_rounding = msb_pos.clone().bvugt(mant_bv.clone());

    // Exact case: shift left to align hidden bit at mant_bits.
    let left_shift = mant_bv.clone().bvsub(msb_pos.clone());
    let exact_aligned = mag_wide.clone().bvshl(left_shift);

    // Rounding case: shift right, then apply round-to-nearest-even.
    let right_shift = msb_pos.bvsub(mant_bv);
    let truncated = mag_wide.clone().bvlshr(right_shift.clone());

    // RNE rounding bits:
    // guard_pos = right_shift - 1 (position of first dropped bit)
    let guard_pos = right_shift.bvsub(one_bv.clone());
    let guard_bit = mag_wide.clone().bvlshr(guard_pos.clone()).bvand(one_bv.clone());

    // sticky = OR of all bits below guard position
    // sticky_mask = (1 << guard_pos) - 1
    // When right_shift == 1, guard_pos == 0, sticky_mask == 0 (no sticky bits).
    let sticky_mask = one_bv.clone().bvshl(guard_pos).bvsub(one_bv.clone());
    let sticky_raw = mag_wide.bvand(sticky_mask);
    let sticky_nonzero = Expr::ite(
        sticky_raw.eq(zero_wide.clone()),
        Expr::bitvec_const(0u64, work_width),
        one_bv.clone(),
    );

    // LSB of truncated result (for tie-breaking: ties round to even).
    let lsb = truncated.clone().bvand(one_bv.clone());

    // RNE: round up if guard=1 AND (sticky!=0 OR lsb=1)
    let round_up = Expr::ite(
        guard_bit.eq(one_bv.clone()),
        // Guard is 1: check if we round up
        Expr::ite(
            sticky_nonzero.bvor(lsb).eq(zero_wide.clone()),
            zero_wide.clone(), // Exact tie with even LSB → round down
            one_bv,            // Not a tie, or tie with odd LSB → round up
        ),
        zero_wide, // Guard is 0 → round down
    );

    let rounded = truncated.bvadd(round_up);

    // Select exact or rounded based on whether precision was lost.
    let aligned = Expr::ite(needs_rounding, rounded, exact_aligned);

    // Detect rounding overflow: if the hidden 1-bit shifted from mant_bits to
    // mant_bits+1, the significand wrapped to 0 and exponent must increment.
    // In the exact case, bit mant_bits+1 is always 0 (no overflow possible).
    let overflow = aligned.clone().extract(mant_bits + 1, mant_bits + 1);
    let overflow_wide = overflow.zero_extend(work_width - 1);
    let final_exp = biased_exp.bvadd(overflow_wide);

    // Extract final IEEE 754 fields.
    let sig_bits = aligned.extract(mant_bits - 1, 0); // mant_bits wide
    let exp_bits = final_exp.extract(eb - 1, 0); // eb wide

    // Assemble: sign(1) ++ exponent(eb) ++ significand(mant_bits)
    let result = sign_bit.concat(exp_bits).concat(sig_bits);

    // If zero, return IEEE +0.0 (all zeros).
    let zero_result = Expr::bitvec_const(0u64, total_width);
    Some(Expr::ite(is_zero, zero_result, result))
}

/// Convert a BV-encoded IEEE 754 float to an integer BV via FP theory.
///
/// Performs float→int conversion using AY's native FP-to-BV operation with
/// Round-Toward-Zero (truncation), matching Rust's `as` and `float_to_int_unchecked`
/// semantics. Uses `fp_to_sbv` (signed) or `fp_to_ubv` (unsigned).
///
/// This is the inverse of `int_to_float_bv` and uses the same FP theory,
/// enabling AY to prove round-trip identities like `u as f32 == f.trunc()`.
///
/// Part of #3465: FP-theory float-to-int for round-trip proofs.
pub(in crate::codegen_ay) fn float_to_int_bv(
    src: Expr,
    target_width: u32,
    signed: bool,
) -> Option<Expr> {
    let src_width = src.sort().bitvec_width()?;
    let (eb, sb) = float_width_to_eb_sb(src_width)?;
    let fp = bv_to_ieee_fp(src, eb, sb);
    let int_bv = if signed {
        fp.fp_to_sbv(RoundingMode::RTZ, target_width)
    } else {
        fp.fp_to_ubv(RoundingMode::RTZ, target_width)
    };
    Some(int_bv)
}

/// Convert a BV-encoded IEEE 754 float to an integer BV with Rust `as`
/// saturation semantics for NaN, infinities, and out-of-range values.
///
/// Part of #3787: fallback saturating cast lane for FloatToInt.
pub(in crate::codegen_ay) fn float_to_int_saturating_bv(
    src: Expr,
    target_width: u32,
    signed: bool,
) -> Option<Expr> {
    let truncated = float_to_int_bv(src.clone(), target_width, signed)?;
    let src_width = src.sort().bitvec_width()?;
    let (eb, sb) = float_width_to_eb_sb(src_width)?;
    let fp = bv_to_ieee_fp(src, eb, sb);
    let fp_sort = fp.sort().clone();

    let zero = Expr::bitvec_const(0u128, target_width);
    let int_min = Expr::bitvec_const(int_min_bits(target_width, signed), target_width);
    let int_max = Expr::bitvec_const(int_max_bits(target_width, signed), target_width);

    let min_bound = if signed {
        int_min.clone().bv_to_fp(RoundingMode::RNE, eb, sb)
    } else {
        zero.clone().bv_to_fp_unsigned(RoundingMode::RNE, eb, sb)
    };
    let max_bound = if signed {
        int_max.clone().bv_to_fp(RoundingMode::RNE, eb, sb)
    } else {
        int_max.clone().bv_to_fp_unsigned(RoundingMode::RNE, eb, sb)
    };

    let is_nan = fp.clone().fp_is_nan();
    let is_pos_inf = fp.clone().fp_eq(Expr::fp_plus_infinity(&fp_sort));
    let is_neg_inf = fp.clone().fp_eq(Expr::fp_minus_infinity(&fp_sort));
    let above_max = fp.clone().fp_gt(max_bound);
    let below_min = fp.fp_lt(min_bound);

    Some(Expr::ite(
        is_nan,
        zero,
        Expr::ite(
            is_pos_inf,
            int_max.clone(),
            Expr::ite(
                is_neg_inf,
                int_min.clone(),
                Expr::ite(above_max, int_max, Expr::ite(below_min, int_min, truncated)),
            ),
        ),
    ))
}

/// Truncate a BV-encoded IEEE 754 float toward zero via FP theory.
/// Convert a BV-encoded IEEE 754 float between widths via FP theory.
///
/// Implements `f as f64` / `f as f32` semantics: BV→FP→fp_to_fp(RNE)→BV.
/// Used for FloatToFloat casts in the CHC path.
pub(in crate::codegen_ay) fn float_to_float_bv(
    src: Expr,
    src_width: u32,
    target_width: u32,
) -> Option<Expr> {
    let (src_eb, src_sb) = float_width_to_eb_sb(src_width)?;
    let (tgt_eb, tgt_sb) = float_width_to_eb_sb(target_width)?;
    let fp = bv_to_ieee_fp(src, src_eb, src_sb);
    if src_width == target_width {
        // Same width: identity (e.g., f32→f32 used by trunc MIR lowering)
        return Some(fp.fp_to_ieee_bv());
    }
    let converted = fp.fp_to_fp(RoundingMode::RNE, tgt_eb, tgt_sb);
    Some(converted.fp_to_ieee_bv())
}

// Re-export pure-BV cast functions from sibling module (Part of #3870).
pub(in crate::codegen_ay) use super::float_arithmetic_pure::float_to_float_bv_pure;
pub(in crate::codegen_ay) use super::float_arithmetic_pure::float_to_int_bv_pure;

/// Returns true if the given BinOp is a float arithmetic operation that
/// should be routed through FP theory.
pub(in crate::codegen_ay) fn is_float_arithmetic_op(op: BinOp) -> bool {
    matches!(
        op,
        BinOp::Add
            | BinOp::AddUnchecked
            | BinOp::Sub
            | BinOp::SubUnchecked
            | BinOp::Mul
            | BinOp::MulUnchecked
            | BinOp::Div
            | BinOp::Rem
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_bindings::Expr;

    #[test]
    fn test_int_to_float_bv_u32_42_to_f32() {
        let src = Expr::bitvec_const(42u64, 32);
        let result = int_to_float_bv(src, false, 32).expect("f32 supported");
        assert_eq!(result.sort().bitvec_width(), Some(32));
    }

    #[test]
    fn test_int_to_float_bv_i32_neg1_to_f32() {
        let src = Expr::bitvec_const(0xFFFF_FFFFu64, 32);
        let result = int_to_float_bv(src, true, 32).expect("f32 supported");
        assert_eq!(result.sort().bitvec_width(), Some(32));
    }

    #[test]
    fn test_int_to_float_bv_u64_to_f64() {
        let src = Expr::bitvec_const(100u64, 64);
        let result = int_to_float_bv(src, false, 64).expect("f64 supported");
        assert_eq!(result.sort().bitvec_width(), Some(64));
    }

    #[test]
    fn test_int_to_float_bv_f16_supported() {
        let src = Expr::bitvec_const(1u64, 16);
        let result = int_to_float_bv(src, false, 16).expect("f16 now supported");
        assert_eq!(result.sort().bitvec_width(), Some(16));
    }

    #[test]
    fn test_float_width_to_eb_sb() {
        assert_eq!(float_width_to_eb_sb(16), Some((5, 11)));
        assert_eq!(float_width_to_eb_sb(32), Some((8, 24)));
        assert_eq!(float_width_to_eb_sb(64), Some((11, 53)));
        assert_eq!(float_width_to_eb_sb(128), Some((15, 113)));
        assert_eq!(float_width_to_eb_sb(80), None); // x87 extended not supported
    }

    #[test]
    fn test_float_to_float_bv_same_width() {
        let bv = Expr::bitvec_const(0x42280000u64, 32); // 42.0f32
        let result = float_to_float_bv(bv, 32, 32).expect("same-width");
        assert_eq!(result.sort().bitvec_width(), Some(32));
    }

    #[test]
    fn test_float_to_float_bv_f32_to_f64() {
        let bv = Expr::bitvec_const(0x42280000u64, 32); // 42.0f32
        let result = float_to_float_bv(bv, 32, 64).expect("f32→f64");
        assert_eq!(result.sort().bitvec_width(), Some(64));
    }

    #[test]
    fn test_float_to_float_bv_f64_to_f32() {
        let bv = Expr::bitvec_const(0x4045000000000000u64, 64); // 42.0f64
        let result = float_to_float_bv(bv, 64, 32).expect("f64→f32");
        assert_eq!(result.sort().bitvec_width(), Some(32));
    }
}
#[cfg(test)]
#[path = "float_arithmetic_saturating_tests.rs"]
mod float_arithmetic_saturating_tests;
