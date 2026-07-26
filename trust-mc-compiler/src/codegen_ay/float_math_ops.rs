// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! BMC/SMT-only FP-theory math operations for BV-encoded IEEE 754 floats.
//!
//! These functions use AY's native FP rounding-mode constants (RNE, RTZ, etc.)
//! and are therefore **not compatible with Z3's CHC fixedpoint parser**.
//! Use only on BMC/SMT solver paths — the CHC path has pure-BV alternatives
//! in `float_rounding.rs` (#3750) and `float_arithmetic.rs` (#3465).
//!
//! Split from `float_arithmetic.rs` to keep file sizes under 500 lines.
//! Part of #3094: BMC parity for math intrinsics.

use ay_bindings::{Expr, RoundingMode};

use super::float_arithmetic::{bv_to_ieee_fp, float_width_to_eb_sb};

/// Round a BV-encoded IEEE 754 float toward zero via FP theory.
///
/// Uses `fp.roundToIntegral(RTZ)`. BMC/SMT path only — Z3's CHC parser
/// rejects rounding-mode constants.
pub(in crate::codegen_ay) fn trunc_fp_bv(src: Expr, width: u32) -> Option<Expr> {
    let (eb, sb) = float_width_to_eb_sb(width)?;
    let fp = bv_to_ieee_fp(src, eb, sb);
    Some(fp.fp_round_to_integral(RoundingMode::RTZ).fp_to_ieee_bv())
}

/// Round a BV-encoded IEEE 754 float toward negative infinity via FP theory.
pub(in crate::codegen_ay) fn floor_fp_bv(src: Expr, width: u32) -> Option<Expr> {
    let (eb, sb) = float_width_to_eb_sb(width)?;
    let fp = bv_to_ieee_fp(src, eb, sb);
    Some(fp.fp_round_to_integral(RoundingMode::RTN).fp_to_ieee_bv())
}

/// Round a BV-encoded IEEE 754 float toward positive infinity via FP theory.
pub(in crate::codegen_ay) fn ceil_fp_bv(src: Expr, width: u32) -> Option<Expr> {
    let (eb, sb) = float_width_to_eb_sb(width)?;
    let fp = bv_to_ieee_fp(src, eb, sb);
    Some(fp.fp_round_to_integral(RoundingMode::RTP).fp_to_ieee_bv())
}

/// Round a BV-encoded IEEE 754 float to nearest, ties away from zero, via FP theory.
pub(in crate::codegen_ay) fn round_fp_bv(src: Expr, width: u32) -> Option<Expr> {
    let (eb, sb) = float_width_to_eb_sb(width)?;
    let fp = bv_to_ieee_fp(src, eb, sb);
    Some(fp.fp_round_to_integral(RoundingMode::RNA).fp_to_ieee_bv())
}

/// Round a BV-encoded IEEE 754 float to nearest, ties to even, via FP theory.
pub(in crate::codegen_ay) fn round_ties_even_fp_bv(src: Expr, width: u32) -> Option<Expr> {
    let (eb, sb) = float_width_to_eb_sb(width)?;
    let fp = bv_to_ieee_fp(src, eb, sb);
    Some(fp.fp_round_to_integral(RoundingMode::RNE).fp_to_ieee_bv())
}

/// Compute IEEE 754 minimum of two BV-encoded floats via FP theory.
pub(in crate::codegen_ay) fn minnum_fp_bv(a: Expr, b: Expr, width: u32) -> Option<Expr> {
    let (eb, sb) = float_width_to_eb_sb(width)?;
    let fp_a = bv_to_ieee_fp(a, eb, sb);
    let fp_b = bv_to_ieee_fp(b, eb, sb);
    Some(fp_a.fp_min(fp_b).fp_to_ieee_bv())
}

/// Compute IEEE 754 maximum of two BV-encoded floats via FP theory.
pub(in crate::codegen_ay) fn maxnum_fp_bv(a: Expr, b: Expr, width: u32) -> Option<Expr> {
    let (eb, sb) = float_width_to_eb_sb(width)?;
    let fp_a = bv_to_ieee_fp(a, eb, sb);
    let fp_b = bv_to_ieee_fp(b, eb, sb);
    Some(fp_a.fp_max(fp_b).fp_to_ieee_bv())
}

/// Compute IEEE 754 square root of a BV-encoded float via FP theory.
///
/// Reinterprets the input BV as FP, applies `fp.sqrt(RNE)`, converts back to BV.
/// Uses FP theory rounding mode — BMC/SMT path only.
pub(in crate::codegen_ay) fn sqrt_bv(src: Expr, width: u32) -> Option<Expr> {
    let (eb, sb) = float_width_to_eb_sb(width)?;
    let fp = bv_to_ieee_fp(src, eb, sb);
    Some(fp.fp_sqrt(RoundingMode::RNE).fp_to_ieee_bv())
}

/// Compute IEEE 754 fused multiply-add of BV-encoded floats via FP theory.
///
/// `fma(a, b, c) = a * b + c` with a single rounding step (IEEE 754-2008).
/// Uses FP theory rounding mode — BMC/SMT path only.
pub(in crate::codegen_ay) fn fma_bv(a: Expr, b: Expr, c: Expr, width: u32) -> Option<Expr> {
    let (eb, sb) = float_width_to_eb_sb(width)?;
    let fp_a = bv_to_ieee_fp(a, eb, sb);
    let fp_b = bv_to_ieee_fp(b, eb, sb);
    let fp_c = bv_to_ieee_fp(c, eb, sb);
    Some(fp_a.fp_fma(RoundingMode::RNE, fp_b, fp_c).fp_to_ieee_bv())
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_bindings::Expr;

    #[test]
    fn test_trunc_fp_bv_f32() {
        let bv = Expr::bitvec_const(0x40490FDBu64, 32); // ~3.14159f32
        let result = trunc_fp_bv(bv, 32).expect("f32 trunc");
        assert_eq!(result.sort().bitvec_width(), Some(32));
    }

    #[test]
    fn test_floor_fp_bv_f32() {
        let bv = Expr::bitvec_const(0x40490FDBu64, 32); // ~3.14159f32
        let result = floor_fp_bv(bv, 32).expect("f32 floor");
        assert_eq!(result.sort().bitvec_width(), Some(32));
    }

    #[test]
    fn test_ceil_fp_bv_f32() {
        let bv = Expr::bitvec_const(0x40490FDBu64, 32); // ~3.14159f32
        let result = ceil_fp_bv(bv, 32).expect("f32 ceil");
        assert_eq!(result.sort().bitvec_width(), Some(32));
    }

    #[test]
    fn test_minnum_fp_bv_f32() {
        let a = Expr::bitvec_const(0x40000000u64, 32); // 2.0f32
        let b = Expr::bitvec_const(0x40400000u64, 32); // 3.0f32
        let result = minnum_fp_bv(a, b, 32).expect("f32 minnum");
        assert_eq!(result.sort().bitvec_width(), Some(32));
    }

    #[test]
    fn test_maxnum_fp_bv_f32() {
        let a = Expr::bitvec_const(0x40000000u64, 32); // 2.0f32
        let b = Expr::bitvec_const(0x40400000u64, 32); // 3.0f32
        let result = maxnum_fp_bv(a, b, 32).expect("f32 maxnum");
        assert_eq!(result.sort().bitvec_width(), Some(32));
    }

    #[test]
    fn test_sqrt_bv_f32() {
        let bv = Expr::bitvec_const(0x40800000u64, 32); // 4.0f32
        let result = sqrt_bv(bv, 32).expect("f32 sqrt");
        assert_eq!(result.sort().bitvec_width(), Some(32));
    }

    #[test]
    fn test_sqrt_bv_f64() {
        let bv = Expr::bitvec_const(0x4010000000000000u64, 64); // 4.0f64
        let result = sqrt_bv(bv, 64).expect("f64 sqrt");
        assert_eq!(result.sort().bitvec_width(), Some(64));
    }

    #[test]
    fn test_fma_bv_f32() {
        let a = Expr::bitvec_const(0x40000000u64, 32); // 2.0f32
        let b = Expr::bitvec_const(0x40400000u64, 32); // 3.0f32
        let c = Expr::bitvec_const(0x3F800000u64, 32); // 1.0f32
        let result = fma_bv(a, b, c, 32).expect("f32 fma");
        assert_eq!(result.sort().bitvec_width(), Some(32));
    }

    #[test]
    fn test_sqrt_bv_f16_supported() {
        // f16 is supported via float_width_to_eb_sb.
        let bv = Expr::bitvec_const(0u64, 16);
        let result = sqrt_bv(bv, 16).expect("f16 sqrt");
        assert_eq!(result.sort().bitvec_width(), Some(16));
    }

    #[test]
    fn test_sqrt_bv_unsupported_width() {
        // x87 80-bit extended precision is still unsupported.
        let bv = Expr::bitvec_const(0u64, 80);
        assert!(sqrt_bv(bv, 80).is_none());
    }
}
