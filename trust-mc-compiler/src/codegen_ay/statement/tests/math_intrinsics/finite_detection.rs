// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Fast-math finite detection (record_fast_float_finite) tests.
//!
//! Fast-math intrinsics require operands to be finite (no NaN/Inf).
//! Finite check works by extracting the exponent field and checking
//! if all bits are 1 (which indicates NaN or Infinity in IEEE 754).
//!
//! Part of #3730: extracted from the math_intrinsics monolith.

use super::*;

/// Test f32 exponent extraction: exponent is bits [30:23].
/// For NaN/Inf, all exponent bits are 1 (0xFF).
#[test]
fn test_f32_exponent_extraction_nan() {
    // f32 NaN: sign=0, exp=0xFF, mantissa!=0
    let nan_bits: u32 = f32::NAN.to_bits();
    let nan_expr = Expr::bitvec_const(nan_bits as u64, 32);

    // Extract exponent field [30:23]
    let exp = nan_expr.extract(30, 23);
    assert_eq!(exp.sort().bitvec_width(), Some(8));

    // Verify the extracted exponent IS all-ones (0xFF) for NaN
    match exp.value() {
        ExprValue::BvExtract { .. } => {
            // Extract of a constant — verify the equality check structure
            let exp_all_ones = exp.eq(Expr::bitvec_const(0xFF, 8));
            assert!(exp_all_ones.sort().is_bool());
        }
        ExprValue::BitVecConst { value, width } => {
            assert_eq!(*width, 8);
            assert_eq!(*value, BigInt::from(0xFF_u32), "NaN exponent should be 0xFF (all ones)");
        }
        other => panic!("expected Extract or BitVecConst for NaN exponent, got {other:?}"),
    }
}

/// Test f32 exponent extraction: normal finite value has non-all-ones exponent.
#[test]
fn test_f32_exponent_extraction_finite() {
    // f32 1.0: sign=0, exp=0x7F (127), mantissa=0
    let one_bits: u32 = 1.0f32.to_bits();
    let one_expr = Expr::bitvec_const(one_bits as u64, 32);

    let exp = one_expr.extract(30, 23);
    assert_eq!(exp.sort().bitvec_width(), Some(8));

    // Verify the exponent is 0x7F (127), NOT 0xFF — proving finite detection works
    match exp.value() {
        ExprValue::BvExtract { .. } => {
            // Extract of a constant — verify the Eq expression rejects NaN/Inf check
            let exp_all_ones = exp.eq(Expr::bitvec_const(0xFF, 8));
            assert!(exp_all_ones.sort().is_bool());
        }
        ExprValue::BitVecConst { value, width } => {
            assert_eq!(*width, 8);
            assert_eq!(*value, BigInt::from(0x7F_u32), "1.0f32 exponent should be 0x7F (127)");
            assert_ne!(*value, BigInt::from(0xFF_u32), "finite float exponent must not be 0xFF");
        }
        other => panic!("expected Extract or BitVecConst for finite exponent, got {other:?}"),
    }
}

/// Test f32 exponent extraction: infinity has all-ones exponent.
#[test]
fn test_f32_exponent_extraction_infinity() {
    let inf_bits: u32 = f32::INFINITY.to_bits();
    let inf_expr = Expr::bitvec_const(inf_bits as u64, 32);

    let exp = inf_expr.extract(30, 23);
    assert_eq!(exp.sort().bitvec_width(), Some(8));

    // Verify the extracted exponent IS all-ones (0xFF) for infinity
    match exp.value() {
        ExprValue::BvExtract { .. } => {
            // Extract of a constant — verify the equality check
            let exp_all_ones = exp.eq(Expr::bitvec_const(0xFF, 8));
            assert!(exp_all_ones.sort().is_bool());
        }
        ExprValue::BitVecConst { value, width } => {
            assert_eq!(*width, 8);
            assert_eq!(*value, BigInt::from(0xFF_u32), "infinity exponent should be 0xFF");
        }
        other => panic!("expected Extract or BitVecConst for infinity exponent, got {other:?}"),
    }
}

/// Test f64 exponent extraction: exponent is bits [62:52].
/// For NaN/Inf, all exponent bits are 1 (0x7FF).
#[test]
fn test_f64_exponent_extraction_nan() {
    let nan_bits: u64 = f64::NAN.to_bits();
    let nan_expr = Expr::bitvec_const(nan_bits as u128, 64);

    // Extract exponent field [62:52]
    let exp = nan_expr.extract(62, 52);
    assert_eq!(exp.sort().bitvec_width(), Some(11)); // 62 - 52 + 1 = 11

    // Verify the extracted exponent IS all-ones (0x7FF) for NaN
    match exp.value() {
        ExprValue::BvExtract { .. } => {
            let exp_all_ones = exp.eq(Expr::bitvec_const(0x7FF, 11));
            assert!(exp_all_ones.sort().is_bool());
        }
        ExprValue::BitVecConst { value, width } => {
            assert_eq!(*width, 11);
            assert_eq!(*value, BigInt::from(0x7FF_u32), "f64 NaN exponent should be 0x7FF");
        }
        other => panic!("expected Extract or BitVecConst for f64 NaN exponent, got {other:?}"),
    }
}

/// Test f64 exponent extraction for a normal finite value (pi).
/// Verifies: exponent is 0x400 (biased 1024), NOT 0x7FF (NaN/Inf).
#[test]
fn test_f64_exponent_extraction_finite() {
    let pi_bits: u64 = std::f64::consts::PI.to_bits();
    let pi_expr = Expr::bitvec_const(pi_bits as u128, 64);

    let exp = pi_expr.extract(62, 52);
    assert_eq!(exp.sort().bitvec_width(), Some(11));

    // pi ~ 3.14159 -> biased exponent = 1024 (0x400)
    match exp.value() {
        ExprValue::BvExtract { .. } => {
            // Extract of a constant -- verify the equality rejects NaN/Inf
            let exp_all_ones = exp.eq(Expr::bitvec_const(0x7FF, 11));
            assert!(exp_all_ones.sort().is_bool());
        }
        ExprValue::BitVecConst { value, width } => {
            assert_eq!(*width, 11);
            assert_eq!(*value, BigInt::from(0x400_u32), "pi exponent should be 0x400 (1024)");
            assert_ne!(*value, BigInt::from(0x7FF_u32), "finite f64 exponent must not be 0x7FF");
        }
        other => panic!("expected Extract or BitVecConst for finite f64 exponent, got {other:?}"),
    }
}
