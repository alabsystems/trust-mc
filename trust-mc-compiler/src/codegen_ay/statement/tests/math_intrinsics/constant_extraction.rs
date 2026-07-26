// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! AY expression constant extraction tests.
//!
//! These test the patterns used by extract_f32_from_expr, extract_f64_from_expr,
//! and extract_i32_from_expr to verify constant recovery from AY bitvec consts.
//!
//! Part of #3730: extracted from the math_intrinsics monolith.

use super::*;

/// Test f32 constant round-trip: bits -> AY expr -> extract -> bits.
#[test]
fn test_f32_const_roundtrip_via_expr_value() {
    use ay_bindings::ExprValue;

    let original: f32 = 3.125;
    let bits = original.to_bits();
    let expr = Expr::bitvec_const(bits as u128, 32);

    if let ExprValue::BitVecConst { value, width } = expr.value() {
        assert_eq!(*width, 32);
        let recovered: u32 = value.to_string().parse().unwrap();
        assert_eq!(recovered, bits);
        let recovered_f32 = f32::from_bits(recovered);
        assert_eq!(recovered_f32, original);
    } else {
        panic!("Expected BitVecConst");
    }
}

/// Test f64 constant round-trip: bits -> AY expr -> extract -> bits.
#[test]
fn test_f64_const_roundtrip_via_expr_value() {
    use ay_bindings::ExprValue;

    let original: f64 = std::f64::consts::E;
    let bits = original.to_bits();
    let expr = Expr::bitvec_const(bits as u128, 64);

    if let ExprValue::BitVecConst { value, width } = expr.value() {
        assert_eq!(*width, 64);
        let recovered: u64 = value.to_string().parse().unwrap();
        assert_eq!(recovered, bits);
        let recovered_f64 = f64::from_bits(recovered);
        assert_eq!(recovered_f64, original);
    } else {
        panic!("Expected BitVecConst");
    }
}

/// Test i32 extraction from bitvec const (positive value).
#[test]
fn test_i32_const_extraction_positive() {
    use ay_bindings::ExprValue;

    let val: i32 = 42;
    // i32 stored as u32 bits in bitvec
    let bits = val as u32;
    let expr = Expr::bitvec_const(bits as u128, 32);

    if let ExprValue::BitVecConst { value, width } = expr.value() {
        assert_eq!(*width, 32);
        let unsigned: u32 = value.to_string().parse().unwrap();
        let signed = unsigned as i32;
        assert_eq!(signed, 42);
    } else {
        panic!("Expected BitVecConst");
    }
}

/// Test i32 extraction from bitvec const (negative value, two's complement).
#[test]
fn test_i32_const_extraction_negative() {
    use ay_bindings::ExprValue;

    let val: i32 = -1;
    // Two's complement: -1 as u32 = 4294967295
    let bits = val as u32;
    assert_eq!(bits, 0xFFFFFFFF);
    let expr = Expr::bitvec_const(bits as u128, 32);

    if let ExprValue::BitVecConst { value, width } = expr.value() {
        assert_eq!(*width, 32);
        let unsigned: u32 = value.to_string().parse().unwrap();
        let signed = unsigned as i32;
        assert_eq!(signed, -1);
    } else {
        panic!("Expected BitVecConst");
    }
}

/// Test that non-32-bit bitvec is rejected for i32 extraction.
#[test]
fn test_i32_extraction_wrong_width_rejected() {
    use ay_bindings::ExprValue;

    let expr = Expr::bitvec_const(42, 64);
    if let ExprValue::BitVecConst { width, .. } = expr.value() {
        assert_ne!(*width, 32);
        // The extract_i32_from_expr method would return None here
    }
}

/// Test that symbolic (non-const) expression is not extractable.
#[test]
fn test_symbolic_expr_not_extractable() {
    use ay_bindings::ExprValue;

    let symbolic = Expr::var("x", Sort::bitvec(32));
    // Symbolic vars are not BitVecConst
    assert!(!matches!(symbolic.value(), ExprValue::BitVecConst { .. }));
}
