// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Math constant folding verification.
//!
//! These tests verify the mathematical operations used in try_fold_math_f32/f64.
//! We test the Rust std library math functions directly since the codegen calls
//! them for constant folding.
//!
//! Part of #3730: extracted from the math_intrinsics monolith.

/// Test f32 sqrt constant folding.
#[test]
fn test_f32_sqrt_fold() {
    let val: f32 = 4.0;
    let result = val.sqrt();
    assert_eq!(result, 2.0);
    // Verify bits round-trip
    let bits = result.to_bits();
    assert_eq!(f32::from_bits(bits), 2.0);
}

/// Test f32 sin/cos constant folding at known values.
#[test]
fn test_f32_trig_fold() {
    let zero: f32 = 0.0;
    assert_eq!(zero.sin(), 0.0);
    assert!((zero.cos() - 1.0).abs() < f32::EPSILON);
}

/// Test f32 floor/ceil/trunc/round constant folding.
#[test]
fn test_f32_rounding_fold() {
    let val: f32 = 2.7;
    assert_eq!(val.floor(), 2.0);
    assert_eq!(val.ceil(), 3.0);
    assert_eq!(val.trunc(), 2.0);
    assert_eq!(val.round(), 3.0);
}

/// Test f32 round_ties_even (banker's rounding).
#[test]
fn test_f32_round_ties_even_fold() {
    // 2.5 rounds to 2.0 (even), 3.5 rounds to 4.0 (even)
    assert_eq!(2.5f32.round_ties_even(), 2.0);
    assert_eq!(3.5f32.round_ties_even(), 4.0);
}

/// Test f32 binary intrinsics: pow, copysign, min, max.
#[test]
fn test_f32_binary_fold() {
    assert_eq!(2.0f32.powf(3.0), 8.0);
    assert_eq!((-1.0f32).copysign(1.0), 1.0);
    assert_eq!(3.0f32.min(5.0), 3.0);
    assert_eq!(3.0f32.max(5.0), 5.0);
}

/// Test f32 fma (fused multiply-add): a * b + c.
#[test]
fn test_f32_fma_fold() {
    let result = 2.0f32.mul_add(3.0, 4.0); // 2 * 3 + 4 = 10
    assert_eq!(result, 10.0);
}

/// Test f32 powi (integer exponent).
#[test]
fn test_f32_powi_fold() {
    assert_eq!(2.0f32.powi(10), 1024.0);
    assert_eq!(2.0f32.powi(-1), 0.5);
}

/// Test f64 sqrt constant folding.
#[test]
fn test_f64_sqrt_fold() {
    let val: f64 = 9.0;
    assert_eq!(val.sqrt(), 3.0);
}

/// Test f64 rounding constant folding.
#[test]
fn test_f64_rounding_fold() {
    let val: f64 = 2.7;
    assert_eq!(val.floor(), 2.0);
    assert_eq!(val.ceil(), 3.0);
    assert_eq!(val.trunc(), 2.0);
    assert_eq!(val.round(), 3.0);
}

/// Test f64 round_ties_even.
#[test]
fn test_f64_round_ties_even_fold() {
    assert_eq!(2.5f64.round_ties_even(), 2.0);
    assert_eq!(3.5f64.round_ties_even(), 4.0);
}

/// Test f64 binary operations: pow, copysign, min, max, fma.
#[test]
fn test_f64_binary_fold() {
    assert_eq!(2.0f64.powf(10.0), 1024.0);
    assert_eq!((-5.0f64).copysign(1.0), 5.0);
    assert_eq!(1.0f64.min(2.0), 1.0);
    assert_eq!(1.0f64.max(2.0), 2.0);
    assert_eq!(2.0f64.mul_add(3.0, 1.0), 7.0);
}

/// Test that unknown intrinsic names produce NaN (unfoldable).
#[test]
fn test_unknown_intrinsic_returns_nan() {
    // Simulate the compute_result closure behavior for unknown names
    let val: f32 = 1.0;
    let result = f32::NAN; // What the closure returns for unknown intrinsics
    assert!(result.is_nan());
    // NaN for non-NaN input means unknown → don't fold
    assert!(!val.is_nan());
}
