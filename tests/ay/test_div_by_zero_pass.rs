// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-expect: BMC_SAFE
//
//! Test case for division-by-zero checks (#61).
//!
//! Pass-only harnesses for div-by-zero safety properties.
//!
//! Split from test_div_by_zero.rs per #1121: compiletest marks files as pass/fail.

/// This test should PASS - divisor is constrained to be non-zero
/// and signed overflow is guarded (INT_MIN / -1).
#[kani::proof]
fn test_div_guarded_pass() {
    let x: i32 = kani::any();
    let y: i32 = kani::any();
    kani::assume(y != 0);
    // Guard against signed overflow: INT_MIN / -1 overflows because |INT_MIN| > INT_MAX
    kani::assume(!(x == i32::MIN && y == -1));

    // Safe division - y is non-zero and no overflow
    let _result = x / y;
}

/// This test should PASS - remainder with non-zero divisor.
#[kani::proof]
fn test_rem_guarded_pass() {
    let x: u32 = kani::any();
    let y: u32 = kani::any();
    kani::assume(y != 0);

    // Safe remainder - y is known to be non-zero
    let _result = x % y;
}

/// Test that division by a known non-zero constant is safe.
#[kani::proof]
fn test_div_by_constant_pass() {
    let x: i32 = kani::any();

    // Division by constant 5 is always safe
    let _result = x / 5;
}

/// Test signed division with both div-by-zero and overflow guards.
#[kani::proof]
fn test_signed_div_guarded_pass() {
    let x: i64 = kani::any();
    let y: i64 = kani::any();
    kani::assume(y != 0);
    // Guard against signed overflow: INT_MIN / -1 overflows because |INT_MIN| > INT_MAX
    kani::assume(!(x == i64::MIN && y == -1));

    let _result = x / y;
}

/// Test u8 division (different bitvector width).
#[kani::proof]
fn test_u8_div_guarded_pass() {
    let x: u8 = kani::any();
    let y: u8 = kani::any();
    kani::assume(y != 0);

    let _result = x / y;
    let _rem = x % y;
}
