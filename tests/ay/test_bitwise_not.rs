// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-expect: PROOF
// kani-flags: --ay-chc-transform
// NOTE: All 4 harnesses are PROOF at ay e1c70f4a.
//
//! Test case for bitwise NOT on integers (#77)
//!
//! This tests that `!x` on an integer uses bvnot (returns same type)
//! while `!x` on a boolean uses logical not (returns bool).

#[kani::proof]
fn test_bitwise_not_u8() {
    let x: u8 = kani::any();
    kani::assume(x == 0xFF);

    let result = !x;
    // !0xFF should be 0x00
    assert!(result == 0x00);
}

#[kani::proof]
fn test_bitwise_not_u32() {
    let x: u32 = kani::any();
    kani::assume(x == 0);

    let result = !x;
    // !0 should be 0xFFFFFFFF
    assert!(result == 0xFFFFFFFF);
}

#[kani::proof]
fn test_logical_not_bool() {
    let x: bool = kani::any();
    kani::assume(x == true);

    let result = !x;
    // !true should be false
    assert!(result == false);
}

#[kani::proof]
fn test_bitwise_not_preserves_type() {
    let x: i32 = kani::any();
    kani::assume(x >= 0 && x < 256);

    // Bitwise NOT should return an i32, not a bool
    let result: i32 = !x;

    // Result should be the bitwise complement
    // For any non-negative value, the result will be negative
    assert!(result < 0 || x < 0);
}
