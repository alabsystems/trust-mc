// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-expect: PROOF
// NOTE: All 8 harnesses are PROOF at ay e1c70f4a.
//
//! Arithmetic overflow/wrapping edge-case tests with symbolic values.
//!
//! Verifies that the AY bitvector encoding correctly handles overflow,
//! underflow, wrapping, checked, and saturating arithmetic at type boundaries.
//! These harnesses use symbolic inputs (kani::any()) constrained to boundary
//! values to test the BV semantics, not just concrete evaluation.
//!
//! Results (ay e1c70f4a): All 8 harnesses PROOF.
//!   Previous CTREX (checked_add, checked_sub, saturating_add, neg_overflow)
//!   fixed by AY bump 3348639a and call dispatch improvements.
//!
//! Part of #3114.

/// Wrapping addition: u8::MAX + 1 wraps to 0.
#[kani::proof]
fn check_wrapping_add_overflow() {
    let x: u8 = kani::any();
    kani::assume(x == u8::MAX);
    let result = x.wrapping_add(1);
    kani::assert(result == 0, "u8::MAX wrapping_add 1 must be 0");
}

/// Wrapping subtraction: 0u8 - 1 wraps to u8::MAX.
#[kani::proof]
fn check_wrapping_sub_underflow() {
    let x: u8 = kani::any();
    kani::assume(x == 0);
    let result = x.wrapping_sub(1);
    kani::assert(result == u8::MAX, "0u8 wrapping_sub 1 must be u8::MAX");
}

/// Checked addition returns None at overflow boundary.
#[kani::proof]
fn check_checked_add_at_max() {
    let x: u32 = kani::any();
    kani::assume(x == u32::MAX);
    let result = x.checked_add(1);
    kani::assert(result.is_none(), "u32::MAX checked_add 1 must be None");

    // Non-overflow case: MAX-1 + 1 = MAX
    let y: u32 = kani::any();
    kani::assume(y == u32::MAX - 1);
    let result2 = y.checked_add(1);
    kani::assert(result2.is_some(), "u32::MAX-1 checked_add 1 must be Some");
    kani::assert(result2.unwrap() == u32::MAX, "u32::MAX-1 + 1 == u32::MAX");
}

/// Checked subtraction returns None at underflow boundary.
#[kani::proof]
fn check_checked_sub_at_zero() {
    let x: u32 = kani::any();
    kani::assume(x == 0);
    let result = x.checked_sub(1);
    kani::assert(result.is_none(), "0u32 checked_sub 1 must be None");

    // Non-underflow case: 1 - 1 = 0
    let y: u32 = kani::any();
    kani::assume(y == 1);
    let result2 = y.checked_sub(1);
    kani::assert(result2.is_some(), "1u32 checked_sub 1 must be Some");
    kani::assert(result2.unwrap() == 0, "1 - 1 == 0");
}

/// Saturating addition clamps at MAX instead of wrapping.
#[kani::proof]
fn check_saturating_add_at_max() {
    let x: u16 = kani::any();
    kani::assume(x == u16::MAX);
    let result = x.saturating_add(1);
    kani::assert(result == u16::MAX, "u16::MAX saturating_add 1 must stay at MAX");

    let y: u16 = kani::any();
    kani::assume(y == u16::MAX - 1);
    let result2 = y.saturating_add(1);
    kani::assert(result2 == u16::MAX, "u16::MAX-1 saturating_add 1 == MAX");
}

/// Mixed-width overflow: u8 widened to u32 then wrapping at u8 boundary.
#[kani::proof]
fn check_mixed_width_overflow() {
    let a: u8 = kani::any();
    kani::assume(a == 200);
    let b: u32 = a as u32;
    // Widened value fits in u32 (no overflow)
    kani::assert(b == 200, "widened u8 200 to u32 is 200");

    // Add in u32 domain, then truncate back to u8
    let sum_u32: u32 = b + 100;
    kani::assert(sum_u32 == 300, "200 + 100 in u32 domain is 300");
    let truncated: u8 = sum_u32 as u8;
    // 300 mod 256 = 44
    kani::assert(truncated == 44, "300 truncated to u8 is 44");
}

/// Signed wrapping: i8::MAX + 1 wraps to i8::MIN.
#[kani::proof]
fn check_signed_overflow_wrapping() {
    let x: i8 = kani::any();
    kani::assume(x == i8::MAX);
    let result = x.wrapping_add(1);
    kani::assert(result == i8::MIN, "i8::MAX wrapping_add 1 must be i8::MIN");

    // Also test i8::MIN - 1 wraps to i8::MAX
    let y: i8 = kani::any();
    kani::assume(y == i8::MIN);
    let result2 = y.wrapping_sub(1);
    kani::assert(result2 == i8::MAX, "i8::MIN wrapping_sub 1 must be i8::MAX");
}

/// Negation overflow: -i8::MIN is undefined (wraps to i8::MIN in Rust).
#[kani::proof]
fn check_neg_overflow() {
    let x: i8 = kani::any();
    kani::assume(x == i8::MIN);
    // i8::MIN.wrapping_neg() == i8::MIN because -(-128) overflows to -128 in 8-bit
    let result = x.wrapping_neg();
    kani::assert(result == i8::MIN, "i8::MIN wrapping_neg must be i8::MIN");

    // Non-overflow: -1 negates to 1
    let y: i8 = kani::any();
    kani::assume(y == -1);
    let result2 = y.wrapping_neg();
    kani::assert(result2 == 1, "-1 wrapping_neg must be 1");
}
