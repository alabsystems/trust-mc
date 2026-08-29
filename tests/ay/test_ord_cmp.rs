// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-expect: PROOF
// NOTE: All 6 harnesses are PROOF at ay e1c70f4a.
//
//! Integration tests for Ord::cmp method codegen (#359).
//!
//! Tests three-way comparison via the Ordering enum.

use std::cmp::Ordering;

/// Test u8::cmp returns Equal for same values.
#[kani::proof]
fn test_cmp_equal() {
    let a: u8 = 5;
    let b: u8 = 5;
    let result = a.cmp(&b);
    kani::assert(result == Ordering::Equal, "cmp(5, 5) should be Equal");
}

/// Test u8::cmp returns Less when lhs < rhs.
#[kani::proof]
fn test_cmp_less() {
    let a: u8 = 3;
    let b: u8 = 7;
    let result = a.cmp(&b);
    kani::assert(result == Ordering::Less, "cmp(3, 7) should be Less");
}

/// Test u8::cmp returns Greater when lhs > rhs.
#[kani::proof]
fn test_cmp_greater() {
    let a: u8 = 10;
    let b: u8 = 2;
    let result = a.cmp(&b);
    kani::assert(result == Ordering::Greater, "cmp(10, 2) should be Greater");
}

/// Test cmp with symbolic values.
#[kani::proof]
fn test_cmp_symbolic() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    kani::assume(a < b);
    let result = a.cmp(&b);
    kani::assert(result == Ordering::Less, "cmp(a, b) should be Less when a < b");
}

/// Test the Cast/main.rs pattern - unit enum cast and cmp.
/// This is the exact pattern from the original failing test.
pub enum Level {
    Error,
}

#[kani::proof]
fn test_cast_enum_cmp() {
    let left = Level::Error;
    // Level::Error has discriminant 0, so (left as u8) == 0
    // 0.cmp(&0) should return Ordering::Equal
    kani::assert((left as u8).cmp(&0) == Ordering::Equal, "cast enum cmp should be Equal");
}

/// Test i32::cmp for signed comparison.
#[kani::proof]
fn test_signed_cmp_negative() {
    let a: i32 = -5;
    let b: i32 = 3;
    let result = a.cmp(&b);
    kani::assert(result == Ordering::Less, "cmp(-5, 3) should be Less");
}
