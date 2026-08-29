// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-expect: PROOF
// NOTE: test_ordering_discriminant_cast gained PROOF at ay 8a4a9bcc2.
//
//! Integration tests for signed enum repr signedness (#3262).
//!
//! `std::cmp::Ordering` uses `#[repr(i8)]` with `Less=-1, Equal=0, Greater=1`.
//! When Ordering discriminant values are cast and compared, the signedness of
//! the BV operations must respect the repr type. With unsigned semantics,
//! `Less as i8` (-1 → 0xFF) would compare greater than `Equal as i8` (0),
//! producing unsound results.

use std::cmp::Ordering;

/// Verify that cmp returns Equal for identical values (baseline).
#[kani::proof]
fn test_signed_enum_cmp_equal() {
    let a: i8 = 5;
    let b: i8 = 5;
    let result = a.cmp(&b);
    kani::assert(result == Ordering::Equal, "cmp(5, 5) should be Equal");
}

/// Verify that i8::cmp correctly returns Less for negative < positive.
/// This exercises signed comparison on signed integer types.
#[kani::proof]
fn test_signed_enum_cmp_negative() {
    let a: i8 = -5;
    let b: i8 = 3;
    let result = a.cmp(&b);
    kani::assert(result == Ordering::Less, "cmp(-5, 3) should be Less");
}

/// Verify that Ordering discriminant cast preserves signed semantics.
/// `Ordering::Less as i8` should be -1, and -1 < 0 requires signed comparison.
#[kani::proof]
fn test_ordering_discriminant_cast() {
    let less_val = Ordering::Less as i8;
    let equal_val = Ordering::Equal as i8;
    kani::assert(less_val == -1, "Ordering::Less should be -1 as i8");
    kani::assert(equal_val == 0, "Ordering::Equal should be 0 as i8");
}

/// Verify width-changing cast: Ordering::Less as i32 must sign-extend.
/// BV(8) 0xFF → BV(32): sign-extend → 0xFFFFFFFF (-1), not zero-extend → 0xFF (255).
/// Exercises ty_signedness_for_cast enum repr path (Part of #3262).
#[kani::proof]
fn test_ordering_widen_cast_signed() {
    let less_wide = Ordering::Less as i32;
    let greater_wide = Ordering::Greater as i32;
    kani::assert(less_wide == -1, "Ordering::Less as i32 should be -1");
    kani::assert(greater_wide == 1, "Ordering::Greater as i32 should be 1");
}
