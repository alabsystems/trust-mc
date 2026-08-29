// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-expect: PROOF
//
//! Test for struct field signedness handling (#672).
//!
//! Verifies that struct field comparisons use the correct signedness
//! based on the field's type, not the struct's type.

struct Mixed {
    signed: i32,
    unsigned: u32,
}

/// Test that signed struct field comparison works correctly.
/// The field `m.signed` is i32, so -1 < 0 should be true.
#[kani::proof]
fn test_signed_field_comparison() {
    let m = Mixed { signed: -1, unsigned: 0 };
    // This should be true: -1 < 0 for signed i32
    kani::assert(m.signed < 0, "signed field -1 should be less than 0");
}

/// Test that unsigned struct field comparison works correctly.
/// The field `m.unsigned` wrapping around should still be >= 0.
#[kani::proof]
fn test_unsigned_field_comparison() {
    let m = Mixed { signed: 0, unsigned: 0xFFFFFFFF };
    // u32 is always >= 0 (unsigned)
    kani::assert(m.unsigned >= 0, "unsigned field should always be >= 0");
}

/// Test mixed field comparisons in the same struct.
#[kani::proof]
fn test_mixed_fields() {
    let m = Mixed { signed: -5, unsigned: 5 };
    // -5 is less than 0 for signed
    kani::assert(m.signed < 0, "-5i32 < 0 should be true");
    // 5 is >= 0 for unsigned
    kani::assert(m.unsigned >= 0, "5u32 >= 0 should be true");
}

/// Tuple with mixed signedness fields.
#[kani::proof]
fn test_tuple_field_signedness() {
    let t: (i32, u32) = (-10, 10);
    // i32 field: -10 < 0 should be true
    kani::assert(t.0 < 0, "-10i32 < 0 should be true");
    // u32 field: 10 >= 0 should be true
    kani::assert(t.1 >= 0, "10u32 >= 0 should be true");
}
