// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-expect: BMC_SAFE
//
//! Regression tests for mixed-width bitvector operations.
//!
//! Tests various edge cases for comparisons and casts between different
//! bitvector widths (u8, u32, u64, etc.). These catch issues like #190
//! (bitvector width mismatch panic) and #196 (signedness detection).
//!
//! Related issues: #189, #190, #196

// Regression test for #190: u64 SwitchInt with u32-ish case targets
#[kani::proof]
fn test_u64_switch() {
    let x: u64 = kani::any();
    kani::assume(x < 5);
    match x {
        0 | 1 | 2 | 3 | 4 => kani::assert(true, "should reach one of these cases"),
        _ => {}
    }
}

// Regression test for #190: mixed-width comparison via cast
#[kani::proof]
fn test_u64_vs_u32_comparison() {
    let a: u64 = kani::any();
    let b: u32 = kani::any();
    // Truncating cast comparison
    if (a as u32) == b {
        // If truncated a equals b, then the low 32 bits match
        kani::assert((a & 0xFFFFFFFF) as u32 == b, "low 32 bits should match");
    }
}

// Regression test for #190: mixed-width equality
#[kani::proof]
fn test_mixed_width_eq() {
    let a: u64 = kani::any();
    let b: u32 = kani::any();
    // Both sides are the same comparison - should be trivially true
    kani::assert((a as u32 == b) == ((a as u32) == b), "equivalent comparison");
}

// Test u8 to u64 extension
#[kani::proof]
fn test_u8_to_u64_extension() {
    let a: u8 = kani::any();
    let b: u64 = a as u64;
    kani::assert(b < 256, "extended u8 should be less than 256");
    kani::assert(b as u8 == a, "round-trip should preserve value");
}

// Test i32 to i64 sign extension
#[kani::proof]
fn test_i32_to_i64_sign_extension() {
    let a: i32 = kani::any();
    let b: i64 = a as i64;
    // Sign extension preserves sign
    if a < 0 {
        kani::assert(b < 0, "sign extension should preserve negative");
    } else {
        kani::assert(b >= 0, "sign extension should preserve non-negative");
    }
    // Round-trip should preserve value
    kani::assert(b as i32 == a, "round-trip should preserve value");
}

// Test unsigned to signed cast with same width
#[kani::proof]
fn test_u32_to_i32_same_width() {
    let a: u32 = kani::any();
    kani::assume(a <= i32::MAX as u32); // Only values that fit in i32
    let b: i32 = a as i32;
    kani::assert(b >= 0, "should be non-negative when in range");
    kani::assert(b as u32 == a, "should round-trip correctly");
}

// Test comparison between u8 and u32 after widening
#[kani::proof]
fn test_u8_u32_comparison() {
    let a: u8 = kani::any();
    let b: u32 = kani::any();
    kani::assume(b < 256);
    if a as u32 == b {
        kani::assert(a == b as u8, "comparison should be symmetric after cast");
    }
}

// Test u16 to u64 in branch condition
#[kani::proof]
fn test_u16_branch_condition() {
    let x: u16 = kani::any();
    let threshold: u64 = 1000;
    if (x as u64) > threshold {
        kani::assert(x > 1000, "branch condition should match");
    }
}
