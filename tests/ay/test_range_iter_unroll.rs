// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
// kani-flags: --ay-chc --unstable=range-iter-unroll --ay-chc-bounded-unroll
// kani-expect: PROOF
// NOTE: All harnesses recovered to PROOF after the ay#8578 false-proof
// defense was reworked upstream (AY pin 3d9db24e68, 2026-05-19).
//
// Minimal tests for RangeIterUnrollPass.

/// Test a simple bounded range sum with explicit unwind.
#[kani::proof]
#[kani::unwind(6)] // 4 iterations + exit
fn check_range_sum() {
    let mut sum: u32 = 0;
    for i in 0u32..4 {
        sum += i;
    }
    assert!(sum == 6);
}

/// Test that an empty range never iterates.
#[kani::proof]
fn check_empty_range() {
    let mut count: u32 = 0;
    for _ in 0u32..0 {
        count += 1;
    }
    assert!(count == 0);
}

/// Test single iteration range (0..1).
#[kani::proof]
fn check_single_iteration() {
    let mut count: u32 = 0;
    let mut value: u32 = 99;
    for i in 0u32..1 {
        count += 1;
        value = i;
    }
    assert!(count == 1);
    assert!(value == 0);
}

/// Test non-zero start range (5..10).
#[kani::proof]
#[kani::unwind(7)] // 5 iterations + exit
fn check_nonzero_start() {
    let mut sum: u32 = 0;
    for i in 5u32..10 {
        sum += i;
    }
    // 5 + 6 + 7 + 8 + 9 = 35
    assert!(sum == 35);
}

/// Test u8 range type.
#[kani::proof]
fn check_range_u8() {
    let mut sum: u8 = 0;
    for i in 0u8..3 {
        sum += i;
    }
    assert!(sum == 3); // 0 + 1 + 2
}

/// Test u64 range type.
#[kani::proof]
#[kani::unwind(5)]
fn check_range_u64() {
    let mut sum: u64 = 0;
    for i in 0u64..4 {
        sum += i;
    }
    assert!(sum == 6); // 0 + 1 + 2 + 3
}

/// Test usize range type (common idiom: 0..arr.len()).
#[kani::proof]
#[kani::unwind(6)]
fn check_range_usize() {
    let mut sum: usize = 0;
    for i in 0usize..5 {
        sum += i;
    }
    assert!(sum == 10); // 0 + 1 + 2 + 3 + 4
}

/// Test u16 range type.
#[kani::proof]
#[kani::unwind(5)]
fn check_range_u16() {
    let mut sum: u16 = 0;
    for i in 0u16..4 {
        sum += i;
    }
    assert!(sum == 6); // 0 + 1 + 2 + 3
}

/// Test u128 range type.
#[kani::proof]
#[kani::unwind(5)]
fn check_range_u128() {
    let mut sum: u128 = 0;
    for i in 0u128..4 {
        sum += i;
    }
    assert!(sum == 6); // 0 + 1 + 2 + 3
}

// === Signed Range Tests (Part of #1555) ===

/// Test i32 range type (most common signed range idiom).
#[kani::proof]
#[kani::unwind(5)]
fn check_range_i32() {
    let mut sum: i32 = 0;
    for i in 0i32..4 {
        sum += i;
    }
    assert!(sum == 6); // 0 + 1 + 2 + 3
}

/// Test signed range with negative start.
#[kani::proof]
#[kani::unwind(6)]
fn check_range_negative_start() {
    let mut sum: i32 = 0;
    for i in -2i32..2 {
        sum += i;
    }
    // -2 + -1 + 0 + 1 = -2
    assert!(sum == -2);
}

/// Test i8 range type.
#[kani::proof]
#[kani::unwind(4)]
fn check_range_i8() {
    let mut sum: i8 = 0;
    for i in 0i8..3 {
        sum += i;
    }
    assert!(sum == 3); // 0 + 1 + 2
}

/// Test i16 range type.
#[kani::proof]
#[kani::unwind(5)]
fn check_range_i16() {
    let mut sum: i16 = 0;
    for i in 0i16..4 {
        sum += i;
    }
    assert!(sum == 6); // 0 + 1 + 2 + 3
}

/// Test i64 range type.
#[kani::proof]
#[kani::unwind(5)]
fn check_range_i64() {
    let mut sum: i64 = 0;
    for i in 0i64..4 {
        sum += i;
    }
    assert!(sum == 6); // 0 + 1 + 2 + 3
}

/// Test i128 range type.
#[kani::proof]
#[kani::unwind(5)]
fn check_range_i128() {
    let mut sum: i128 = 0;
    for i in 0i128..4 {
        sum += i;
    }
    assert!(sum == 6); // 0 + 1 + 2 + 3
}

/// Test isize range type.
#[kani::proof]
#[kani::unwind(6)]
fn check_range_isize() {
    let mut sum: isize = 0;
    for i in 0isize..5 {
        sum += i;
    }
    assert!(sum == 10); // 0 + 1 + 2 + 3 + 4
}
