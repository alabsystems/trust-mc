// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// kani-verify-fail
//
//! DISCRIMINATING: #2055 — intermediate-read constraint-replacement regressions.
//! Any PASS/PROOF result here means the false-proof bug resurfaced.
//!
//! Soundness test for #2055: intermediate reads between re-assignments.
//!
//! When a local is assigned, read by another assignment, then re-assigned
//! within the same basic block, the CHC encoder must preserve the intermediate
//! value. A constraint-replacement approach that only keeps the final
//! assignment's constraint will produce false proofs.
//!
//! These harnesses SHOULD produce verification failures (counterexample found).
//! CHC correctly finds CTREX for all harnesses.
// kani-expect: CTREX

/// Simple read-then-overwrite: b copies a's first value, then a is overwritten.
///
/// Bug: If only the last constraint on a__out is active (a__out == 0),
/// then b__out == a__out gives b == 0 instead of the correct b == 42.
#[kani::proof]
fn test_read_then_overwrite_should_fail() {
    let mut a: i32 = 42;
    let b: i32 = a; // b = 42
    a = 0;
    // b is 42, not 0. This assertion is WRONG and should produce CTREX.
    assert!(b == 0, "b should NOT be 0");
}

/// Multiple locals reading intermediate values of a re-assigned local.
#[kani::proof]
fn test_multiple_intermediate_reads_should_fail() {
    let mut x: i32 = 10;
    let a: i32 = x; // a = 10
    x = 20;
    let b: i32 = x; // b = 20
    x = 30;
    // a=10, b=20, x=30. The assertion a == b is WRONG.
    assert!(a == b, "a and b should NOT be equal");
}

/// Read via arithmetic expression between re-assignments.
#[kani::proof]
fn test_arithmetic_intermediate_read_should_fail() {
    let mut x: i32 = 5;
    let y: i32 = x + 1; // y = 6
    x = 100;
    // y is 6, not 101. This assertion is WRONG.
    assert!(y == 101, "y should NOT be 101");
}
