// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-expect: BMC_SAFE
//
//! Regression tests for SwitchInt path condition handling.
//!
//! These tests verify that #82 and #593 are fixed: assertions in branches are
//! properly guarded by path conditions so that only reachable assertions are checked.
//!
//! - #82: Basic path condition handling for local discriminants
//! - #593: Constant and projected discriminants (not just simple locals)

/// Test that assertions in mutually exclusive branches don't conflict.
/// Before the fix, both assert!(false) in unreachable branches would fail.
#[kani::proof]
fn test_mutually_exclusive_branches() {
    let x: i32 = kani::any();
    kani::assume(x > 0);

    if x > 0 {
        // This branch is reachable
        assert!(true);
    } else {
        // This branch is unreachable due to assume(x > 0)
        // Before fix: this would fail. After fix: properly guarded.
        assert!(false);
    }
}

/// Test nested conditionals with path conditions.
#[kani::proof]
fn test_nested_branches() {
    let x: i32 = kani::any();
    let y: i32 = kani::any();
    kani::assume(x == 5);
    kani::assume(y == 10);

    if x > 0 {
        if y > 5 {
            // Both conditions are satisfied, this should be checked
            assert!(x + y == 15);
        } else {
            // y > 5 is true due to assume, so this is unreachable
            assert!(false);
        }
    } else {
        // x > 0 is true due to assume, so this is unreachable
        assert!(false);
    }
}

/// Test that assume works correctly in conjunction with branches.
#[kani::proof]
fn test_assume_with_branch() {
    let flag: bool = kani::any();

    if flag {
        kani::assume(flag);
        assert!(flag);
    } else {
        kani::assume(!flag);
        assert!(!flag);
    }
}

/// Test constant discriminant in match expression (#593).
///
/// When matching on a constant value, the discriminant is not a local variable.
/// This test verifies that constant discriminants generate proper guards.
#[kani::proof]
fn test_constant_discriminant() {
    // Matching on a constant - discriminant is the constant 5, not a local
    match 5u32 {
        0 => assert!(false, "unreachable: 5 != 0"),
        5 => assert!(true, "reachable: 5 == 5"),
        _ => assert!(false, "unreachable: 5 matches exactly"),
    }
}

/// Test tuple field projection as discriminant (#593).
///
/// When the discriminant comes from a tuple field, it requires projection handling.
#[kani::proof]
fn test_projected_discriminant() {
    let pair: (u32, u32) = (42, 100);

    // The discriminant here is `pair.0` which is a projected place
    match pair.0 {
        0 => assert!(false, "unreachable: 42 != 0"),
        42 => assert!(true, "reachable: 42 == 42"),
        _ => assert!(false, "unreachable: 42 matches exactly"),
    }
}
