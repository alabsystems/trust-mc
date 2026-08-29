// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-expect: BMC_SAFE
//
//! Soundness test for #155: stale SSA in pass-1 path conditions (passing harnesses).
//!
//! Split per #1119: compiletest marks files as pass/fail, not individual harnesses.
//! See soundness_155_stale_ssa_fail.rs for the expected-to-fail harnesses.
//!
//! This test demonstrates correct handling of the #155 issue:
//! - Unreachable branches should not trigger assertions
//! - Correct assertions in taken branches should pass
//! - All harnesses in this file should PASS verification

/// This test should PASS - the assertion is not reachable.
///
/// Control test: x remains 0, so the then-branch is not taken.
#[kani::proof]
fn test_not_reassigned_before_branch_should_pass() {
    let mut x: i32 = 0;
    // x is NOT reassigned
    if x != 0 {
        // This branch is NOT taken (x=0 == 0)
        assert!(false, "This assertion should be unreachable");
    }
    // Verification succeeds because the assertion is unreachable
}

/// This test should PASS - taken branch has correct assertion.
///
/// The reassignment makes the branch reachable, and the assertion is correct.
#[kani::proof]
fn test_reassigned_before_branch_correct_assertion() {
    let mut x: i32 = 0;
    x = 1;
    if x != 0 {
        assert!(x == 1, "x should be 1 after reassignment");
    }
}

/// This test should PASS - x is reassigned but doesn't change branch outcome.
///
/// x starts at 0, is reassigned to 0, so branch is still not taken.
#[kani::proof]
fn test_reassign_same_value_branch_not_taken() {
    let mut x: i32 = 0;
    x = 0; // Reassign to same value
    if x != 0 {
        // Branch NOT taken (x=0)
        assert!(false, "This assertion should be unreachable");
    }
}

/// This test should PASS - else branch is taken.
///
/// x is reassigned to 0, so the else branch is taken, not the then branch.
#[kani::proof]
fn test_reassign_to_zero_else_branch() {
    let mut x: i32 = 5;
    x = 0; // Reassign to 0
    if x != 0 {
        assert!(false, "Then branch should NOT be taken");
    }
    // Verification succeeds - else branch taken, no assertion
}
