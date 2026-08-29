// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-expect: BMC_SAFE
// Routed by lane_policy.toml: acyclic branch-condition implications are
// bounded and BMC discharges them directly.
//
//! Soundness test for #128: assertion encoding bug (passing harnesses).
//!
//! Split per #623: compiletest marks files as pass/fail, not individual harnesses.
//! See soundness_128_assert_violated.rs for the expected-to-fail harness.
//!
//! This test demonstrates correct handling of the #128 issue:
//! - `assert!(true)` inside conditional branches should pass
//! - Assertions implied by branch conditions should pass
//! - All harnesses in this file should PASS verification

/// This test should PASS - assert!(true) in a conditional branch.
///
/// Bug symptom (#128): With implication encoding, solver may avoid the branch
/// by making path_condition false, potentially reporting spurious sat.
#[kani::proof]
fn test_assert_true_in_branch_should_pass() {
    let x: i32 = kani::any();

    // No assume! The branch condition is unconstrained.
    if x > 0 {
        // This assert trivially holds - no input can violate it
        assert!(true);
    } else {
        // This branch also has a trivially true assertion
        assert!(true);
    }
    // Both branches have assert!(true), so verification should succeed
}

/// This test should PASS - assert!(true) only in one branch, no else.
///
/// Bug symptom (#128): Solver could make x <= 0 to avoid the branch entirely
/// and report sat for a "violation" that doesn't exist.
#[kani::proof]
fn test_assert_true_in_taken_branch() {
    let x: i32 = kani::any();

    if x > 0 {
        assert!(true);
    }
    // No else branch - just fall through
}

/// This test should PASS - assertion implied by branch condition.
///
/// Inside `if x > 5`, x > 5 holds, so x > 0 must hold.
/// Bug symptom (#128): Solver could avoid the branch by making x <= 5,
/// potentially reporting spurious sat.
#[kani::proof]
fn test_assert_implied_by_branch_condition() {
    let x: i32 = kani::any();

    if x > 5 {
        // Inside this branch, x > 5, so x > 0 must hold
        assert!(x > 0);
    }
}

// test_assert_can_be_violated moved to soundness_128_assert_violated.rs (#623)
