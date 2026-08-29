// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-expect: BMC_SAFE
// Routed by lane_policy.toml: acyclic branch-merge/phi cases are bounded and
// BMC discharges them directly.
//
//! Soundness test for #129: missing phi/merge for branch-assigned locals (passing harnesses).
//!
//! Split per #623: compiletest marks files as pass/fail, not individual harnesses.
//! See soundness_129_fail_expected.rs for the expected-to-fail harness.
//!
//! This test demonstrates the soundness issue described in #129:
//! The AY backend emits assignment constraints unconditionally without
//! guarding them by the branch path condition. This means locals assigned
//! in mutually-exclusive branches don't get a proper merge (phi node).
//! The last SSA version allocated "wins" regardless of which branch was taken.
//!
//! Test design:
//! - Variable `y` is assigned different values in if/else branches
//! - After the branch, `kani::assume` constrains which branch was taken
//! - Assertion checks that `y` has the correct value for the taken branch
//! - Correct behavior: VERIFICATION SUCCESS (y matches branch condition)
//! - Bug behavior: Assertion may fail because y has the wrong value

/// This test should PASS - branch-assigned variable retains correct value.
///
/// Bug symptom (#129): Without proper phi/merge, y may have value 2 even when x > 0.
#[kani::proof]
fn test_branch_assigned_value_with_assume() {
    let x: i32 = kani::any();

    let y = if x > 0 { 1 } else { 2 };

    // Constrain to the then-branch
    kani::assume(x > 0);

    // In the then-branch, y should be 1
    assert!(y == 1);
}

/// This test should PASS - constrain to else-branch, check y == 2.
///
/// Bug symptom (#129): y may have wrong value if phi/merge is missing.
#[kani::proof]
fn test_branch_assigned_value_else_branch() {
    let x: i32 = kani::any();

    let y = if x > 0 { 1 } else { 2 };

    // Constrain to the else-branch
    kani::assume(x <= 0);

    // In the else-branch, y should be 2
    assert!(y == 2);
}

/// This test should PASS - without assume, y can be 1 or 2.
///
/// Both values are valid post-branch, so the disjunction holds.
#[kani::proof]
fn test_branch_assigned_value_no_assume() {
    let x: i32 = kani::any();

    let y = if x > 0 { 1 } else { 2 };

    // Without assume, y could be 1 or 2 - both are valid
    assert!(y == 1 || y == 2);
}

/// This test should PASS - multiple branch-assigned variables.
///
/// Bug symptom (#129): Both a and b may have wrong values if phi/merge is missing.
#[kani::proof]
fn test_multiple_branch_assigned_variables() {
    let x: i32 = kani::any();

    let (a, b) = if x > 0 { (10, 20) } else { (30, 40) };

    kani::assume(x > 0);

    // Both a and b should have then-branch values
    assert!(a == 10);
    assert!(b == 20);
}

// test_branch_assigned_wrong_assertion moved to soundness_129_fail_expected.rs (#623)

/// This test should PASS - nested branch assignments.
///
/// Bug symptom (#129): z may have wrong value if nested phi/merge is missing.
#[kani::proof]
fn test_nested_branch_assignment() {
    let x: i32 = kani::any();
    let y: i32 = kani::any();

    let z = if x > 0 { if y > 0 { 1 } else { 2 } } else { 3 };

    kani::assume(x > 0);
    kani::assume(y > 0);

    // x > 0 and y > 0, so z should be 1
    assert!(z == 1);
}
