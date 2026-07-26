// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-verify-fail
// kani-expect: CTREX
//
//! Soundness test for #129: verification finds branch phi violations.
//!
//! Split from soundness_129_branch_phi.rs per #623:
//! compiletest marks files as pass/fail, not individual harnesses.
//!
//! This harness SHOULD produce a verification failure (counterexample found).
//! The `kani-verify-fail` directive tells ay-compiletest.sh this is expected.

/// This test should FAIL - incorrect assertion (control test).
///
/// Wrong assertion: y is 1 in then-branch, not 2.
#[kani::proof]
fn test_branch_assigned_wrong_assertion() {
    let x: i32 = kani::any();

    let y = if x > 0 { 1 } else { 2 };

    kani::assume(x > 0);

    // Wrong assertion - y is 1 in then-branch, not 2
    assert!(y == 2); // Should FAIL
}
