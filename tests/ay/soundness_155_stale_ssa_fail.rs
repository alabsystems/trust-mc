// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// kani-verify-fail
//
//! DISCRIMINATING: #155 — stale SSA path-condition regressions.
//! Any PASS/PROOF result here means the false-proof bug resurfaced.
//!
//! Soundness test for #155: stale SSA in pass-1 path conditions (failing harnesses).
//!
//! Split from soundness_155_stale_ssa.rs per #1119:
//! compiletest marks files as pass/fail, not individual harnesses.
//!
//! These harnesses SHOULD produce verification failures (counterexample found).
//! The `kani-verify-fail` directive tells ay-compiletest.sh this is expected.
// kani-expect: CTREX
//!
//! Bug symptom (#155): If pass-1 uses stale SSA versions, then-blocks may appear
//! unreachable, and assertions would be masked (false proofs).

/// This test should FAIL - the assertion is reachable and violated.
///
/// Bug symptom (#155): If pass-1 path condition uses stale SSA (x=0),
/// the then-block may appear unreachable, and the `assert!(false)` is masked.
/// A false proof (incorrectly claims verification success) would result.
#[kani::proof]
fn test_reassigned_before_branch_should_fail() {
    let mut x: i32 = 0;
    x = 1; // Reassign x before the branch condition
    if x != 0 {
        // This branch IS taken (x=1 != 0), so assertion should fire
        assert!(false, "This assertion should be reachable and fail");
    }
}

/// This test should FAIL - multiple reassignments before branch.
///
/// Bug symptom (#155): Pass-1 may use any of the stale SSA versions.
#[kani::proof]
fn test_multiple_reassign_before_branch_should_fail() {
    let mut x: i32 = 0;
    x = 1;
    x = 2;
    x = 3; // Final value is 3
    if x > 0 {
        // x=3 > 0, so this branch IS taken
        assert!(false, "This assertion should be reachable and fail");
    }
}

/// This test should FAIL - computed value used in branch condition.
///
/// Bug symptom (#155): If pass-1 uses stale SSA, computed value may be wrong.
#[kani::proof]
fn test_computed_value_before_branch_should_fail() {
    let mut x: i32 = 5;
    let y: i32 = 10;
    x = x + y; // x = 15
    if x > 10 {
        // x=15 > 10, so branch IS taken
        assert!(false, "This assertion should be reachable");
    }
}

/// This test should FAIL - symbolic value reassigned before branch.
///
/// Shows interaction between symbolic inputs and reassignment.
#[kani::proof]
fn test_symbolic_reassign_before_branch_should_fail() {
    let input: i32 = kani::any();
    kani::assume(input > 0); // input is positive

    let mut x: i32 = 0;
    x = input; // Reassign with symbolic value

    if x > 0 {
        // x = input > 0, so branch IS taken
        assert!(false, "This assertion should be reachable");
    }
}
