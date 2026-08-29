// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-verify-fail
// kani-expect: CTREX
//
//! Soundness test for #128: verification finds actual violations.
//!
//! Split from soundness_128_assert_true_branch.rs per #623:
//! compiletest marks files as pass/fail, not individual harnesses.
//!
//! This harness SHOULD produce a verification failure (counterexample found).
//! The `kani-verify-fail` directive tells ay-compiletest.sh this is expected.

/// This test should FAIL - assertion CAN be violated.
///
/// Counterexample exists: x could be <= 0. This is a control test to ensure
/// the test infrastructure reports failures correctly.
#[kani::proof]
fn test_assert_can_be_violated() {
    let x: i32 = kani::any();

    // No constraint on x - it could be any i32, including negative
    assert!(x > 0); // Counterexample: x = 0 or x = -1
}
