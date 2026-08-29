// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// kani-verify-fail
//
//! Test case for division-by-zero checks (#61).
//!
//! Fail-only harnesses for div-by-zero safety properties.
//!
//! Split from test_div_by_zero.rs per #1121: compiletest marks files as pass/fail.
//! The `kani-verify-fail` directive tells ay-compiletest.sh this is expected.
// kani-expect: CTREX

/// This test should FAIL - unconstrained divisor can be zero.
/// The div-by-zero check assertion should catch this.
#[kani::proof]
fn test_div_unguarded_fail() {
    let x: i32 = kani::any();
    let y: i32 = kani::any();
    // No constraint on y - it could be zero!

    // Unsafe division - should trigger div_by_zero_check failure
    let _result = x / y;
}

/// This test should FAIL - unconstrained divisor for remainder.
#[kani::proof]
fn test_rem_unguarded_fail() {
    let x: u32 = kani::any();
    let y: u32 = kani::any();
    // No constraint on y - it could be zero!

    // Unsafe remainder - should trigger mod_by_zero_check failure
    let _result = x % y;
}
