// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// kani-verify-fail
//
//! Test case for bounds check assertions (#60) - failing harnesses.
//!
//! Split from test_bounds_check.rs per #1120:
//! compiletest marks files as pass/fail, not individual harnesses.
//!
//! This harness SHOULD produce a verification failure (counterexample found).
//! The `kani-verify-fail` directive tells ay-compiletest.sh this is expected.
// kani-expect: CTREX

/// This test should FAIL - unconstrained index can be out of bounds.
#[kani::proof]
fn test_array_index_unguarded_fail() {
    let arr: [i32; 4] = [1, 2, 3, 4];
    let idx: usize = kani::any();
    // No constraint on idx - it could be >= 4!

    // Unsafe indexing - should trigger bounds_check failure
    let _val = arr[idx];
}
