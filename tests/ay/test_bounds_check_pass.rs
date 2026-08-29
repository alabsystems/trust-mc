// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-expect: UNKNOWN
// kani-expect: test_2d_array_guarded_pass=BMC_SAFE
// kani-expect: test_array_constant_index_pass=BMC_SAFE
// kani-expect: test_array_index_guarded_pass=BMC_SAFE
// kani-expect: test_empty_array_no_access_pass=PROOF
// kani-expect: test_slice_index_guarded_pass=PROOF
// NOTE: 3 array-index harnesses route through bounded BMC; slice indexing remains UNKNOWN.
// kani-flags: --ay-chc-track=mem
//
//! Test case for bounds check assertions (#60) - passing harnesses.
//!
//! Split per #1120: compiletest marks files as pass/fail, not individual harnesses.
//! See test_bounds_check_fail.rs for the expected-to-fail harness.
//!
//! Tests that the AY backend emits bounds-check safety properties
//! equivalent to CBMC's `--bounds-check`.

/// This test should PASS - index is constrained to be in bounds.
#[kani::proof]
fn test_array_index_guarded_pass() {
    let arr: [i32; 4] = [1, 2, 3, 4];
    let idx: usize = kani::any();
    kani::assume(idx < 4);

    // Safe indexing - idx is known to be < array length
    let _val = arr[idx];
}

/// Test with constant index that is in bounds.
#[kani::proof]
fn test_array_constant_index_pass() {
    let arr: [u8; 3] = [10, 20, 30];

    // All constant indices are valid
    let _a = arr[0];
    let _b = arr[1];
    let _c = arr[2];
}

/// Test slice indexing with guarded index.
#[kani::proof]
fn test_slice_index_guarded_pass() {
    let arr: [i32; 5] = [1, 2, 3, 4, 5];
    // Prefer unsizing coercion over `&arr[..]` to avoid `Index<RangeFull>` calls (#26).
    let slice: &[i32] = &arr;
    let idx: usize = kani::any();
    kani::assume(idx < 5);

    // Safe slice indexing
    let _val = slice[idx];
}

/// Test 2D array indexing (nested bounds checks).
#[kani::proof]
fn test_2d_array_guarded_pass() {
    let arr: [[i32; 3]; 2] = [[1, 2, 3], [4, 5, 6]];
    let i: usize = kani::any();
    let j: usize = kani::any();
    kani::assume(i < 2);
    kani::assume(j < 3);

    // Both indices are bounded
    let _val = arr[i][j];
}

/// Test that bounds check on zero-length iteration is safe.
#[kani::proof]
fn test_empty_array_no_access_pass() {
    let arr: [i32; 0] = [];
    // No indexing, just declaration - should pass
    assert!(arr.len() == 0);
}
