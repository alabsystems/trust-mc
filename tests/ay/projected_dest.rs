// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-expect: PROOF
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for projected destination handling in function inlining.
//!
//! This test verifies that calls with projected destinations (e.g., `_3.0 = foo()`)
//! are correctly handled via ret_tmp + post_return_bb.
//!
//! Part of #223 (function inlining) and Phase 4 Milestone 1.

/// Returns a tuple - tests projected destination handling.
fn returns_tuple() -> (i32, i32) {
    (1, 2)
}

/// Returns a nested tuple.
fn returns_nested() -> ((i32, i32), i32) {
    ((10, 20), 30)
}

#[kani::proof]
fn test_projected_first_field() {
    let (x, _y) = returns_tuple();
    kani::assert(x == 1, "first field should be 1");
}

#[kani::proof]
fn test_projected_second_field() {
    let (_x, y) = returns_tuple();
    kani::assert(y == 2, "second field should be 2");
}

#[kani::proof]
fn test_projected_both_fields() {
    let (x, y) = returns_tuple();
    kani::assert(x == 1, "first field should be 1");
    kani::assert(y == 2, "second field should be 2");
}

#[kani::proof]
fn test_projected_nested() {
    let ((a, b), c) = returns_nested();
    kani::assert(a == 10, "nested first should be 10");
    kani::assert(b == 20, "nested second should be 20");
    kani::assert(c == 30, "outer second should be 30");
}

#[kani::proof]
fn test_projected_sum() {
    let (x, y) = returns_tuple();
    kani::assert(x + y == 3, "sum should be 3");
}
