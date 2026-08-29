// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-expect: PROOF
//
//! Simple AY backend end-to-end test.
//!
//! This is the Phase 1 milestone test case.
//! It tests basic symbolic execution with assumes and asserts.

#[kani::proof]
fn simple_add() {
    let x: i32 = kani::any();
    let y: i32 = kani::any();
    kani::assume(x == 5);
    kani::assume(y == 3);
    assert!(x + y == 8);
}
