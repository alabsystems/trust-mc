// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! T1 Kani pair, passing half: the assumption bounds both operands below 100,
//! so the sum cannot overflow and the assertion holds.
//! Expected: VERIFICATION:- SUCCESSFUL.

#[kani::proof]
fn bounded_add_is_below_200() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    kani::assume(a < 100 && b < 100);
    assert!(a + b < 200);
}
