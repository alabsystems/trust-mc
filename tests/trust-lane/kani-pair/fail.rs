// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! T1 Kani pair, failing half: the assumption bounds both operands below 100,
//! so the sum never overflows, but the assertion is false for a = b = 99. The
//! failure is a reachable user assertion, not only an arithmetic check.
//! Expected: VERIFICATION:- FAILED, with the assertion as the failed check.

#[kani::proof]
fn bounded_add_assertion_fails() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    kani::assume(a < 100 && b < 100);
    let sum = a + b;
    assert!(sum < 150, "sum reaches 150");
}
