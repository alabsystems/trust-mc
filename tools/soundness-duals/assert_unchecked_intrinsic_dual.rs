// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! `hint::assert_unchecked` with a violable condition.
//!
//! Oracle: MUST FAIL bug_assert_unchecked_violable; MUST PASS safe_assert_unchecked_assumed.
//! Calling `assert_unchecked(false)` is UB. With `ub_checks()` false (Kani's semantics) core's
//! precondition check does not run, and the only remaining obligation is the `assume` intrinsic,
//! which Kani asserts ("Rust intrinsic assumption failed"). A lane that merely assumes it
//! prunes the violating path and proves the harness.

#[kani::proof]
fn bug_assert_unchecked_violable() {
    let x: u8 = kani::any();
    unsafe { std::hint::assert_unchecked(x < 10) };
    std::hint::black_box(x);
}

#[kani::proof]
fn safe_assert_unchecked_assumed() {
    let x: u8 = kani::any();
    kani::assume(x < 10);
    unsafe { std::hint::assert_unchecked(x < 10) };
    assert!(x < 10);
}
