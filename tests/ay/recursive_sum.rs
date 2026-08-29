// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: --ay-chc
// kani-verify-fail
// kani-expect: CTREX
//
//! Test: recursive function does not crash the compiler.
//!
//! The inline translator previously had no recursion depth guard, causing
//! unbounded stack recursion on recursive Rust functions with small bodies.
//! After #3614, the inline translator bails at MAX_INLINE_DEPTH=4, producing
//! an over-approximated result. After #4058, the inline walker emits an
//! `__assert_fail_inline_recursive_unwind` guard when `unwinding_assertions`
//! is enabled, making the recursion exhaustion reachable as CTREX.
//! Part of #3614, #4058.

fn recursive_sum(n: u32) -> u32 {
    if n == 0 { 0 } else { n + recursive_sum(n - 1) }
}

#[kani::proof]
#[kani::unwind(6)]
fn ay_recursive_sum() {
    let n: u32 = kani::any();
    kani::assume(n <= 5);
    let result = recursive_sum(n);
    assert!(result <= 15); // sum(0..=5) = 15
}
