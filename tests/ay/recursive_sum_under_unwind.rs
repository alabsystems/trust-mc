// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-verify-fail
// kani-expect: CTREX
//
//! Part of #4058 D5: compiletest canary for recursive unwind assertion.
//!
//! recursive_sum is self-recursive. With `#[kani::unwind(2)]`, the inline
//! walker exhausts the unwind budget and emits an
//! `__assert_fail_inline_recursive_unwind` guard (when `unwinding_assertions`
//! is enabled). The driver fail-closes on that evidence and surfaces the
//! recursion exhaustion as a CTREX instead of a backend-dependent PROOF or
//! UNKNOWN.

fn recursive_sum(n: u32) -> u32 {
    if n == 0 { 0 } else { n + recursive_sum(n - 1) }
}

#[kani::proof]
#[kani::unwind(2)]
fn check_recursive_sum_bounded() {
    let n: u32 = kani::any();
    kani::assume(n <= 5);
    let result = recursive_sum(n);
    assert!(result <= 15);
}
