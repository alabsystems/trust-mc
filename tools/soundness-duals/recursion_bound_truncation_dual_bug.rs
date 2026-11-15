// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// T3a review dual, BUG twin of recursion_bound_truncation_dual_safe.rs: the
// same shapes with a real bug reachable on a shallow path (n = 0 or 1 level),
// so a repair of the safe twin cannot be a blinding. SUCCESSFUL is a missed bug.

fn fill(c: &mut u32, n: u32, x: u8) {
    if n == 0 {
        *c = 7;
        return;
    }
    fill(c, n - 1, x);
    assert!(*c == 8, "after recursion c is 8 (false)");
}

#[kani::proof]
#[kani::unwind(4)]
fn bug_fill_shallow() {
    let x: u8 = kani::any();
    let n: u32 = kani::any();
    kani::assume(n <= 1);
    let mut c: u32 = 0;
    fill(&mut c, n, x);
    assert!(n == 0 || c == 7);
}

// Real recursion-unwinding failure: Kani fails ONLY the unwinding assertion;
// the in-callee assertion is never violated. A certified Genuine failure of
// that assertion is a false certificate.
fn fill2(c: &mut u32, n: u32) {
    if n == 0 {
        *c = 7;
        return;
    }
    fill2(c, n - 1);
    assert!(*c == 7, "after recursion c is 7");
}

#[kani::proof]
#[kani::unwind(3)]
fn bug_real_unwind_failure() {
    let n: u32 = kani::any();
    kani::assume(n <= 6);
    let mut c: u32 = 0;
    fill2(&mut c, n);
}
