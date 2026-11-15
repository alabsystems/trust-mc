// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// T3a review dual, SAFE twin. Every harness here is a correct program (upstream
// Kani 0.67 corpus-rev build: VERIFICATION:- SUCCESSFUL for all three). The
// recursion exceeds the CHC inline walker's depth (MAX_INLINE_DEPTH = 4; one
// parameter is nondeterministic, so no const-recursion relief). Past the bound
// the walker returns the recursion-unwind marker as a value only: the call's
// writes are dropped and its value is stripped to the success branch one level
// up, while the checks AFTER the call in the callee are still emitted on that
// truncated path. A failure of such a check is a truncation artifact.
//
// MUST NOT CERTIFY: SUCCESSFUL, or FAILED without [AY:CTREX_CAT:Genuine].

fn fill(c: &mut u32, n: u32, x: u8) {
    if n == 0 {
        *c = 7;
        return;
    }
    fill(c, n - 1, x);
    assert!(*c == 7, "after recursion c is 7");
}

#[kani::proof]
fn safe_fill_side_effect_past_bound() {
    let x: u8 = kani::any();
    let mut c: u32 = 0;
    fill(&mut c, 6, x);
}

fn pick(n: u32, b: bool) -> u32 {
    if n == 0 {
        return 0;
    }
    let r = pick(n - 1, b);
    if b {
        assert!(r == 0, "pick with b is zero");
        r
    } else {
        42
    }
}

#[kani::proof]
fn safe_pick_value_past_bound() {
    let b: bool = kani::any();
    let _v = pick(6, b);
}

fn acc(c: &mut u8, n: u32, x: u8) {
    if n == 0 {
        *c = 0;
        return;
    }
    acc(c, n - 1, x);
    *c += 1;
}

#[kani::proof]
fn safe_acc_overflow_past_bound() {
    let x: u8 = kani::any();
    let mut c: u8 = 255;
    acc(&mut c, 6, x);
}
