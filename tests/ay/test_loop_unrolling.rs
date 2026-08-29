// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: --ay-chc --ay-chc-int-lift
// kani-expect: UNKNOWN
// NOTE: All harnesses demoted PROOF→UNKNOWN by false proof defense (ay#8578).
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! AY backend end-to-end tests for bounded loop unrolling (Issue #192).

#[kani::proof]
#[kani::unwind(3)]
fn ay_while_loop_counts_to_three() {
    let mut i: u8 = 0;
    while i < 3 {
        i += 1;
    }
    assert!(i == 3);
}

#[kani::proof]
#[kani::unwind(6)]
fn ay_loop_break_counts_to_five() {
    let mut x: u8 = 0;
    loop {
        x += 1;
        if x == 5 {
            break;
        }
    }
    assert!(x == 5);
}

#[kani::proof]
#[kani::unwind(2)]
fn ay_nested_while_loops_sum_to_four() {
    let mut i: u8 = 0;
    let mut sum: u8 = 0;
    while i < 2 {
        let mut j: u8 = 0;
        while j < 2 {
            sum += 1;
            j += 1;
        }
        i += 1;
    }
    assert!(sum == 4);
}
