// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: --unstable=array-iter-unroll
// kani-expect: PROOF
//
// Test: Multi-element array iteration to verify ArrayIterUnrollPass
// Status: PASSING with ArrayIterUnrollPass transformation
// Part of #468

#[kani::proof]
#[kani::unwind(4)] // Array len + 1 for loop exit check
fn check_two_element_iteration() {
    let arr: [u8; 2] = [10, 20];
    let mut sum: u8 = 0;
    for x in arr {
        sum = sum.wrapping_add(x);
    }
    kani::assert(sum == 30, "sum should be 30");
}

#[kani::proof]
#[kani::unwind(5)] // Array len + 1 for loop exit check
fn check_three_element_iteration() {
    let arr: [u8; 3] = [1, 2, 3];
    let mut sum: u8 = 0;
    for x in arr {
        sum = sum.wrapping_add(x);
    }
    kani::assert(sum == 6, "sum should be 6");
}
