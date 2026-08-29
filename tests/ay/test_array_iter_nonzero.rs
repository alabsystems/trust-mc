// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: --unstable=array-iter-unroll
// kani-expect: PROOF
//
// Test: Non-zero length array iteration to exercise iterator infrastructure
// Status: PASSING with ArrayIterUnrollPass transformation

#[kani::proof]
#[kani::unwind(3)] // Array len + 1 for loop exit check
fn check_single_element_iteration() {
    let arr: [u8; 1] = [42];
    let mut sum: u8 = 0;
    for x in arr {
        sum = sum.wrapping_add(x);
    }
    kani::assert(sum == 42, "sum should be 42");
}
