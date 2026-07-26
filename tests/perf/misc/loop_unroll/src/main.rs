// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! This test checks the performance of bounded loop unrolling.
//! It uses fixed bounds to exercise the unrolling transformation at scale.

#[kani::proof]
#[kani::unwind(32)]
fn loop_unroll_linear_sum() {
    let mut i: u32 = 0;
    let mut sum: u32 = 0;
    while i < 32 {
        sum += i;
        i += 1;
    }
    assert!(sum == 496);
}

#[kani::proof]
#[kani::unwind(8)]
fn loop_unroll_nested_sum() {
    let mut i: u32 = 0;
    let mut sum: u32 = 0;
    while i < 8 {
        let mut j: u32 = 0;
        while j < 8 {
            sum += i + j;
            j += 1;
        }
        i += 1;
    }
    assert!(sum == 448);
}

fn main() {}
