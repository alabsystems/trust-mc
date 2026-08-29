// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-expect: PROOF
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Test: Simple function inlining - add function

fn simple_add(x: i32, y: i32) -> i32 {
    x + y
}

#[kani::proof]
fn test_inline_add() {
    let a: i32 = 5;
    let b: i32 = 3;
    let c = simple_add(a, b);
    assert!(c == 8);
}
