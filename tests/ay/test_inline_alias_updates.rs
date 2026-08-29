// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-expect: second_arg_writeback_direct=PROOF
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Part of #3936 D7: end-to-end verification that the inline alias-update map
// correctly propagates writes through the second (and later) &mut arguments.

fn overwrite_second(_x: &mut i32, y: &mut i32) {
    *y = 7;
}

#[kani::proof]
fn second_arg_writeback_direct() {
    let mut x = 1i32;
    let mut y = 2i32;
    overwrite_second(&mut x, &mut y);
    assert!(x == 1);
    assert!(y == 7);
}
