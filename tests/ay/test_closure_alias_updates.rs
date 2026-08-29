// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-expect: closure_second_arg_writeback=PROOF
// kani-expect: closure_env_and_second_arg_writeback=PROOF
// kani-flags: --ay-chc-track=mem
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Part of #3967: end-to-end verification that closure alias writeback keeps
// tuple-arg and env mutations visible to the caller.

#[kani::proof]
fn closure_second_arg_writeback() {
    let mut x = 1i32;
    let mut y = 2i32;
    let f = |_a: &mut i32, b: &mut i32| {
        *b = 7;
    };
    f(&mut x, &mut y);
    assert!(x == 1);
    assert!(y == 7);
}

#[kani::proof]
fn closure_env_and_second_arg_writeback() {
    let mut x = 1i32;
    let mut y1 = 2i32;
    let mut y2 = 3i32;
    let mut counter = 10i32;
    let mut f = |_a: &mut i32, b: &mut i32| {
        counter += 1;
        *b = 7;
        counter
    };
    let first = f(&mut x, &mut y1);
    let second = f(&mut x, &mut y2);
    assert!(first == 11);
    assert!(second == 12);
    assert!(y1 == 7);
    assert!(y2 == 7);
}
