// kani-expect: PROOF
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// Diagnostic for #4003: does Vec capture itself work even without any Vec method call?
// The closure captures a Vec but doesn't use it — just returns a constant.

fn takes_dyn_fun(fun: &dyn Fn() -> i32) {
    let x = fun();
    assert!(x == 5);
}

#[kani::proof]
fn main() {
    let a = vec![3i32];
    let closure = || {
        let _ = &a; // force capture
        5
    };
    takes_dyn_fun(&closure);
}
