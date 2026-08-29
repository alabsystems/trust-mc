// kani-expect: PROOF
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

fn takes_dyn_fun(fun: &dyn Fn() -> i32) {
    let x = fun();
    assert!(x == 5);
}

#[kani::proof]
fn main() {
    let a = vec![3];
    let closure = || a[0] + 2;
    takes_dyn_fun(&closure);
}
