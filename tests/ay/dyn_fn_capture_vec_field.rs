// kani-expect: PROOF
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// Diagnostic for #4003: capture Vec and access its len field directly.
// If this passes, Vec capture propagation works and the issue is Vec method stubs.

fn takes_dyn_fun(fun: &dyn Fn() -> usize) {
    let x = fun();
    assert!(x == 1);
}

#[kani::proof]
fn main() {
    let a = vec![3i32];
    let closure = || a.len();
    takes_dyn_fun(&closure);
}
