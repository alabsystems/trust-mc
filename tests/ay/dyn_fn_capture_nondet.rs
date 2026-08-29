// kani-expect: PROOF
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// Diagnostic for #4003: isolate capture propagation across function boundaries.
// If this fails CTREX, capture propagation is broken (not just Vec::index).
// If this passes PROOF, captures work and Vec::index is the sole blocker.

fn takes_dyn_fun(fun: &dyn Fn() -> i32) {
    let x = fun();
    assert!(x == 5);
}

#[kani::proof]
fn main() {
    let a: i32 = kani::any();
    kani::assume(a == 3);
    let closure = || a + 2;
    takes_dyn_fun(&closure);
}
