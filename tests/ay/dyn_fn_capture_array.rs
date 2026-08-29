// kani-expect: PROOF
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// Diagnostic for #4003: isolate array indexing in closure body via dyn Fn.
// Uses fixed-size array (no heap) to test if inline_index_expr fires for
// captures through the fn_trait_dispatch closure path.

fn takes_dyn_fun(fun: &dyn Fn() -> i32) {
    let x = fun();
    assert!(x == 5);
}

#[kani::proof]
fn main() {
    let a = [3i32];
    let closure = || a[0] + 2;
    takes_dyn_fun(&closure);
}
