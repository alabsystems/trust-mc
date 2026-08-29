// kani-expect: PROOF
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// Diagnostic for #4003: does Vec value propagate through closure captures?
// Tests capture of Vec without indexing — just checks if the closure body
// can access the captured Vec's structure at all.

fn takes_dyn_fun(fun: &dyn Fn() -> bool) {
    let x = fun();
    assert!(x);
}

#[kani::proof]
fn main() {
    let a = vec![3i32];
    // Capture Vec but only check that it's non-empty (avoids Index::index)
    let closure = || !a.is_empty();
    takes_dyn_fun(&closure);
}
