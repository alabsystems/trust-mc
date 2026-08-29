// kani-expect: PROOF
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// Diagnostic for #4003: Vec indexing inside a closure, but called directly (no dyn).

#[kani::proof]
fn main() {
    let a = vec![3i32];
    let closure = || a[0] + 2;
    let x = closure();
    assert!(x == 5);
}
