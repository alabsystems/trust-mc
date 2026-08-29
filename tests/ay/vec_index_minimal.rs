// kani-expect: PROOF
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// Diagnostic for #4003: minimal Vec indexing without any closure/dyn involvement.

#[kani::proof]
fn main() {
    let a = vec![3i32];
    let x = a[0];
    assert!(x == 3);
}
