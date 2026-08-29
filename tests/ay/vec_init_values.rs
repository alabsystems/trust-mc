// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// kani-expect: PROOF
// Checks that vec![...] macro initialization propagates concrete element values
// through CHC rules so assertions on indexed elements are provable.
// Part of #4182.

#[kani::proof]
fn test_vec_init_single() {
    let v = vec![42i32];
    assert!(v[0] == 42);
}

#[kani::proof]
fn test_vec_init_two() {
    let v = vec![1i32, 2];
    assert!(v[0] == 1);
    assert!(v[1] == 2);
}
