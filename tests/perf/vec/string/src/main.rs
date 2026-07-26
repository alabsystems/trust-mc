// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! This test checks the performance of pushing onto a vector of strings
//! The test is from https://github.com/model-checking/kani/issues/1673.
//! Upstream Kani history: Pre CBMC 5.71.0, it took ~8.5 minutes and consumed ~27 GB.
//! With CBMC 5.71.0, it took ~70 seconds and consumed ~255 MB.

const N: usize = 9;

#[kani::proof]
#[kani::unwind(10)]
fn main() {
    let mut v: Vec<String> = Vec::new();
    for _i in 0..N {
        v.push(String::from("ABC"));
    }
    assert_eq!(v.len(), N);
    let index: usize = kani::any();
    kani::assume(index < v.len());
    let x = &v[index];
    assert_eq!(*x, "ABC");
}
