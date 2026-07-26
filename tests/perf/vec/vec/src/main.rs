// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! This test checks the performance of 2d-vectors
//! The test is from https://github.com/model-checking/kani/issues/1226.
//! Upstream Kani history: Pre CBMC 5.72.0, it ran out of memory.
//! With CBMC 5.72.0, it took ~2 seconds and consumed a few hundred MB.

#[kani::proof]
#[kani::unwind(5)]
#[kani::solver(minisat)]
fn main() {
    let v1: Vec<Vec<i32>> = vec![vec![1], vec![]];

    let v2: Vec<i32> = v1.into_iter().flatten().collect();
    assert_eq!(v2, vec![1]);
}
