// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// @flag --unroll=10
// @expect error
// kani-verify-fail
// Reason: SMACK recursion test - fib(6) = 8, assertion says != 8 (expected failure)

fn fib(x: u64) -> u64 {
    match x {
        0 => 0,
        1 => 1,
        _ => fib(x - 1) + fib(x - 2),
    }
}

#[kani::proof]
pub fn main() {
    let x = fib(6);
    assert!(x != 8);
}
