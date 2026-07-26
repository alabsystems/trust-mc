// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// @flag --unroll=10
// @expect error
// kani-verify-fail
// Reason: SMACK recursion test - fac(5,1) = 120, assertion says != 120 (expected failure)

fn fac(n: u64, acc: u64) -> u64 {
    match n {
        0 => acc,
        _ => fac(n - 1, acc * n),
    }
}

#[kani::proof]
pub fn main() {
    let x = fac(5, 1);
    assert!(x != 120);
}
