// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// @flag --no-memory-splitting
// @expect error
// kani-verify-fail
// Reason: SMACK vector test - v[0] unchanged at 0, assertion says != 0 (expected failure)

#[kani::proof]
pub fn main() {
    let mut v: Vec<u64> = Vec::new();
    v.push(0);
    v.push(1);
    v.push(3);
    assert!(v[0] == 0);
    assert!(v[1] == 1);
    assert!(v[2] == 3);
    v[2] = v[0] + v[1];
    assert!(v[0] != 0);
    assert!(v[1] == 1);
    assert!(v[2] == 1);
}
