// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// @expect error
// kani-verify-fail
// Reason: SMACK arithmetic test - 3 * 2 = 6, assertion says != 6 (expected failure)

#[kani::proof]
pub fn main() {
    let a = 2;
    let b = 3;
    assert!(b * a != 6);
}
