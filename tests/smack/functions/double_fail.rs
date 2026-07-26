// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// @expect error
// kani-verify-fail
// Reason: SMACK function test - double(a) = 2*a, assertion says b != 2*a (expected failure)

fn double(a: u32) -> u32 {
    a * 2
}

#[kani::proof]
pub fn main() {
    let a = kani::any();
    if a <= std::u32::MAX / 2 {
        // avoid overflow
        let b = double(a);
        assert!(b != 2 * a);
    }
}
