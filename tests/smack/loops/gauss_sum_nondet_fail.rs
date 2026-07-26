// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// @flag --no-memory-splitting --unroll=10
// @expect error
// kani-verify-fail
// Reason: SMACK loop test - Gauss formula holds, assertion negates it (expected failure)

#[kani::proof]
#[kani::unwind(5)]
pub fn main() {
    let mut sum = 0;
    let b: u64 = kani::any();
    if b < 5 && b > 1 {
        for i in 0..b {
            sum += i;
        }
        assert!(2 * sum != b * (b - 1));
    }
}
