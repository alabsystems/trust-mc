// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// @flag --integer-overflow
// @expect overflow
// kani-verify-fail
// Reason: SMACK overflow test - 128 * 2 = 256 overflows u8 (expected failure)

fn get128() -> u8 {
    128
}

#[kani::proof]
pub fn main() {
    let a: u8 = get128();
    let b: u8 = 2;
    let c = a * b;
}
