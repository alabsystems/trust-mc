// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-verify-fail
// kani-expect: CTREX
//
//! Expected-fail test for kani::any() nondeterminism.
//! The finite BMC lane finds CTREX: x could be any u8 value, not just 0.
//!
//! Run with:
//!   ./scripts/ay-compiletest.sh tests/ay/kani_any_chc_fail.rs

#[kani::proof]
fn any_assert_is_not_constant() {
    let x: u8 = kani::any();
    assert!(x == 0);
}
