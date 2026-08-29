// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-expect: UNKNOWN
// kani-expect: any_assume_constrains=PROOF
// kani-expect: any_assume_constrains_bool=PROOF
// NOTE: any_assume_constrains_bool was PROOF at ay 417854b7, regressed to UNKNOWN at ay 8a4a9bcc2 (false proof caught by defense).
//
//! CHC sanity tests for kani::any() nondeterminism.
//!
//! Run with:
//!   ./scripts/trust_mc -Z unstable-options --backend=ay --ay-chc tests/ay/kani_any_chc_pass.rs

#[kani::proof]
fn any_assume_constrains() {
    let x: u8 = kani::any();
    kani::assume(x == 5);
    assert!(x == 5);
}

#[kani::proof]
fn any_assume_constrains_bool() {
    let flag: bool = kani::any();
    kani::assume(flag);
    assert!(flag);
}
