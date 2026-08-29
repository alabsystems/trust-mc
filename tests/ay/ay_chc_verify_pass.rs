// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-expect: PROOF
// NOTE: Recovered PROOF at trust_mc 3eb155d516 / AY 733ba8cd; keep strict as a CHC success-path canary.
//
//! Test for --ay-chc-verify flag (Part of #970).
//!
//! This harness should pass CHC verification and model verification.
//! Used to validate that the verification hook works correctly for SAFE results.
//!
//! Run with:
//!   ./scripts/kani tests/ay/ay_chc_verify_pass.rs --ay-chc --ay-chc-verify -v

/// Simple harness that should pass CHC verification.
///
/// The assumption (x < 100) constrains the symbolic input,
/// and the assertion (x < 200) is trivially satisfied.
/// This tests the Safe result path with model verification.
#[kani::proof]
fn simple_safe() {
    let x: u32 = kani::any();
    kani::assume(x < 100);
    assert!(x < 200, "Value constrained to [0,100) should be less than 200");
}
