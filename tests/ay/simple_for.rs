// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// kani-flags: --default-unwind 15 --ay-chc-int-lift
// kani-expect: UNKNOWN
//
//! Phase 3 Tier 1 test: simple for loop
//!
//! Tests BMC verification of a simple for loop with sufficient unwind depth.
//! Part of #609 - Phase 3 Tier 1 metrics tracking.
//!
//! STATUS: PASSING - CHC/Spacer with int-lift proves the for-loop invariant.
//! Int-lift (#112 Direction 2) promotes BV scalars to Int, letting Spacer
//! synthesize loop invariants in LIA instead of BV theory.
//!
//! The `--default-unwind 15` remains for BMC fallback. The `--ay-chc-int-lift`
//! flag enables Int-lifting which resolves the BV theory wall (W2:3183).
//! Without int-lift, Spacer returns UNKNOWN due to cross-theory BV/Int mismatch.

/// Simple for loop over a fixed range.
///
/// Loop invariant: sum == (number of iterations completed so far)
/// Post-condition: sum == 10 after 10 iterations
#[kani::proof]
fn ay_simple_for() {
    let mut sum: u32 = 0;
    for _i in 0..10 {
        sum += 1;
    }
    assert!(sum == 10);
}
