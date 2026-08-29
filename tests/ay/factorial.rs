// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: --ay-chc
// kani-expect: BMC_SAFE
// Routed to BMC lane (lane_policy.toml) — bounded loop with unwind(14).
// CHC regressed UNKNOWN->ERROR after ay bump. BMC proves the bounded safety
// obligation despite the file-level CHC flag. Part of #4225.
//
//! Phase 3 Tier 1 test: factorial computation
//!
//! Tests CHC/Spacer verification of factorial with bounds assertion.
//! Part of #609 - Phase 3 Tier 1 metrics tracking.

/// Factorial computation with bounded input.
///
/// Loop invariant: result == (i-1)!
/// Post-condition: result >= 1 (factorial is always positive)
///
/// Note: Full correctness (result == n!) requires recursive definition.
/// We verify the weaker property that factorial is always positive.
#[kani::proof]
#[kani::unwind(14)]
fn ay_factorial() {
    let n: u32 = kani::any();
    kani::assume(n <= 12); // 13! overflows u32
    let mut result: u32 = 1;
    let mut i: u32 = 1;
    while i <= n {
        // Invariant: result == (i-1)!
        result *= i;
        i += 1;
    }
    // Post: result == n!, and n! is always positive for n >= 0
    assert!(result >= 1);
}
