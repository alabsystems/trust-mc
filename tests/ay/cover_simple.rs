// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-expect: PROOF
//
//! Test file for #922 - cover property result reporting in AY backend.

/// Simple cover test - should report SATISFIED
#[kani::proof]
fn test_cover_reachable() {
    let x: u32 = kani::any();
    kani::assume(x < 100);
    // This condition is reachable when x == 50
    kani::cover!(x == 50, "x equals 50");
}

/// Cover test with always-reachable condition
#[kani::proof]
fn test_cover_always_reachable() {
    let x: bool = kani::any();
    // This is always reachable (x can be true or false)
    kani::cover!(x, "x is true");
}
