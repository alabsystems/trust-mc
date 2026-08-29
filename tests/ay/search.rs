// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-expect: UNKNOWN
//
//! Phase 3 Tier 1 test: linear search
//!
//! Tests CHC/Spacer verification of linear search in a fixed array.
//! Part of #609 - Phase 3 Tier 1 metrics tracking.

/// Linear search in a fixed-size array.
///
/// Loop invariant: found == (target in arr[0..i])
/// Post-condition: i == 10 (loop completes all iterations)
///
/// Note: Full correctness (found iff target in arr) requires quantifiers.
/// We verify the simpler property that the loop completes.
#[kani::proof]
fn ay_linear_search() {
    let arr: [u32; 10] = kani::any();
    let target: u32 = kani::any();
    let mut found: bool = false;
    let mut i: u32 = 0;
    // Invariant: found == (target in arr[0..i])
    while i < 10 {
        if arr[i as usize] == target {
            found = true;
        }
        i += 1;
    }
    // Post: loop completes, i == 10
    assert!(i == 10);
    // Suppress unused variable warning
    let _ = found;
}
