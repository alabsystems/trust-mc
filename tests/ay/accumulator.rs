// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: --ay-chc --ay-chc-int-lift
// kani-expect: UNKNOWN
//
//! Phase 3 Tier 1 test: accumulator loop
//!
//! Tests CHC/Spacer verification of a sum accumulator with symbolic bound.
//! Part of #609 - Phase 3 Tier 1 metrics tracking.

/// Sum accumulator with symbolic bound.
///
/// Loop invariant: sum == 0 + 1 + 2 + ... + (i-1) = i*(i-1)/2
/// Post-condition: sum <= n*n (conservative quadratic bound)
#[kani::proof]
#[kani::unwind(102)]
fn ay_accumulator() {
    let n: u32 = kani::any();
    kani::assume(n <= 100);
    let mut sum: u32 = 0;
    let mut i: u32 = 0;
    while i < n {
        // Invariant: sum == i*(i-1)/2
        sum += i;
        i += 1;
    }
    // Sum of 0..n = n*(n-1)/2 < n*n
    assert!(sum <= n * n);
}
