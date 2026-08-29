// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: --ay-chc --ay-chc-int-lift
// kani-expect: ay_while_countdown=UNKNOWN
// kani-expect: ay_while_early_exit=UNKNOWN
// kani-expect: ay_while_nested_condition=UNKNOWN
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Phase 3 Tier 2 tests: While loop patterns
//!
//! Tests more complex while loop patterns beyond basic Tier 1 counting loops.
//! These require CHC/Spacer to synthesize more complex invariants.
//!
//! Part of Phase 3 completion criteria.
//! Phase 3 completion criteria.

/// While loop with countdown (decrement pattern).
///
/// Loop invariant: 0 <= i <= n
/// Post-condition: i == 0
#[kani::proof]
fn ay_while_countdown() {
    let n: u32 = kani::any();
    kani::assume(n <= 1000);

    let mut i: u32 = n;
    while i > 0 {
        i -= 1;
    }

    assert!(i == 0);
}

/// While loop with nested condition in body.
///
/// Loop invariant: 0 <= i <= n AND sum <= i
/// Post-condition: sum <= n
#[kani::proof]
fn ay_while_nested_condition() {
    let n: u32 = kani::any();
    kani::assume(n <= 100);

    let mut i: u32 = 0;
    let mut sum: u32 = 0;

    while i < n {
        // Conditionally increment sum
        if i % 2 == 0 {
            sum += 1;
        }
        i += 1;
    }

    // Sum of even indices from 0 to n-1 is at most n
    assert!(sum <= n);
}

/// While loop with potential early termination (break equivalent).
///
/// Tests CHC handling of loops that may terminate before bound.
/// Loop invariant: 0 <= i <= n
#[kani::proof]
fn ay_while_early_exit() {
    let n: u32 = kani::any();
    let target: u32 = kani::any();
    kani::assume(n <= 100);

    let mut i: u32 = 0;
    let mut found: bool = false;

    while i < n && !found {
        if i == target {
            found = true;
        }
        i += 1;
    }

    // If target < n, found should be true
    // If target >= n, found should be false
    // In all cases, i <= n
    assert!(i <= n);
}
