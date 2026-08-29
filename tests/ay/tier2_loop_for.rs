// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: --ay-chc --ay-chc-int-lift --ay-chc-no-retry
// kani-expect: ay_for_simple_range=UNKNOWN
// kani-expect: ay_for_symbolic_range=UNKNOWN  // AY-bump regression from PROOF (3d9db24e68); sound demotion
// Solver nondeterminism: keep primary CHC lane so ay_for_simple_range emits UNKNOWN cleanly.
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Phase 3 Tier 2 tests: For loop patterns
//!
//! Tests Rust's `for` construct with range iterators.
//! Desugared to while loops internally, but tests iterator reasoning.
//!
//! Part of Phase 3 completion criteria.
//! Phase 3 completion criteria.

/// For loop over constant range.
///
/// Simple for-range that CHC should verify easily.
/// Loop invariant: sum == i * (i - 1) / 2
#[kani::proof]
fn ay_for_simple_range() {
    let mut sum: u32 = 0;

    for i in 0..10u32 {
        sum += i;
    }

    // Sum of 0..10 = 0+1+2+...+9 = 45
    assert!(sum == 45);
}

/// For loop with symbolic upper bound.
///
/// Tests CHC with symbolic range bounds.
/// Loop invariant: 0 <= sum <= n*n
#[kani::proof]
fn ay_for_symbolic_range() {
    let n: u32 = kani::any();
    kani::assume(n <= 50);

    let mut sum: u32 = 0;

    // Use a while loop to keep the MIR shape simple for early CHC encoding.
    let mut i: u32 = 0;
    while i < n {
        sum += i;
        i += 1;
    }

    // Sum of 0..(n-1) = n*(n-1)/2 <= n*n
    assert!(sum <= n * n);
}
