// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: --ay-chc-int-lift
// kani-expect: ay_loop_conditional_break=UNKNOWN
// kani-expect: ay_loop_multiple_exits=UNKNOWN
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Phase 3 Tier 2 tests: Infinite loop patterns
//!
//! Tests Rust's `loop` construct which creates infinite loops
//! that must be exited via `break` or `return`.
//!
//! Part of Phase 3 completion criteria.
//! Phase 3 completion criteria.

/// Infinite loop with conditional break.
///
/// Loop invariant: 0 <= i <= n
/// Post-condition: i == n (exits when condition met)
#[kani::proof]
fn ay_loop_conditional_break() {
    let n: u32 = kani::any();
    kani::assume(n <= 1000);
    kani::assume(n > 0); // Ensure we can exit

    let mut i: u32 = 0;

    loop {
        i += 1;
        if i >= n {
            break;
        }
    }

    assert!(i == n);
}

/// Infinite loop with multiple potential exit conditions.
///
/// Tests CHC handling of disjunctive exit conditions.
/// Loop invariant: 0 <= i AND 0 <= j (j increments by 2, may exceed m)
#[kani::proof]
fn ay_loop_multiple_exits() {
    let n: u32 = kani::any();
    let m: u32 = kani::any();
    kani::assume(n <= 100);
    kani::assume(m <= 100);
    kani::assume(n > 0 || m > 0); // At least one will trigger exit

    let mut i: u32 = 0;
    let mut j: u32 = 0;

    loop {
        i += 1;
        j += 2;

        // Exit on first condition met
        if i >= n {
            break;
        }
        if j >= m {
            break;
        }
    }

    // One of these must be true when we exit
    assert!(i >= n || j >= m);
}
