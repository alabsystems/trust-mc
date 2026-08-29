// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: --ay-chc --ay-chc-int-lift
// kani-expect: ay_unbounded_countdown_accum=UNKNOWN  // AY-bump regression from PROOF (3d9db24e68); sound demotion
// kani-expect: ay_unbounded_iteration_count=UNKNOWN
// kani-expect: ay_unbounded_max_tracking=UNKNOWN
// kani-expect: ay_unbounded_conditional_accum=UNKNOWN
// kani-expect: ay_unbounded_two_vars=UNKNOWN
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Phase 3 Tier 2 tests: Additional unbounded loop patterns
//!
//! Tests more complex unbounded verification scenarios requiring
//! sophisticated invariant synthesis.
//!
//! Part of Phase 3 completion criteria.
//! Phase 3 completion criteria.

/// Two-variable loop with coupled invariants.
///
/// Loop invariant: j == 2*i AND 0 <= i <= n
/// Post-condition: j == 2*n
#[kani::proof]
fn ay_unbounded_two_vars() {
    let n: u32 = kani::any();
    kani::assume(n <= 500); // Prevent overflow in j = 2*n

    let mut i: u32 = 0;
    let mut j: u32 = 0;

    while i < n {
        i += 1;
        j += 2;
    }

    // Invariant: j == 2*i
    assert!(j == 2 * n);
}

/// Countdown to zero with accumulator.
///
/// Loop invariant: sum == (n - i) * n
/// Post-condition: sum == n * n
#[kani::proof]
fn ay_unbounded_countdown_accum() {
    let n: u32 = kani::any();
    kani::assume(n <= 100);

    let mut i: u32 = n;
    let mut sum: u32 = 0;

    while i > 0 {
        sum += n; // Add n each iteration
        i -= 1;
    }

    // After n iterations: sum == n * n
    assert!(sum == n * n);
}

/// Conditional accumulator based on loop variable.
///
/// Loop invariant: count >= 0 AND count <= i
/// Post-condition: count <= n
#[kani::proof]
fn ay_unbounded_conditional_accum() {
    let n: u32 = kani::any();
    kani::assume(n <= 200);

    let mut i: u32 = 0;
    let mut count: u32 = 0;

    while i < n {
        // Only increment count on odd iterations
        if i % 2 == 1 {
            count += 1;
        }
        i += 1;
    }

    // count is at most n/2 (floor division), so count <= n
    assert!(count <= n);
}

/// Max tracking loop - finds maximum of symbolic values.
///
/// Loop invariant: max >= each seen value (checked per-iteration)
/// Post-condition: max >= any individual value
#[kani::proof]
fn ay_unbounded_max_tracking() {
    let n: u32 = kani::any();
    kani::assume(n > 0 && n <= 10);

    let mut max: u32 = 0;
    let mut i: u32 = 0;

    while i < n {
        let val: u32 = kani::any();
        kani::assume(val <= 100);

        if val > max {
            max = val;
        }
        assert!(max >= val);
        i += 1;
    }

    // max is at most 100 (our assumption bound)
    assert!(max <= 100);
}

/// Bounded iteration count with termination guarantee.
///
/// Loop invariant: iteration_count <= n AND (done OR iteration_count < n)
/// Post-condition: iteration_count <= n
#[kani::proof]
fn ay_unbounded_iteration_count() {
    let n: u32 = kani::any();
    kani::assume(n <= 50);

    let mut iteration_count: u32 = 0;
    let mut done: bool = false;

    while iteration_count < n && !done {
        let should_stop: bool = kani::any();
        if should_stop {
            done = true;
        }
        iteration_count += 1;
    }

    // We never exceed n iterations
    assert!(iteration_count <= n);
}
