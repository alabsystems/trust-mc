// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: --ay-chc-int-lift
// kani-expect: UNKNOWN
// NOTE: All harnesses demoted PROOF→UNKNOWN by false proof defense (ay#8578).
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Phase 5 test: Unbounded loop verification via CHC/Spacer.
//!
//! This test demonstrates trust_mc's core value proposition over Kani/CBMC:
//! verifying unbounded loops without explicit unwind bounds.
//!
//! **Why CBMC fails**: BMC must unroll loops to a fixed bound. With symbolic `n`,
//! CBMC would need `#[kani::unwind(N)]` where N >= max(n). No finite N works.
//!
//! **Why CHC succeeds**: CHC/Spacer finds the loop invariant `i <= n` inductively,
//! proving the property for ALL values of n without enumeration.
//!
//! Part of #470, #16 (Phase 5: BigInt/HashMap Verification)
//!
//! Phase 5 completion criteria (Test 6)
//!
//! Success criteria:
//! - trust_mc: Proves in <30s without unwind annotation
//! - Kani/CBMC: Requires concrete unwind, proof incomplete for n > unwind

/// Simple unbounded loop - cannot be verified by BMC without known bound.
///
/// The loop invariant is: `0 <= i <= n`
/// The postcondition is: `i == n` (when loop terminates)
fn count_to_n(n: u64) -> u64 {
    let mut i: u64 = 0;
    while i < n {
        i += 1;
    }
    i
}

/// Verify that count_to_n(n) returns exactly n.
///
/// This property holds for all n, but BMC cannot prove it without
/// unrolling n times. CHC proves it inductively.
#[kani::proof]
fn verify_count_equals_n() {
    let n: u64 = kani::any();
    // Prevent unrealistic values that would cause overflow
    kani::assume(n < 1_000_000_000);

    let result = count_to_n(n);

    assert_eq!(result, n);
}

/// Verify that count_to_n always returns a value <= input.
///
/// Simpler property that CHC should find easily via invariant `i <= n`.
#[kani::proof]
fn verify_count_bounded() {
    let n: u64 = kani::any();
    kani::assume(n < 1_000_000_000);

    let result = count_to_n(n);

    assert!(result <= n);
}

/// Verify loop reaches exactly the target - no overshoot.
///
/// This tests that the loop terminates precisely at n, not beyond.
/// Requires CHC to reason that while condition i < n prevents overshoot.
#[kani::proof]
fn verify_count_no_overshoot() {
    let n: u64 = kani::any();
    kani::assume(n > 0 && n < 1_000_000_000);

    let result = count_to_n(n);

    // Property: result is exactly n, not greater
    // This requires proving the loop condition i < n is tight
    assert!(result >= n); // Combined with verify_count_bounded (result <= n), proves result == n
}
