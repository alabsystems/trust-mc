// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
// kani-expect: UNKNOWN
// NOTE: All harnesses demoted PROOF→UNKNOWN by false proof defense (ay#8578).
// kani-flags: --ay-chc --ay-chc-int-lift
//
//! Phase 3 Tier 1 test: simple_while - Unbounded loop verification via CHC/Spacer.
//!
//! Aligns with Phase 3 Tier 1 `simple_while` criterion.
//! See VISION.md for full Phase 3 criteria.
//!
//! This test verifies the Phase 3 completion criterion from VISION.md:
//! "Done when: Verify simple loops without explicit bounds"
//!
//! **Key distinction from Phase 5 tests:**
//! - Single loop, primitive types, no heap allocations
//! - Symbolic upper bound forces unbounded reasoning
//! - No `#[kani::unwind]` annotation
//!
//! **Expected behavior:**
//! - CHC/Spacer synthesizes invariant: `0 <= i <= n`
//! - Verifies postcondition: `i == n` at loop exit
//!
//! Part of #599 (Phase 3 completion test)

/// Simple unbounded loop counting to a symbolic bound.
///
/// CHC/Spacer should synthesize the invariant `0 <= i <= n` to prove
/// the postcondition holds for all valid values of `n`.
#[kani::proof]
fn ay_unbounded_simple_loop() {
    let n: u32 = kani::any();
    kani::assume(n < 1_000_000);

    let mut i: u32 = 0;
    while i < n {
        i += 1;
    }

    assert!(i == n);
}
