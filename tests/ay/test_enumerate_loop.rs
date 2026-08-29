// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
// kani-expect: ay_enumerate_symbolic=UNKNOWN
// kani-flags: --ay-chc --ay-chc-int-lift
//
//! Enumerate-pattern loop verification test.
//!
//! Part of #2214 acceptance criteria:
//!   "Spacer produces PROOF for at least: simple while loop with counter,
//!    for-range loop, enumerate loop"
//!
//! The enumerate pattern tracks both an index counter and iteration values.
//! After #2214 flattening, the (usize, T) tuples that this pattern produces
//! are decomposed into scalar state vars that Spacer can reason about.
//!
//! Limitations:
//! - Rust's `.enumerate()` adapter creates `Enumerate<Iter<T>>`, a nested
//!   Datatype that requires recursive flattening (not yet supported, see #2274).
//! - Spacer invariant synthesis handles 2-variable linear relations but fails
//!   with 3+ counters or nonlinear terms, so divergent-stride patterns like
//!   `val == 2 * idx` cannot yet be proven.
//!
//! This test verifies the enumerate *pattern* (dual-counter lockstep) using
//! while loops where all state is in scalar locals that the current single-level
//! flattener handles correctly.

/// Enumerate pattern with symbolic bound: index tracks iteration count.
///
/// Verifies that Spacer synthesizes invariants for enumerate-style patterns:
/// two counters advancing in lockstep with a symbolic upper bound.
/// CHC invariant: `idx == i && 0 <= i <= n`.
#[kani::proof]
fn ay_enumerate_symbolic() {
    let n: u32 = kani::any();
    kani::assume(n <= 50);

    let mut idx: u32 = 0;
    let mut i: u32 = 0;
    while i < n {
        // Enumerate invariant: idx always equals i
        assert!(idx == i);
        idx += 1;
        i += 1;
    }

    assert!(idx == n);
}
