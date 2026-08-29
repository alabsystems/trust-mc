// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-expect: BMC_SAFE
// NOTE: CHC remains timing-sensitive here after false proof defense (ay#8578).
//
//! Test case for div_euclid/rem_euclid CHC dispatch (Part of #3186).
//!
//! Verifies the Euclidean division and remainder operations produce
//! correct results for unsigned types. Signed div_euclid/rem_euclid
//! are blocked on missing `wrapping_abs` CHC stub (#3293).

/// Unsigned rem_euclid: equivalent to regular remainder.
#[kani::proof]
fn test_u64_rem_euclid() {
    let x: u64 = kani::any();
    let y: u64 = kani::any();
    kani::assume(y != 0);
    // Constrain to avoid timeout on large values
    kani::assume(x < 1_000_000 && y < 1_000_000);

    let r = x.rem_euclid(y);
    assert!(r == x % y);
}

/// Unsigned div_euclid: equivalent to regular division.
#[kani::proof]
fn test_u32_div_euclid_simple() {
    let x: u32 = kani::any();
    let y: u32 = kani::any();
    kani::assume(y != 0);
    kani::assume(x < 10000 && y < 100);

    let q = x.div_euclid(y);
    assert!(q == x / y);
}

/// Unsigned rem_euclid for u8: small domain for solver.
#[kani::proof]
fn test_u8_rem_euclid() {
    let x: u8 = kani::any();
    let y: u8 = kani::any();
    kani::assume(y != 0);

    let r = x.rem_euclid(y);
    assert!(r == x % y);
}
