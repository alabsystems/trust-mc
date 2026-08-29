// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-expect: BMC_SAFE
//
//! Test case for SIGNED div_euclid/rem_euclid CHC dispatch (Part of #3293).
//!
//! These harnesses were blocked by the missing `wrapping_abs` CHC stub.
//! Signed euclid operations call `wrapping_abs` internally, which had no
//! CHC encoding — falling through to unconstrained → spurious CTREX.

/// Signed rem_euclid: remainder is always non-negative.
#[kani::proof]
fn test_i32_rem_euclid() {
    let x: i32 = kani::any();
    let y: i32 = kani::any();
    kani::assume(y != 0);
    kani::assume(x > -100 && x < 100 && y > -100 && y < 100);
    let r = x.rem_euclid(y);
    assert!(r >= 0 && r < y.wrapping_abs());
}

/// Signed div_euclid with concrete values.
#[kani::proof]
fn test_i32_div_euclid_concrete() {
    let q = (-7i32).div_euclid(4);
    let r = (-7i32).rem_euclid(4);
    // -7 = 4 * (-2) + 1, so q = -2, r = 1
    assert!(q == -2);
    assert!(r == 1);
}

/// Signed rem_euclid with positive divisor: remainder bounded by divisor.
#[kani::proof]
fn test_i32_rem_euclid_positive_divisor() {
    let x: i32 = kani::any();
    kani::assume(x > -100 && x < 100);
    let r = x.rem_euclid(7);
    // Euclidean remainder is always in [0, |divisor|)
    assert!(r >= 0 && r < 7);
}
