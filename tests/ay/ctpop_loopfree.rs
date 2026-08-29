// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-expect: BMC_SAFE
// Routed to BMC lane (lane_policy.toml): these loop-free intrinsic checks are
// straight-line bitvector obligations. CHC returns UNKNOWN/timeouts on the
// symbolic ctpop cases, while bounded BMC discharges them directly.
//
// Loop-free ctpop verification: tests that the `count_ones()` intrinsic
// (which compiles to `ctpop`) returns correct results for symbolic inputs.
// Uses property-based checks instead of a manual reference loop.

#[kani::proof]
fn test_ctpop_u8_known_values() {
    // Concrete spot-checks
    assert!(0u8.count_ones() == 0);
    assert!(1u8.count_ones() == 1);
    assert!(0xFFu8.count_ones() == 8);
    assert!(0x0Fu8.count_ones() == 4);
    assert!(0xAAu8.count_ones() == 4);
    assert!(0x55u8.count_ones() == 4);
    assert!(0x80u8.count_ones() == 1);

    // Symbolic: count_ones is always in [0, 8] for u8
    let x: u8 = kani::any();
    let pop = x.count_ones();
    assert!(pop <= 8);

    // Zero has zero bits set
    if x == 0 {
        assert!(pop == 0);
    }

    // Complementary property: count_ones(x) + count_ones(!x) == 8
    let complement_pop = (!x).count_ones();
    assert!(pop + complement_pop == 8);
}

#[kani::proof]
fn test_ctpop_u16_symbolic() {
    let x: u16 = kani::any();
    let pop = x.count_ones();
    assert!(pop <= 16);

    if x == 0 {
        assert!(pop == 0);
    }

    // Complementary property
    let complement_pop = (!x).count_ones();
    assert!(pop + complement_pop == 16);
}
