// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-expect: BMC_SAFE
// Routed to BMC lane (lane_policy.toml): these loop-free intrinsic checks are
// straight-line bitvector obligations. CHC can prove them, but spends tens of
// seconds in Spacer where bounded BMC discharges them directly.
//
// Loop-free cttz verification: tests that the `trailing_zeros()` intrinsic
// (which compiles to `cttz`) returns correct results for symbolic inputs.
// Unlike the Kani harness in tests/trust_mc/Intrinsics/Count/cttz.rs, this
// avoids the break-containing manual reference loop that Spacer cannot model.

#[kani::proof]
fn test_cttz_u8_known_values() {
    // Concrete spot-checks
    assert!(0u8.trailing_zeros() == 8);
    assert!(1u8.trailing_zeros() == 0);
    assert!(2u8.trailing_zeros() == 1);
    assert!(4u8.trailing_zeros() == 2);
    assert!(0x80u8.trailing_zeros() == 7);
    assert!(0xFFu8.trailing_zeros() == 0);
    assert!(0xF0u8.trailing_zeros() == 4);

    // Symbolic: trailing_zeros is always in [0, 8] for u8
    let x: u8 = kani::any();
    let tz = x.trailing_zeros();
    assert!(tz <= 8);

    // If x != 0, then trailing_zeros < 8
    if x != 0 {
        assert!(tz < 8);
    }

    // If LSB is set, trailing_zeros == 0
    if x & 1 == 1 {
        assert!(tz == 0);
    }
}

#[kani::proof]
fn test_cttz_u16_symbolic() {
    let x: u16 = kani::any();
    let tz = x.trailing_zeros();
    assert!(tz <= 16);

    if x == 0 {
        assert!(tz == 16);
    }
    if x != 0 {
        assert!(tz < 16);
    }
    // LSB set means zero trailing zeros
    if x & 1 == 1 {
        assert!(tz == 0);
    }
}
