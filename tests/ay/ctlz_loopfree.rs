// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-expect: BMC_SAFE
// Routed to BMC lane (lane_policy.toml): these loop-free intrinsic checks are
// straight-line bitvector obligations. CHC returns UNKNOWN/timeouts on the
// symbolic ctlz cases, while bounded BMC discharges them directly.
//
// Loop-free ctlz verification: tests that the `leading_zeros()` intrinsic
// (which compiles to `ctlz`) returns correct results for symbolic inputs.
// Unlike the Kani harness in tests/trust_mc/Intrinsics/Count/ctlz.rs, this
// avoids the break-containing manual reference loop that Spacer cannot model.

#[kani::proof]
fn test_ctlz_u8_known_values() {
    // Concrete spot-checks
    assert!(0u8.leading_zeros() == 8);
    assert!(1u8.leading_zeros() == 7);
    assert!(0x80u8.leading_zeros() == 0);
    assert!(0x40u8.leading_zeros() == 1);
    assert!(0xFFu8.leading_zeros() == 0);
    assert!(0x0Fu8.leading_zeros() == 4);

    // Symbolic: leading_zeros is always in [0, 8] for u8
    let x: u8 = kani::any();
    let lz = x.leading_zeros();
    assert!(lz <= 8);

    // If x != 0, then leading_zeros < 8
    if x != 0 {
        assert!(lz < 8);
    }

    // If MSB is set, leading_zeros == 0
    if x >= 128 {
        assert!(lz == 0);
    }
}

#[kani::proof]
fn test_ctlz_u16_symbolic() {
    let x: u16 = kani::any();
    let lz = x.leading_zeros();
    assert!(lz <= 16);

    if x == 0 {
        assert!(lz == 16);
    }
    if x != 0 {
        assert!(lz < 16);
    }
    // MSB set means zero leading zeros
    if x >= 0x8000 {
        assert!(lz == 0);
    }
}
