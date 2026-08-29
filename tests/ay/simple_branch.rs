// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-expect: BMC_SAFE
// Routed by lane_policy.toml: acyclic if/else BV32 control flow is bounded and
// BMC discharges it directly, avoiding the historical CHC/Spacer UNKNOWN.
//
//! Simple branching test for AY backend.
//!
//! Tests SwitchInt terminator handling for conditionals.

#[kani::proof]
fn test_simple_if() {
    let x: i32 = kani::any();
    let y: i32;
    if x > 0 {
        y = 1;
    } else {
        y = 2;
    }
    // y should be either 1 or 2, never 0
    assert!(y == 1 || y == 2);
}

#[kani::proof]
fn test_positive_branch() {
    let x: i32 = kani::any();
    kani::assume(x > 0);
    if x > 0 {
        assert!(true); // Should pass - this branch is taken
    } else {
        assert!(false); // Should never reach - but currently does with broken SwitchInt!
    }
}
