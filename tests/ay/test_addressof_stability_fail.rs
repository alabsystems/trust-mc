// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: --ay-chc-track=reg
//
// kani-verify-fail
//
//! AddressOf stability fail test at reg-level CHC mode.
//!
//! - test_addressof_loop_stability_should_fail: Still fails (expected CTREX).
//!   Loop-aware address tracking not yet implemented.
//!
//! Pass harness split to test_addressof_stability.rs (Part of #3194).
// kani-expect: CTREX

/// Test address stability with loop iteration.
/// Each iteration should produce the same address for the same variable.
/// This test fails because loop handling creates separate iterations with
/// potentially different ref_pointees entries.
/// Blocked by: loop-aware address tracking.
#[kani::proof]
fn test_addressof_loop_stability_should_fail() {
    let mut x: i32 = 0;
    let iterations: u32 = kani::any();
    kani::assume(iterations <= 3);

    let mut first_addr: *const i32 = std::ptr::null();
    let mut i: u32 = 0;

    while i < iterations {
        x = x + 1;
        let current_addr: *const i32 = &x as *const i32;

        if i == 0 {
            first_addr = current_addr;
        } else {
            // Address should be stable across loop iterations
            // Fails because loop iterations don't share ref_pointees
            kani::assert(current_addr == first_addr, "address stable across loop iterations");
        }
        i = i + 1;
    }
}
