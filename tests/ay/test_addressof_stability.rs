// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: --ay-chc-track=reg
// kani-expect: PROOF
//
//! AddressOf stability tests at reg-level CHC mode — pass-only harnesses.
//!
//! - test_mut_ref_addressof_stability: PASSES at reg level. Pointer write-back
//!   through `as *mut T` casts works via ref_targets propagation
//!   (Part of #1978, commit 0a472257). Renamed from `_should_fail` (#2111).
//!
//! Split from test_addressof_stability_fail.rs (Part of #3194).

/// Test mutable reference address stability with pointer write-back.
/// Reg-level CHC now handles `*ptr = val` writes via ref_targets propagation,
/// so the pointer write-back correctly updates `x` (Part of #1978, #2111).
#[kani::proof]
fn test_mut_ref_addressof_stability() {
    let cond: bool = kani::any();
    let mut x: i32;

    let addr1: *mut i32;
    if cond {
        x = 20;
        addr1 = &mut x as *mut i32;
    } else {
        x = 30;
        addr1 = &mut x as *mut i32;
    }

    // Modify through pointer
    unsafe {
        *addr1 = 100;
    }

    // Value should be updated through the pointer
    kani::assert(x == 100, "write through pointer should update x");
}
