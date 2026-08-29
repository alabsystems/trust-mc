// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-expect: PROOF
// NOTE: Both alignment pass harnesses are PROOF at trust_mc 0a0dbc0198 / AY 733ba8cd.
// kani-flags: --ay-chc-track=ptr
//
//! Alignment verification tests (#712) — pass-only harnesses.
//!
//! These tests require Ptr track level because alignment checks depend on
//! concrete pointer addresses. At Reg level, pointer addresses are symbolic
//! state variables, making alignment checks vacuously satisfiable (#2064, #2079).
//!
//! Fail harnesses split to test_alignment_safety_fail.rs (Part of #3194).

/// This test should PASS - pointer is properly aligned.
#[kani::proof]
fn test_aligned_ptr_deref_pass() {
    let val: u64 = 0x123456789ABCDEF0;
    let p: *const u64 = &val as *const u64;

    // Pointer is derived from a properly aligned reference
    unsafe {
        let read_val = *p;
        assert!(read_val == 0x123456789ABCDEF0);
    }
}

/// This test should PASS - u8 has alignment 1, so any pointer is aligned.
#[kani::proof]
fn test_byte_ptr_any_offset_pass() {
    let arr: [u8; 8] = [10, 20, 30, 40, 50, 60, 70, 80];
    let idx: usize = kani::any();
    kani::assume(idx < 8);

    // u8 has alignment 1, so offset doesn't cause misalignment
    let p: *const u8 = unsafe { arr.as_ptr().add(idx) };

    unsafe {
        let _val = *p;
    }
}
