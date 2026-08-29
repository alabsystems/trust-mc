// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// kani-verify-fail
//
//! Alignment verification fail tests (#712) — expected-CTREX harnesses.
//!
//! These tests require Ptr track level because alignment checks depend on
//! concrete pointer addresses. At Reg level, pointer addresses are symbolic
//! state variables, making alignment checks vacuously satisfiable (#2064, #2079).
//!
//! Split from test_alignment_safety.rs (Part of #3194).
// kani-expect: CTREX
// kani-flags: --ay-chc-track=ptr

/// This test should FAIL - dereferencing a misaligned pointer.
/// The alignment_check assertion should catch this.
#[kani::proof]
fn test_misaligned_ptr_deref_fail() {
    // Create an array of bytes
    let bytes: [u8; 8] = [1, 2, 3, 4, 5, 6, 7, 8];

    // Get pointer to bytes[1], which is NOT aligned for u32 (requires 4-byte alignment)
    let misaligned_ptr: *const u32 = unsafe { bytes.as_ptr().add(1) as *const u32 };

    // Unsafe misaligned dereference - should trigger alignment_check failure
    unsafe {
        let _val = *misaligned_ptr;
    }
}

/// This test should FAIL - offset creates misalignment.
#[kani::proof]
fn test_offset_misaligned_fail() {
    let arr: [u8; 16] = [0; 16];
    let base_ptr = arr.as_ptr();

    // Offset by 3 bytes, then cast to u64 pointer (requires 8-byte alignment)
    let misaligned: *const u64 = unsafe { base_ptr.add(3) as *const u64 };

    // Unsafe misaligned dereference
    unsafe {
        let _val = *misaligned;
    }
}
