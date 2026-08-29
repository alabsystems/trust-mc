// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-expect: PROOF
// kani-expect: copy_bool_with_dynamic_count=BMC_SAFE
// kani-expect: copy_with_dynamic_count=BMC_SAFE
//
//! Test copy_nonoverlapping with dynamic (non-constant) count.
//!
//! The constant/zero-count harnesses remain CHC PROOF after #3665's
//! ub_checks::maybe_is_aligned stub name fix. The two symbolic-count harnesses
//! are acyclic but produce guarded copy/validity state that times out in Spacer,
//! so lane_policy.toml routes them through direct BMC.
//!
//! Part of #698: Verify that copy_nonoverlapping with dynamic counts is handled
//! correctly by the validity checking pass. The pass should:
//! - Not emit UnsupportedCheck for dynamic counts
//! - Use a guarded validity check: count == 0 || validity_check
//! - Avoid false positives when count is 0
//!
//! This test exercises the dynamic count code path.

use std::ptr;

/// Test copy_nonoverlapping with a symbolic (dynamic) count.
/// The count value is determined at runtime via kani::any().
///
/// Uses individual guarded assertions instead of a `for i in 0..count` loop
/// because CHC/Spacer cannot synthesize the quantified array invariant needed
/// for loops over symbolic bounds with array equality checks.
#[kani::proof]
fn copy_with_dynamic_count() {
    let src: [u8; 4] = [1, 2, 3, 4];
    let mut dst: [u8; 4] = [0; 4];

    // Dynamic count - not known at compile time
    let count: usize = kani::any();
    kani::assume(count <= 4);

    unsafe {
        ptr::copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr(), count);
    }

    // Verify the copy worked correctly for the given count.
    // Individual guarded assertions avoid the need for a loop invariant.
    if count > 0 {
        assert!(dst[0] == src[0]);
    }
    if count > 1 {
        assert!(dst[1] == src[1]);
    }
    if count > 2 {
        assert!(dst[2] == src[2]);
    }
    if count > 3 {
        assert!(dst[3] == src[3]);
    }
}

/// Test copy_nonoverlapping with count == 0.
/// This should not trigger any validity check failures.
#[kani::proof]
fn copy_with_zero_count() {
    let src: [u8; 4] = [1, 2, 3, 4];
    let mut dst: [u8; 4] = [0; 4];

    // Zero count - no bytes should be copied, no validity check should run
    unsafe {
        ptr::copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr(), 0);
    }

    // Destination should be unchanged
    assert!(dst == [0, 0, 0, 0]);
}

/// Test copy_nonoverlapping with a type that has validity constraints (bool).
/// Bool only has valid values 0 and 1, so this actually exercises the
/// GuardedDerefValidity path (Part of #698).
///
/// Note: The tests above use u8 which has no validity constraints, so they
/// don't exercise the guarded validity check at all.
///
/// Uses individual guarded assertions (same rationale as copy_with_dynamic_count).
#[kani::proof]
fn copy_bool_with_dynamic_count() {
    let src: [bool; 4] = [true, false, true, false];
    let mut dst: [bool; 4] = [false; 4];

    // Dynamic count - exercises GuardedDerefValidity since bool has validity constraints
    let count: usize = kani::any();
    kani::assume(count <= 4);

    unsafe {
        ptr::copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr(), count);
    }

    // Verify the copy worked correctly for the given count.
    if count > 0 {
        assert!(dst[0] == src[0]);
    }
    if count > 1 {
        assert!(dst[1] == src[1]);
    }
    if count > 2 {
        assert!(dst[2] == src[2]);
    }
    if count > 3 {
        assert!(dst[3] == src[3]);
    }
}

/// Test copy_nonoverlapping with bool and count == 0.
/// This verifies the guard (count == 0) prevents false positives even
/// for types with validity constraints.
#[kani::proof]
fn copy_bool_with_zero_count() {
    let src: [bool; 4] = [true, false, true, false];
    let mut dst: [bool; 4] = [false; 4];

    // Zero count - guard should skip validity check
    unsafe {
        ptr::copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr(), 0);
    }

    // Destination should be unchanged
    assert!(dst == [false, false, false, false]);
}

/// Minimal test: copy_nonoverlapping with raw pointer casts (no as_ptr/as_mut_ptr
/// method call transitions) and smaller arrays. PROOF after #3665 fixed the
/// ub_checks::maybe_is_aligned stub name mismatch (Rust nightly 2025-12-03
/// renamed the function, dropping the `_and_not_null` suffix).
#[kani::proof]
fn copy_raw_ptr_constant() {
    let src: [u8; 2] = [1, 2];
    let mut dst: [u8; 2] = [0, 0];
    unsafe {
        // Raw pointer casts: these are MIR Cast statements, not Call terminators.
        // This eliminates 2 basic block transitions vs as_ptr/as_mut_ptr.
        core::ptr::copy_nonoverlapping(
            &src as *const [u8; 2] as *const u8,
            &mut dst as *mut [u8; 2] as *mut u8,
            2,
        );
    }
    assert!(dst[0] == 1);
    assert!(dst[1] == 2);
}
