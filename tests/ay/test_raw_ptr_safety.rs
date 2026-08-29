// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-expect: PROOF
// NOTE: All 5 harnesses now PROOF at ay 65537dc81 (false proof defense no longer triggers).
//
//! Test cases for raw pointer safety checks (#711, #713) — passing harnesses.
//!
//! Failing harnesses moved to test_raw_ptr_safety_fail.rs per #2292:
//! compiletest marks files as pass/fail, not individual harnesses.
//!
//! Alignment tests (#712) moved to test_alignment_safety.rs (requires Ptr track level).

use std::mem;

// ============================================================================
// #711: Null pointer dereference tests (passing)
// ============================================================================

/// This test should PASS - pointer is checked to be non-null before deref.
#[kani::proof]
fn test_null_ptr_guarded_pass() {
    let x: u32 = 42;
    let p: *const u32 = &x as *const u32;

    // Pointer is derived from a valid reference, so it's non-null
    unsafe {
        let val = *p;
        assert!(val == 42);
    }
}

/// This test should PASS - symbolic pointer checked against null.
#[kani::proof]
fn test_symbolic_ptr_null_check_pass() {
    let x: u64 = kani::any();
    let p: *const u64 = &x as *const u64;

    // The pointer is derived from a reference to x, which is on the stack
    // and guaranteed non-null
    unsafe {
        let val = *p;
        // Should read the symbolic value back
        assert!(val == x);
    }
}

// ============================================================================
// #713: Dead object (use-after-scope) tests (passing)
// ============================================================================

/// This test should PASS - pointer is used while local is still alive.
#[kani::proof]
fn test_ptr_in_scope_pass() {
    let x: u32 = 42;
    let p: *const u32 = &x as *const u32;

    // Pointer is used while x is still in scope
    unsafe {
        let val = *p;
        assert!(val == 42);
    }
}

/// This test should PASS - pointer used in same scope.
#[kani::proof]
fn test_same_scope_ptr_pass() {
    let val: u64 = kani::any();
    let ptr: *const u64 = &val as *const u64;

    unsafe {
        let read = *ptr;
        // Value should match since val is still alive
        assert!(read == val);
    }
}

// ============================================================================
// #1136: Raw pointer field address-of should apply field offset
// ============================================================================

#[repr(C)]
struct Pair {
    a: u32,
    b: u32,
}

/// This test should PASS - &(*ptr).b should be offset from ptr, not ptr itself.
#[kani::proof]
fn test_raw_ptr_field_address_offset() {
    let val = Pair { a: 1, b: 2 };
    let ptr: *const Pair = &val as *const Pair;

    unsafe {
        let field_ptr = &(*ptr).b as *const u32;
        let expected = (ptr as *const u8).add(mem::size_of::<u32>()) as *const u32;
        assert!(field_ptr == expected);
    }
}
