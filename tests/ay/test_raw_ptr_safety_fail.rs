// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// kani-verify-fail
// kani-expect: CTREX
//
//! Failing harnesses for raw pointer safety checks (#711, #713).
//!
//! Split from test_raw_ptr_safety.rs per #2292:
//! compiletest marks files as pass/fail, not individual harnesses.
//!
//! These harnesses SHOULD produce verification failures (counterexample found).
//! The `kani-verify-fail` directive tells ay-compiletest.sh this is expected.

use std::ptr;

// ============================================================================
// #711: Null pointer dereference tests (failing)
// ============================================================================

/// This test should FAIL - dereferencing a null raw pointer.
/// The null_pointer_check assertion should catch this.
#[kani::proof]
fn test_null_ptr_deref_fail() {
    let p: *const u32 = ptr::null();
    // Unsafe null dereference - should trigger null_pointer_check failure
    unsafe {
        let _val = *p;
    }
}

/// This test should FAIL - casting zero to pointer and dereferencing.
#[kani::proof]
fn test_zero_cast_ptr_deref_fail() {
    let p: *const i32 = 0 as *const i32;
    // Unsafe null dereference via integer cast - should fail
    unsafe {
        let _val = *p;
    }
}

// ============================================================================
// #713: Dead object (use-after-scope) tests (failing)
// ============================================================================

/// This test should FAIL - dereferencing pointer to out-of-scope local.
/// The dead_object assertion should catch this.
#[kani::proof]
fn test_dead_object_after_scope_fail() {
    let p: *const u32;

    {
        let x: u32 = 42;
        p = &x as *const u32;
        // x goes out of scope here
    }

    // Unsafe dereference of pointer to dead local - should trigger dead_object failure
    unsafe {
        let _val = *p;
    }
}

/// This test should FAIL - inner block local accessed after block ends.
#[kani::proof]
fn test_inner_block_dead_object_fail() {
    let ptr: *const i64;

    {
        let inner_val: i64 = kani::any();
        ptr = &inner_val as *const i64;
        // inner_val goes out of scope here
    }

    // Dereference after inner_val is dead
    unsafe {
        let _val = *ptr;
    }
}

/// This test should FAIL - nested scope with dead object.
#[kani::proof]
fn test_nested_scope_dead_object_fail() {
    let outer_ptr: *const u32;

    {
        let outer: u32 = 100;
        outer_ptr = &outer as *const u32;

        {
            let _inner: u32 = 200;
            // inner goes out of scope here
        }

        // outer is still alive here
        unsafe {
            let val = *outer_ptr;
            assert!(val == 100);
        }
        // outer goes out of scope here
    }

    // outer is dead now
    unsafe {
        let _val = *outer_ptr;
    }
}
