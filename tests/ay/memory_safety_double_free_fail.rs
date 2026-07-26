// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// kani-verify-fail
// kani-expect: CTREX
// kani-flags: --ay-chc-track=ptr
//
//! Double-free regression harness for trust_mc (#1034).
//!
//! This harness intentionally frees the same allocation twice. The AY
//! memory model should reject the second deallocation if `dealloc_ok`
//! is asserted before each `deallocate` call.
//!
//! Note: The memory model's `deallocate` is idempotent by design. Double-free
//! detection requires asserting `dealloc_ok(ptr)` before each deallocation.
//! This test validates that the precondition mechanism works correctly.

/// This test should FAIL - double-free on a heap allocation.
///
/// The test pattern:
/// 1. Allocate memory
/// 2. Free it (valid)
/// 3. Free it again (invalid - should be detected)
#[kani::proof]
fn test_heap_double_free_should_fail() {
    let ptr: *mut u32 = Box::into_raw(Box::new(456));

    unsafe {
        // First free - valid
        drop(Box::from_raw(ptr));

        // Second free - double-free, should be detected
        // Note: In real Rust this is UB. In verification, the memory model
        // should flag this as invalid if dealloc_ok is checked.
        drop(Box::from_raw(ptr));
    }
}
