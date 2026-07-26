// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// kani-verify-fail
// kani-expect: CTREX
// soundness-accepted-verdict: UNKNOWN
// kani-flags: --ay-chc-track=ptr
//
//! Size mismatch regression harness for trust_mc (#1174).
//!
//! This harness intentionally deallocates memory with a wrong size.
//! The AY memory model should detect the size mismatch:
//! - obj_size[obj_id] records the allocation size
//! - dealloc checks: dealloc_size == obj_size[obj_id]
//! - Mismatch triggers safety check failure
//!
//! Rust's allocator contract requires dealloc size to match alloc size.
//! This is UB in real Rust; trust_mc should detect it during verification.
//!
//! CTREX is preferred for the size mismatch. `UNKNOWN` is accepted only as a
//! fail-closed non-PROOF outcome; any `PROOF` result is a false proof
//! regression.

use std::alloc::{Layout, alloc, dealloc};

/// This test should FAIL - deallocation with wrong size.
#[kani::proof]
fn test_heap_size_mismatch_should_fail() {
    unsafe {
        // Allocate 64 bytes
        let layout_alloc = Layout::from_size_align(64, 8).unwrap();
        let ptr = alloc(layout_alloc);

        if !ptr.is_null() {
            // Write something to the allocated memory
            *ptr = 42;

            // WRONG: Deallocate with 32 bytes instead of 64
            // The memory model should detect: obj_size[obj_id] == 64 != 32
            let layout_dealloc = Layout::from_size_align(32, 8).unwrap();
            dealloc(ptr, layout_dealloc);
        }
    }
}
