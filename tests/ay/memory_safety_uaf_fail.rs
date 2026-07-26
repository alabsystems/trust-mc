// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// kani-verify-fail
// kani-expect: CTREX
// soundness-accepted-verdict: UNKNOWN
// kani-flags: --ay-chc-track=ptr
//
//! Use-after-free regression harness for trust_mc (#1032).
//!
//! This harness intentionally dereferences a freed heap pointer. The AY
//! memory model should reject the invalid dereference (object_valid=false).
//! `UNKNOWN` is an accepted fail-closed outcome for the soundness ledger; any
//! `PROOF` result is a false proof regression.

/// This test should FAIL - use-after-free on a heap allocation.
#[kani::proof]
fn test_heap_use_after_free_should_fail() {
    let ptr: *mut u32 = Box::into_raw(Box::new(123));

    unsafe {
        // Free the allocation.
        drop(Box::from_raw(ptr));

        // Use-after-free: invalid dereference should be detected.
        let _val = *ptr;
    }
}
