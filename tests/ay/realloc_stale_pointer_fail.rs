// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// kani-verify-fail
// kani-expect: CTREX
// soundness-accepted-verdict: UNKNOWN
// kani-flags: --ay-chc-track=mem
// NOTE: Was UNKNOWN, then ERROR at ay 65537dc81 (#4225); under the CHC lane at
// ay build.1636 the verdict is FAILED with [AY:CTREX_CAT:Unknown] (ay-chc
// inconclusive) — fail-closed. The ledger invariant is NO PROOF, ever.
//
//! DISCRIMINATING: #2425 — realloc stale-pointer use-after-free detection.
//! Any PASS/PROOF result here means the heap model stopped invalidating old pointers.
//!
//! Realloc stale-pointer regression harness for trust_mc (#2425).
//!
//! This harness intentionally dereferences the OLD pointer after
//! `std::alloc::realloc`. The nondeterministic realloc model explores
//! both in-place growth and move-to-new-allocation paths. On the
//! "moved" path, `obj_valid[old_id]` is set to false, so any
//! subsequent dereference of the old pointer should be detected as
//! a use-after-free (stale pointer).
//!
//! Expected result: CTREX (counterexample found on the moved branch).

use std::alloc::{Layout, alloc, realloc};

/// This test should FAIL — use of stale pointer after realloc.
///
/// Pattern:
/// 1. Allocate 16 bytes
/// 2. Write a value through the pointer
/// 3. Realloc to 32 bytes (may move the allocation)
/// 4. Read through the OLD pointer — invalid on the moved branch
///
/// NOTE: Uses `core::ptr::read_volatile` to force the stale read to happen
/// at its source location in the MIR. Without volatile, the MIR optimizer
/// may reorder the read before the realloc, avoiding the use-after-free
/// check entirely (#3636).
#[kani::proof]
fn test_realloc_stale_pointer_should_fail() {
    unsafe {
        let layout = Layout::from_size_align(16, 8).unwrap();
        let old_ptr = alloc(layout);

        if !old_ptr.is_null() {
            // Write to the original allocation.
            *old_ptr = 0xAB;

            // Realloc may move the data to a new location.
            let _new_ptr = realloc(old_ptr, layout, 32);

            // BUG: using old_ptr after realloc — if realloc moved the data,
            // old_ptr is now a dangling/stale pointer.
            // read_volatile prevents MIR from reordering this read before realloc.
            let _stale_read = core::ptr::read_volatile(old_ptr);
        }
    }
}
