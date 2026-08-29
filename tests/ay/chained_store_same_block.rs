// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-expect: PROOF
// Fixed #4228: raw-ptr load/store path asymmetry resolved in [U]130.
// PROOF at 9s with AY pin 65537dc8. Was UNKNOWN due to stale annotation.
// kani-flags: --ay-chc-track=mem
//
//! Test multiple stores to same type array within a single basic block (#1447).
//!
//! This test verifies that when two stores to the same type-indexed memory array
//! occur in the same basic block, both stores are visible in the final state.
//! If the SSA encoding bug exists (see research report), the test will fail due
//! to over-constrained SMT formulas.

/// Minimal test: two consecutive stores to same type pointers
/// Both stores MUST be in same basic block (no intervening assertions/branches)
#[kani::proof]
fn test_two_stores_same_block() {
    let mut x: i32 = 0;
    let mut y: i32 = 0;
    let px: *mut i32 = &mut x;
    let py: *mut i32 = &mut y;

    // Two stores to i32* type in same basic block
    unsafe {
        *px = 10; // Store 1 to arr_i32
        *py = 20; // Store 2 to arr_i32 (same type, same block)
    }

    // Single assertion at end - NOT between stores
    // If bug exists: arr_i32__out is over-constrained, causing false UNSAT/failure
    let result = unsafe { *px == 10 && *py == 20 };
    kani::assert(result, "both stores visible");
}
