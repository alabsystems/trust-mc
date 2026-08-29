// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-expect: PROOF
// NOTE: test_conditional_allocation was PROOF at ay 417854b7, regressed to UNKNOWN at ay 8a4a9bcc2 (false proof caught by defense).
// kani-flags: --ay-chc-track=mem
//
//! Memory safety verification tests (#1031).
//!
//! Kani proof harnesses for memory safety properties using AY's memory tracking mode.
//! Uses `--ay-chc-track=mem` for SMT array-based memory model.
//!
//! ## Retained Harnesses
//!
//! Only harnesses that exercise non-trivial verification properties are retained:
//! - `test_conditional_allocation`: symbolic branch with counter invariant
//! - `test_bounds_checking_works`: symbolic array index with bounds guard
//!
//! 7 tautological harnesses deleted (Part of #2558, Prover F3 from P1:1353):
//! they asserted concrete arithmetic (42==42, 1==1, etc.) and inflated PROOF metrics.

/// Test: Conditional allocation is tracked correctly (inline).
#[kani::proof]
fn test_conditional_allocation() {
    let cond: bool = kani::any();
    let mut allocated: u32 = 0;
    let mut freed: u32 = 0;

    if cond {
        allocated = allocated + 1;
        let _value: i32 = 100;
        freed = freed + 1;
    }

    // Either path: allocations should be balanced
    kani::assert(allocated == freed, "conditional allocation balanced");
}

/// Test: Verify memory model bounds checking works.
///
/// This indirectly tests that the memory safety infrastructure is functioning.
#[kani::proof]
fn test_bounds_checking_works() {
    let arr: [i32; 4] = [10, 20, 30, 40];
    let idx: usize = kani::any();
    kani::assume(idx < 4);

    let value = arr[idx];
    kani::assert(value >= 10 && value <= 40, "in-bounds access safe");
}
