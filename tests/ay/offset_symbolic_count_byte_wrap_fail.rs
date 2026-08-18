// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-verify-fail
// kani-expect: CTREX
// soundness-accepted-verdict: UNKNOWN
//
//! Soundness regression for the `count_checks_fold_clean` gate in
//! `codegen_ay/chc/stmt/codegen_stmt_rvalue_offset.rs`.
//!
//! That gate refuses to resolve pointer provenance (and so keeps the
//! `offset_provenance_unresolved` demotion) unless the count-only checks fold
//! clean on a CONCRETE count. Its stated worry is that with a SYMBOLIC count the
//! byte-product overflow obligation could be lost, so resolving provenance would
//! drop the fail-closed net and let a false Safe through.
//!
//! This harness is that worry made concrete, and it pins the obligation that has
//! to hold for any future relaxation of the gate to be sound: a SYMBOLIC count,
//! large enough that `count * size_of::<u32>()` wraps the 64-bit byte offset,
//! stepping a pointer far outside a 4-element array and dereferencing it. The
//! count itself stays below `isize::MAX`, so the isize-RANGE check alone cannot
//! catch it — only the byte-product (mul-overflow) obligation can.
//!
//! REQUIRED: never a PROOF. Expected `Offset in bytes overflows isize`.
//! If this ever verifies, the mul-overflow obligation has gone vacuous for
//! symbolic counts and any provenance relaxation resting on it is unsound.

#[kani::proof]
fn offset_symbolic_count_byte_wrap_must_fail() {
    let arr: [u32; 4] = kani::any();
    let ptr = arr.as_ptr();

    let count: usize = kani::any();
    // 2^62 <= count < isize::MAX: `count` passes the isize-range check while
    // `count * 4` wraps past 2^64. Only the mul-overflow obligation rules it out.
    kani::assume(count >= (1usize << 62));
    kani::assume(count < (isize::MAX as usize));

    let stepped = unsafe { ptr.add(count) };
    let observed = unsafe { *stepped };
    kani::assume(observed != 0);
}
