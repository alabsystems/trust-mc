// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Relational comparison of raw pointers into two DISTINCT allocations.
//!
//! Oracle: MUST FAIL. The relative order of two allocations' addresses is unspecified, so no
//! order can be proven. Upstream Kani 0.67.0 (measured 2026-09-15) reports FAILED on both
//! (`assertion failed: pa < pb`). Real rustc lays locals out differently at different opt
//! levels: two `()` locals are adjacent and ordered at -C opt-level=0 and share one address at
//! opt-level=2.
//!
//! The CHC lane gives a stack local the constant address `concat(obj_id, 0)`
//! (`get_or_create_local_address`), so a cross-allocation `<` compares allocation ids in
//! declaration order and is PROVEN.

#[kani::proof]
fn bug_distinct_u8_locals_lt() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let pa: *const u8 = &a;
    let pb: *const u8 = &b;
    assert!(pa < pb);
}

#[kani::proof]
fn bug_distinct_unit_locals_lt() {
    let a = ();
    let b = ();
    let pa: *const () = &a;
    let pb: *const () = &b;
    assert!(pa < pb);
}
