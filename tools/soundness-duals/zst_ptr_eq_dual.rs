// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Equality of pointers to a zero-sized type: exact within one allocation, unspecified across
//! two (rustc may place two zero-sized locals at one address).
//!
//! Oracle: Rust semantics, cross-checked with upstream Kani (see the manifest rows).
//!   MUST PASS: safe_subslice_data_ptrs_equal, safe_box_subslice_data_ptrs_equal (the shape of
//!     kani/PointerComparison/ptr_comparison.rs check_box_comparison), safe_zst_ptr_copies_equal.
//!   MUST FAIL: bug_distinct_unit_locals_ne.

#[kani::proof]
fn safe_subslice_data_ptrs_equal() {
    let obj = [0u16, 10];
    let first: *const [u16] = &obj[1..2];
    let second: *const [u16] = &obj[1..2];
    assert!(second as *const () == first as *const ());
}

#[kani::proof]
fn safe_box_subslice_data_ptrs_equal() {
    let obj = Box::new([0u16, 10]);
    let first: *const [u16] = &obj[1..2];
    let second: *const [u16] = &obj[1..2];
    assert!(second as *const () == first as *const ());
}

#[kani::proof]
fn safe_zst_ptr_copies_equal() {
    let u = ();
    let p: *const () = &u;
    let q = p;
    assert!(p == q);
}

#[kani::proof]
fn bug_distinct_unit_locals_ne() {
    let a = ();
    let b = ();
    let pa: *const () = &a;
    let pb: *const () = &b;
    assert!(pa != pb);
}
