// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Pointer difference across two stack allocations.
//!
//! Oracle: Rust semantics, cross-checked with upstream Kani 0.67.0 (see the manifest rows).
//!   MUST FAIL: bug_offset_from_cross_alloc ("same allocation" UB check),
//!              bug_usize_distance_cross_alloc (the distance of two allocations is unspecified).
//!   MUST PASS: safe_offset_from_within_array.

#[kani::proof]
fn bug_offset_from_cross_alloc() {
    let a: u16 = kani::any();
    let b: u16 = kani::any();
    let pa: *const u16 = &a;
    let pb: *const u16 = &b;
    let _d = unsafe { pb.offset_from(pa) };
}

#[kani::proof]
fn bug_usize_distance_cross_alloc() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let xa = &a as *const u8 as usize;
    let xb = &b as *const u8 as usize;
    assert!(xb.wrapping_sub(xa) == 1);
}

#[kani::proof]
fn safe_offset_from_within_array() {
    let arr: [u16; 5] = kani::any();
    let first: *const u16 = &arr[1];
    let last: *const u16 = &arr[4];
    let d = unsafe { last.offset_from(first) };
    assert!(d == 3);
}
