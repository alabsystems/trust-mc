// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Address order of stack allocations: unspecified ACROSS allocations, exact WITHIN one.
//!
//! Oracle: Rust semantics, cross-checked with upstream Kani 0.67.0 (see the manifest rows).
//!   MUST FAIL: bug_cross_alloc_lt_via_usize, bug_cross_alloc_gt, bug_cross_alloc_cmp_less
//!     (the relative order of two allocations is unspecified, so neither order is provable).
//!   MUST PASS: safe_within_array_order, safe_within_array_addr_distance,
//!     safe_cross_alloc_addresses_differ, safe_addr_nonnull_aligned.
//!
//! The CHC lane used to give every stack local the constant address `concat(obj_id, 0)`, so a
//! comparison across two locals compared allocation ids in declaration order and was proven.

#[kani::proof]
fn bug_cross_alloc_lt_via_usize() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let xa = &a as *const u8 as usize;
    let xb = &b as *const u8 as usize;
    assert!(xa < xb);
}

#[kani::proof]
fn bug_cross_alloc_gt() {
    let a: u16 = kani::any();
    let b: u16 = kani::any();
    let pa: *const u16 = &a;
    let pb: *const u16 = &b;
    assert!(pa > pb);
}

#[kani::proof]
fn bug_cross_alloc_cmp_less() {
    let a: u32 = kani::any();
    let b: u32 = kani::any();
    let pa: *const u32 = &a;
    let pb: *const u32 = &b;
    assert!(pa.cmp(&pb) == core::cmp::Ordering::Less);
}

#[kani::proof]
fn safe_within_array_order() {
    let arr: [u32; 4] = kani::any();
    let first: *const u32 = &arr[0];
    let last: *const u32 = &arr[3];
    assert!(first < last);
    assert!(last >= first);
    assert!(first.cmp(&last) == core::cmp::Ordering::Less);
    assert!(unsafe { first.add(3) } == last);
}

#[kani::proof]
fn safe_within_array_addr_distance() {
    let arr: [u32; 4] = kani::any();
    let first: *const u32 = &arr[0];
    let last: *const u32 = &arr[3];
    assert!(last as usize - first as usize == 12);
}

#[kani::proof]
fn safe_cross_alloc_addresses_differ() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let pa: *const u8 = &a;
    let pb: *const u8 = &b;
    assert!(pa != pb);
    assert!(pa as usize != pb as usize);
}

#[kani::proof]
fn safe_addr_nonnull_aligned() {
    let x: u32 = kani::any();
    let p: *const u32 = &x;
    assert!(p as usize != 0);
    assert!(p.is_aligned());
}
