// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A slice element address is `data + idx * size_of::<T>()` with every bit of the byte offset. A
//! slice built with a claimed length past its allocation passes the index check for any smaller
//! index, so an index at `2^32` bytes reads out of bounds; a pointer representation that keeps only
//! a 32-bit offset lane folds it back onto element 0, which passes the allocation bound.
//!
//! Oracle: Rust semantics (reading `s[1 << 32]` of a 16-byte allocation is an out-of-bounds read,
//! UB), cross-checked with upstream Kani at the corpus rev (see the manifest row).
//!   MUST FAIL: bug_slice_index_past_lane_aliases_element_zero,
//!     bug_slice_symbolic_index_past_lane_aliases_element_one.
//!   MUST PASS: safe_slice_index_in_bounds_under_claimed_length.

#[kani::proof]
fn bug_slice_index_past_lane_aliases_element_zero() {
    let mut arr = [0u8; 16];
    arr[0] = 7;
    let s: &[u8] = unsafe { std::slice::from_raw_parts(arr.as_ptr(), 1usize << 33) };
    assert!(s[1usize << 32] == 7);
}

#[kani::proof]
fn bug_slice_symbolic_index_past_lane_aliases_element_one() {
    let mut arr = [0u8; 16];
    arr[1] = 5;
    let s: &[u8] = unsafe { std::slice::from_raw_parts(arr.as_ptr(), 1usize << 33) };
    let i: usize = kani::any();
    kani::assume(i == (1usize << 32) + 1);
    assert!(s[i] == 5);
}

#[kani::proof]
fn safe_slice_index_in_bounds_under_claimed_length() {
    let mut arr = [0u8; 16];
    arr[1] = 5;
    let s: &[u8] = unsafe { std::slice::from_raw_parts(arr.as_ptr(), 16) };
    let i: usize = kani::any();
    kani::assume(i == 1);
    assert!(s[i] == 5);
}
