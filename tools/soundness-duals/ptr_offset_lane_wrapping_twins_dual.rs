// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Twins of ptr_offset_lane_truncation_dual.rs. A wrapping pointer step is address arithmetic mod
//! 2^64 in both directions: a small step keeps the exact distance, and a large backwards step
//! keeps every bit of it. A pointer representation that keeps only a 32-bit offset lane reads the
//! low 32 bits of a large distance.
//!
//! Oracle: Rust semantics (`wrapping_add` / `wrapping_sub` are `wrapping_offset`, address
//! arithmetic mod 2^64).
//!   MUST PASS: safe_small_wrapping_add_distance_exact (3 elements of u128 are 48 bytes),
//!     safe_large_wrapping_sub_distance_exact (the distance is 0x3FFF_FFFF_FFFF_FFF0).
//!   MUST FAIL: bug_large_wrapping_sub_truncated_distance (the distance is not its low 32 bits),
//!     bug_small_wrapping_add_distance_off_by_one_element.

#[kani::proof]
fn safe_small_wrapping_add_distance_exact() {
    let arr = [0u128; 10];
    let v_0: *const u128 = &arr[0];
    let v_3: *const u128 = v_0.wrapping_add(3);
    assert!(v_3.addr().wrapping_sub(v_0.addr()) == 48);
}

#[kani::proof]
fn bug_small_wrapping_add_distance_off_by_one_element() {
    let arr = [0u128; 10];
    let v_0: *const u128 = &arr[0];
    let v_3: *const u128 = v_0.wrapping_add(3);
    assert!(v_3.addr().wrapping_sub(v_0.addr()) == 32);
}

#[kani::proof]
fn bug_large_wrapping_sub_truncated_distance() {
    let arr = [0u128; 10];
    let v_0: *const u128 = &arr[0];
    let high = usize::MAX / (size_of::<u128>() * 4);
    let v_back: *const u128 = v_0.wrapping_sub(high);
    assert!(v_0.addr().wrapping_sub(v_back.addr()) == 0xFFFF_FFF0);
}

#[kani::proof]
fn safe_large_wrapping_sub_distance_exact() {
    let arr = [0u128; 10];
    let v_0: *const u128 = &arr[0];
    let high = usize::MAX / (size_of::<u128>() * 4);
    let v_back: *const u128 = v_0.wrapping_sub(high);
    assert!(v_0.addr().wrapping_sub(v_back.addr()) == high * 16);
}
