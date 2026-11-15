// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The address of a pointer moved far outside its allocation by wrapping arithmetic keeps every
//! bit of the byte distance: `v_0.wrapping_add(n).addr() - v_0.addr() == n * size_of::<T>()`
//! (mod 2^64). A pointer representation that keeps only a 32-bit offset reads the low 32 bits.
//!
//! Oracle: Rust semantics (`wrapping_add` is `wrapping_offset`, address arithmetic mod 2^64; the
//! shape of tests/expected/offset-wraps-around/main.rs `harness_without_ub`), cross-checked with
//! upstream Kani (see the manifest rows).
//!   MUST FAIL: bug_truncated_distance_const, bug_truncated_distance_stack (the distance is
//!     0x3FFF_FFFF_FFFF_FFF0, not its low 32 bits).
//!   MUST PASS: safe_true_distance_stack.

#[kani::proof]
fn bug_truncated_distance_const() {
    let v: &[u128] = &[0; 10];
    let v_0: *const u128 = &v[0];
    let high = usize::MAX / (size_of::<u128>() * 4);
    let v_wrap: *const u128 = v_0.wrapping_add(high);
    assert!(v_wrap.addr().wrapping_sub(v_0.addr()) == 0xFFFF_FFF0);
}

#[kani::proof]
fn bug_truncated_distance_stack() {
    let arr = [0u128; 10];
    let v_0: *const u128 = &arr[0];
    let high = usize::MAX / (size_of::<u128>() * 4);
    let v_wrap: *const u128 = v_0.wrapping_add(high);
    assert!(v_wrap.addr().wrapping_sub(v_0.addr()) == 0xFFFF_FFF0);
}

#[kani::proof]
fn safe_true_distance_stack() {
    let arr = [0u128; 10];
    let v_0: *const u128 = &arr[0];
    let high = usize::MAX / (size_of::<u128>() * 4);
    let v_wrap: *const u128 = v_0.wrapping_add(high);
    assert!(v_wrap.addr().wrapping_sub(v_0.addr()) == high * 16);
}
