// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (both directions) -- indexing a `Vec` after `Vec::extend`
//! from a range, on the CHC lane (walker fail-closed review, round 1 of the
//! repair after the merge with main's Rule D, 2026-10-14, finding 2).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, measured 2026-10-14):
//!   x1_range_index0_safe            -> VERIFICATION:- SUCCESSFUL
//!   x2_range_index2_safe            -> VERIFICATION:- SUCCESSFUL
//!   x3_inclusive_index2_safe        -> VERIFICATION:- SUCCESSFUL
//!   x4_u32_range_index1_safe        -> VERIFICATION:- SUCCESSFUL
//!   x5_range_index3_bug             -> VERIFICATION:- FAILED  ('index out of bounds')
//!   x6_inclusive_to_max_safe        -> VERIFICATION:- SUCCESSFUL
//!   x6_inclusive_to_max_len_bug     -> VERIFICATION:- FAILED  ('assertion failed: v.len() == 5')
//!   x7_extend_twice_safe            -> VERIFICATION:- SUCCESSFUL
//!   x7_extend_twice_value_bug       -> VERIFICATION:- FAILED  ('assertion failed: v[4] == 10')
//!   x8_symbolic_len_index_safe      -> VERIFICATION:- SUCCESSFUL
//!   x8_symbolic_len_index_bug       -> VERIFICATION:- FAILED  ('index out of bounds')
//!   x9_symbolic_value_safe          -> VERIFICATION:- SUCCESSFUL
//!   x10_after_push_index_safe       -> VERIFICATION:- SUCCESSFUL
//!   x10_after_push_value_bug        -> VERIFICATION:- FAILED  ('assertion failed: v[3] == 4')
//!   s1_slice_sym_value_safe         -> VERIFICATION:- SUCCESSFUL
//!   s2_slice_sym_len_index_safe     -> VERIFICATION:- SUCCESSFUL
//!   s3_iter_sym_index_safe          -> VERIFICATION:- SUCCESSFUL
//!   s4_const_slice_value_safe       -> VERIFICATION:- SUCCESSFUL
//!   s5_slice_sym_index_bug          -> VERIFICATION:- FAILED  ('index out of bounds')
//!   s6_slice_from_vec_index_safe    -> VERIFICATION:- SUCCESSFUL
//!   s7_slice_from_vec_index_bug     -> VERIFICATION:- FAILED  ('index out of bounds')
//!   p1_long_range_prefix_safe       -> VERIFICATION:- SUCCESSFUL
//!   p2_long_range_value_safe        -> VERIFICATION:- SUCCESSFUL
//!   p2_long_range_value_bug         -> VERIFICATION:- FAILED  ('assertion failed: v[19] == 18')
//!   p3_sym_slice_prefix_safe        -> VERIFICATION:- SUCCESSFUL
//!   p3_sym_slice_prefix_bug         -> VERIFICATION:- FAILED  ('assertion failed: v[0] == 6')
//!   p4_sym_range_prefix_safe        -> VERIFICATION:- SUCCESSFUL
//!   p5_long_range_prefix_sum_safe   -> VERIFICATION:- SUCCESSFUL
//!   p6_sym_slice_prefix_len_safe    -> VERIFICATION:- SUCCESSFUL
//!   p7_extend_then_vec_eq_safe      -> VERIFICATION:- SUCCESSFUL
//!
//! MECHANISM UNDER TEST. `vec_op_extend_range` set the side-state length, so
//! `v.len()` was right, but wrote the Vec's own `len` and `data` fields only for
//! a one-element range, and an index check reads the fields:
//! `v.extend(0u8..3); assert!(v[0] == 0)` failed `index out of bounds`
//! certified Genuine on main and on the branch, where Kani proves it. The
//! fields are now written for every count
//! (`codegen_call_vec_ops_extend_range.rs`, `write_range_extended_vec_fields`):
//! the elements exactly for a constant integer range of at most 16, a fresh
//! array (an identified sound havoc, never certified) otherwise. The `s` rows
//! are the same hole in `extend_from_slice` (and `extend` from a slice
//! iterator) when the source's length is known and its values are not: certified
//! Genuine on main, a false failure on the branch before this round; the
//! fields move by the count and `data` is a fresh array
//! (`codegen_call_vec_ops_len.rs`, `write_appended_vec_fields`), and a slice
//! of a whole array local has the array's length (`resolve_slice_arg_length`).
//!
//! The `p` rows (round 2, finding 4): round 1 made `data` a fresh array for
//! every append of unknown values, which also dropped the Vec's OLD
//! elements, so `vec![5, 6]; v.extend_from_slice(&a); v[0] == 5` for a
//! symbolic `a` failed closed where main and Kani prove it. An append of a
//! constant count now stores fresh values in the appended slots only and keeps
//! the rest, and a constant integer range stores its values exactly up to 64
//! elements (`appended_data`). A symbolic count still makes `data` a fresh
//! array (p4): the exact store form timed out on ay d80d17a90.
//!
//! Lane scope: CHC (the model is the CHC lane's; the BMC lane fails these
//! closed, OverApproximation, on both bundles).
//!
//! Run: trust-mc-driver -Z unstable-options --harness-timeout=30s --ay-chc range_extend_index_dual.rs

#[kani::proof]
fn x1_range_index0_safe() {
    let mut v: Vec<u8> = Vec::new();
    v.extend(0u8..3);
    assert!(v[0] == 0);
}

#[kani::proof]
fn x2_range_index2_safe() {
    let mut v: Vec<u8> = Vec::new();
    v.extend(0u8..3);
    assert!(v[2] == 2);
}

#[kani::proof]
fn x3_inclusive_index2_safe() {
    let mut v: Vec<u8> = Vec::new();
    v.extend(0u8..=2);
    assert!(v[2] == 2);
}

#[kani::proof]
fn x4_u32_range_index1_safe() {
    let mut v: Vec<u32> = Vec::new();
    v.extend(0u32..3);
    assert!(v[1] == 1);
}

#[kani::proof]
fn x5_range_index3_bug() {
    let mut v: Vec<u8> = Vec::new();
    v.extend(0u8..3);
    assert!(v[3] == 3);
}

#[kani::proof]
fn x6_inclusive_to_max_safe() {
    let mut v: Vec<u8> = Vec::new();
    v.extend(250u8..=255);
    assert!(v.len() == 6);
    assert!(v[5] == 255);
}

#[kani::proof]
fn x6_inclusive_to_max_len_bug() {
    let mut v: Vec<u8> = Vec::new();
    v.extend(250u8..=255);
    assert!(v.len() == 5);
}

#[kani::proof]
fn x7_extend_twice_safe() {
    let mut v: Vec<u16> = Vec::new();
    v.extend(0u16..3);
    v.extend(10u16..12);
    assert!(v.len() == 5);
    assert!(v[3] == 10);
}

#[kani::proof]
fn x7_extend_twice_value_bug() {
    let mut v: Vec<u16> = Vec::new();
    v.extend(0u16..3);
    v.extend(10u16..12);
    assert!(v[4] == 10);
}

#[kani::proof]
#[kani::unwind(6)]
fn x8_symbolic_len_index_safe() {
    let n: u8 = kani::any();
    kani::assume(n <= 4);
    let mut v: Vec<u8> = Vec::new();
    v.extend(0u8..n);
    if n > 2 {
        let _ = v[2];
    }
}

#[kani::proof]
#[kani::unwind(6)]
fn x8_symbolic_len_index_bug() {
    let n: u8 = kani::any();
    kani::assume(n <= 4);
    let mut v: Vec<u8> = Vec::new();
    v.extend(0u8..n);
    if n > 1 {
        let _ = v[2];
    }
}

#[kani::proof]
#[kani::unwind(6)]
fn x9_symbolic_value_safe() {
    let n: u8 = kani::any();
    kani::assume(n <= 4);
    let mut v: Vec<u8> = Vec::new();
    v.extend(0u8..n);
    if n > 2 {
        assert!(v[2] == 2);
    }
}

#[kani::proof]
fn x10_after_push_index_safe() {
    let mut v: Vec<u8> = Vec::new();
    v.push(7);
    v.extend(1u8..4);
    assert!(v[0] == 7);
    assert!(v[3] == 3);
}

#[kani::proof]
fn x10_after_push_value_bug() {
    let mut v: Vec<u8> = Vec::new();
    v.push(7);
    v.extend(1u8..4);
    assert!(v[3] == 4);
}

#[kani::proof]
fn s1_slice_sym_value_safe() {
    let a: [u8; 3] = kani::any();
    let mut v: Vec<u8> = Vec::new();
    v.extend_from_slice(&a);
    assert!(v[2] == a[2]);
}

#[kani::proof]
fn s2_slice_sym_len_index_safe() {
    let a: [u8; 3] = kani::any();
    let mut v: Vec<u8> = Vec::new();
    v.extend_from_slice(&a);
    assert!(v.len() == 3);
    let _ = v[2];
}

#[kani::proof]
fn s3_iter_sym_index_safe() {
    let a: [u8; 3] = kani::any();
    let mut v: Vec<u8> = Vec::new();
    v.extend(a.iter());
    let _ = v[2];
}

#[kani::proof]
fn s4_const_slice_value_safe() {
    let mut v: Vec<u8> = Vec::new();
    v.extend_from_slice(&[4u8, 5, 6]);
    assert!(v[2] == 6);
}

#[kani::proof]
fn s5_slice_sym_index_bug() {
    let a: [u8; 3] = kani::any();
    let mut v: Vec<u8> = Vec::new();
    v.extend_from_slice(&a);
    let _ = v[3];
}

#[kani::proof]
fn s6_slice_from_vec_index_safe() {
    let w: Vec<u8> = vec![kani::any(), kani::any(), kani::any()];
    let mut v: Vec<u8> = Vec::new();
    v.extend_from_slice(&w);
    assert!(v.len() == 3);
    let _ = v[2];
}

#[kani::proof]
fn s7_slice_from_vec_index_bug() {
    let w: Vec<u8> = vec![kani::any(), kani::any(), kani::any()];
    let mut v: Vec<u8> = Vec::new();
    v.extend_from_slice(&w);
    let _ = v[3];
}

#[kani::proof]
fn p1_long_range_prefix_safe() {
    let mut v: Vec<u8> = vec![5, 6];
    v.extend(0u8..20);
    assert!(v[0] == 5 && v[1] == 6);
}

#[kani::proof]
fn p2_long_range_value_safe() {
    let mut v: Vec<u8> = Vec::new();
    v.extend(0u8..20);
    assert!(v[19] == 19);
}

#[kani::proof]
fn p2_long_range_value_bug() {
    let mut v: Vec<u8> = Vec::new();
    v.extend(0u8..20);
    assert!(v[19] == 18);
}

#[kani::proof]
fn p3_sym_slice_prefix_safe() {
    let mut v: Vec<u8> = vec![5, 6];
    let a: [u8; 2] = kani::any();
    v.extend_from_slice(&a);
    assert!(v[0] == 5);
}

#[kani::proof]
fn p3_sym_slice_prefix_bug() {
    let mut v: Vec<u8> = vec![5, 6];
    let a: [u8; 2] = kani::any();
    v.extend_from_slice(&a);
    assert!(v[0] == 6);
}

#[kani::proof]
#[kani::unwind(6)]
fn p4_sym_range_prefix_safe() {
    let n: u8 = kani::any();
    kani::assume(n <= 3);
    let mut v: Vec<u8> = vec![5, 6];
    v.extend(0..n);
    assert!(v[1] == 6);
}

#[kani::proof]
fn p5_long_range_prefix_sum_safe() {
    let mut v: Vec<u8> = vec![1, 2, 3];
    v.extend(0u8..17);
    assert!(v[0] + v[1] + v[2] == 6);
}

#[kani::proof]
fn p6_sym_slice_prefix_len_safe() {
    let mut v: Vec<u8> = vec![5, 6];
    let a: [u8; 3] = kani::any();
    v.extend_from_slice(&a);
    assert!(v[0] == 5 && v[1] == 6 && v.len() == 5);
}

#[kani::proof]
fn p7_extend_then_vec_eq_safe() {
    let mut v: Vec<u8> = Vec::new();
    v.extend(0u8..3);
    assert!(v == vec![0u8, 1, 2]);
}
