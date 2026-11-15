// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (both directions) -- Kani's unwinding assertion on CBMC's
//! `memcmp` loop behind `raw_eq` and `compare_bytes` (array and slice `==`,
//! `&str` comparison and ordering), under a declared unwind
//! (fix/chc-walker-fail-closed, walker fail-closed repair round 5, review
//! finding 4).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, measured 2026-10-01 to
//! 2026-10-02):
//!   m1_u32_array_eq_u3_bug     -> VERIFICATION:- FAILED  ('unwinding assertion loop 0')
//!   m1_u32_array_eq_u9_safe    -> VERIFICATION:- SUCCESSFUL
//!   m2_u16_slice_eq_u3_bug     -> VERIFICATION:- FAILED  ('unwinding assertion loop 0')
//!   m2_u16_slice_eq_u5_safe    -> VERIFICATION:- SUCCESSFUL
//!   m3_u8_array_eq4_u3_bug     -> VERIFICATION:- FAILED  ('unwinding assertion loop 0')
//!   m4_u64_vec_eq_u3_bug       -> VERIFICATION:- FAILED  ('unwinding assertion loop 0')
//!   m5_u16_array_ne_u3_bug     -> VERIFICATION:- FAILED  ('unwinding assertion loop 0')
//!   y1_dedup_str_u3_bug        -> VERIFICATION:- FAILED  ('unwinding assertion loop 0')
//!   y1_dedup_str_u8_safe       -> VERIFICATION:- SUCCESSFUL
//!   y2_sort_str_u3_bug         -> VERIFICATION:- FAILED  ('unwinding assertion loop 0')
//!   y3_sort_u64_pairs_u3_safe  -> VERIFICATION:- SUCCESSFUL
//!   y4_sort_byte_arrays_u3_bug -> VERIFICATION:- FAILED  ('unwinding assertion loop 0')
//!
//! MECHANISM UNDER TEST. Kani implements `raw_eq` and `compare_bytes` with
//! CBMC's builtin `memcmp`, a loop it unwinds once per BYTE. The loop walk
//! read both body-less intrinsics as loop-free, so a modelled comparison
//! stated no unwinding assertion, and the trip-bound table counted elements
//! (`[x, 7u32] == [x, 7]` is eight bytes, bounded by 2). The walk treats both
//! as loops (`obligation_free_walk::runs_kani_memcmp_loop`), the table counts
//! bytes (`size_of::<T>()` per element, and `raw_eq` / `compare_bytes` rows),
//! a closure passed as a zero-sized constant (`dedup`'s `|a, b| a == b`) is
//! walked, and a sort of `[P; M]` elements is bounded by `max(len - 1, M)`.

#[kani::proof]
#[kani::unwind(3)]
fn m1_u32_array_eq_u3_bug() {
    let x: u32 = kani::any();
    let a: [u32; 2] = [x, 7];
    let b: [u32; 2] = [x, 7];
    assert!(a == b);
}

#[kani::proof]
#[kani::unwind(9)]
fn m1_u32_array_eq_u9_safe() {
    let x: u32 = kani::any();
    let a: [u32; 2] = [x, 7];
    let b: [u32; 2] = [x, 7];
    assert!(a == b);
}

#[kani::proof]
#[kani::unwind(3)]
fn m2_u16_slice_eq_u3_bug() {
    let x: u16 = kani::any();
    let a: [u16; 2] = [x, 7];
    let b: [u16; 2] = [x, 7];
    let sa: &[u16] = &a;
    let sb: &[u16] = &b;
    assert!(sa == sb);
}

#[kani::proof]
#[kani::unwind(5)]
fn m2_u16_slice_eq_u5_safe() {
    let x: u16 = kani::any();
    let a: [u16; 2] = [x, 7];
    let b: [u16; 2] = [x, 7];
    let sa: &[u16] = &a;
    let sb: &[u16] = &b;
    assert!(sa == sb);
}

#[kani::proof]
#[kani::unwind(3)]
fn m3_u8_array_eq4_u3_bug() {
    let x: u8 = kani::any();
    let a: [u8; 4] = [x, 1, 2, 3];
    let b: [u8; 4] = [x, 1, 2, 3];
    assert!(a == b);
}

#[kani::proof]
#[kani::unwind(3)]
fn m4_u64_vec_eq_u3_bug() {
    let x: u64 = kani::any();
    let a: Vec<u64> = vec![x];
    let b: Vec<u64> = vec![x];
    assert!(a == b);
}

#[kani::proof]
#[kani::unwind(3)]
fn m5_u16_array_ne_u3_bug() {
    let x: u16 = kani::any();
    let a: [u16; 2] = [x, 7];
    let b: [u16; 2] = [x, 7];
    assert!(!(a != b));
}

#[kani::proof]
#[kani::unwind(3)]
fn y1_dedup_str_u3_bug() {
    let mut v: Vec<&str> = vec!["abcdef", "abcdef"];
    v.dedup();
}

#[kani::proof]
#[kani::unwind(8)]
fn y1_dedup_str_u8_safe() {
    let mut v: Vec<&str> = vec!["abcdef", "abcdef"];
    v.dedup();
    assert!(v.len() == 1);
}

#[kani::proof]
#[kani::unwind(3)]
fn y2_sort_str_u3_bug() {
    let mut v: Vec<&str> = vec!["abcdef", "abcdef"];
    v.sort();
}

#[kani::proof]
#[kani::unwind(3)]
fn y3_sort_u64_pairs_u3_safe() {
    let x: u64 = kani::any();
    let mut v: Vec<[u64; 2]> = vec![[x, 1], [x, 1]];
    v.sort();
    assert!(v.len() == 2);
}

#[kani::proof]
#[kani::unwind(3)]
fn y4_sort_byte_arrays_u3_bug() {
    let x: u8 = kani::any();
    let mut v: Vec<[u8; 6]> = vec![[x, 1, 2, 3, 4, 5], [x, 1, 2, 3, 4, 5]];
    v.sort();
    assert!(v.len() == 2);
}
