// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (both directions) -- a range literal is the value of its
//! local only while nothing rewrites it (fix/chc-walker-fail-closed, walker
//! fail-closed repair round 5, review finding 1 (c) and its class).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, measured 2026-10-01 to
//! 2026-10-02):
//!   l1_extend_after_next_bug               -> VERIFICATION:- FAILED  ('assertion failed: v.len() == 5')
//!   l1_extend_after_next_safe              -> VERIFICATION:- SUCCESSFUL
//!   l2_extend_after_next_back_bug          -> VERIFICATION:- FAILED  ('assertion failed: v.len() == 5')
//!   l2_extend_after_next_back_safe         -> VERIFICATION:- SUCCESSFUL
//!   l3_extend_after_nth_bug                -> VERIFICATION:- FAILED  ('assertion failed: v.len() == 6')
//!   l3_extend_after_nth_safe               -> VERIFICATION:- SUCCESSFUL
//!   l4_extend_after_store_through_ref_bug  -> VERIFICATION:- FAILED  ('assertion failed: v.len() == 5')
//!   l4_extend_after_store_through_ref_safe -> VERIFICATION:- SUCCESSFUL
//!   l5_extend_after_field_write_bug        -> VERIFICATION:- FAILED  ('assertion failed: v.len() == 5')
//!   l5_extend_after_field_write_safe       -> VERIFICATION:- SUCCESSFUL
//!   l6_extend_advanced_in_fn_bug           -> VERIFICATION:- FAILED  ('assertion failed: v.len() == 5')
//!   l6_extend_advanced_in_fn_safe          -> VERIFICATION:- SUCCESSFUL
//!   l7_extend_exhausted_inclusive_bug      -> VERIFICATION:- FAILED  ('assertion failed: v.len() == 1')
//!   l7_extend_exhausted_inclusive_safe     -> VERIFICATION:- SUCCESSFUL
//!   l8_extend_inclusive_next_back_bug      -> VERIFICATION:- FAILED  ('assertion failed: v.len() == 5')
//!   l8_extend_inclusive_next_back_safe     -> VERIFICATION:- SUCCESSFUL
//!   l9_extend_literal_per_branch_bug       -> VERIFICATION:- FAILED  ('assertion failed: v.len() == 3')
//!   l9_extend_literal_per_branch_safe      -> VERIFICATION:- SUCCESSFUL
//!   l10_extend_bound_reassigned_bug        -> VERIFICATION:- FAILED  ('assertion failed: v.len() == 5')
//!   l10_extend_bound_reassigned_safe       -> VERIFICATION:- SUCCESSFUL
//!   t1_slice_by_advanced_range_len_bug     -> VERIFICATION:- FAILED  ('assertion failed: s.len() == 2')
//!   t1_slice_by_advanced_range_len_safe    -> VERIFICATION:- SUCCESSFUL
//!   t2_slice_by_advanced_range_value_bug   -> VERIFICATION:- FAILED  ('assertion failed: s[0] == 1')
//!   t2_slice_by_advanced_range_value_safe  -> VERIFICATION:- SUCCESSFUL
//!   t3_slice_inclusive_empty_bug           -> VERIFICATION:- FAILED  ('assertion failed: !s.is_empty()')
//!   t3_slice_inclusive_empty_safe          -> VERIFICATION:- SUCCESSFUL
//!   t4_slice_exhausted_inclusive_bug       -> VERIFICATION:- FAILED  ('assertion failed: s.len() == 1')
//!   t4_slice_exhausted_inclusive_safe      -> VERIFICATION:- SUCCESSFUL
//!   t5_slice_inclusive_reversed_bug        -> VERIFICATION:- FAILED  ('a panic whose message Kani does not format')
//!
//! MECHANISM UNDER TEST. The CHC range models read a range's bounds, and a
//! `RangeInclusive`'s freshness, from a syntactic scan of the MIR literal
//! that built the local (`extract_range_const_field_from_mir`). A range
//! advanced by `next` / `next_back` / `nth`, written through `&mut` or by a
//! field store, advanced in a helper, or assigned on two paths, still read as
//! its literal, so `v.extend(r)` extended by the literal's length and
//! `&a[r]` sliced by it. The literal now answers only when every local of the
//! copy chain (and each local a field constant is read through) has one
//! definition, no partial write and no mutable or raw borrow; otherwise the
//! range's state is read. An inclusive slice index also follows
//! `into_slice_range`: `start..=end` is `start'..end + 1` with `start'` the
//! end once the range is exhausted, and is reversed only when
//! `start' > end + 1`.

use std::ops::Range;

#[kani::proof]
fn l1_extend_after_next_bug() {
    let mut r = 0u32..5;
    r.next();
    let mut v: Vec<u32> = Vec::new();
    v.extend(r);
    assert!(v.len() == 5);
}

#[kani::proof]
fn l1_extend_after_next_safe() {
    let mut r = 0u32..5;
    r.next();
    let mut v: Vec<u32> = Vec::new();
    v.extend(r);
    assert!(v.len() == 4);
}

#[kani::proof]
fn l2_extend_after_next_back_bug() {
    let mut r = 0u32..5;
    r.next_back();
    let mut v: Vec<u32> = Vec::new();
    v.extend(r);
    assert!(v.len() == 5);
}

#[kani::proof]
fn l2_extend_after_next_back_safe() {
    let mut r = 0u32..5;
    r.next_back();
    let mut v: Vec<u32> = Vec::new();
    v.extend(r);
    assert!(v.len() == 4);
}

#[kani::proof]
fn l3_extend_after_nth_bug() {
    let mut r = 0u32..6;
    r.nth(2);
    let mut v: Vec<u32> = Vec::new();
    v.extend(r);
    assert!(v.len() == 6);
}

#[kani::proof]
fn l3_extend_after_nth_safe() {
    let mut r = 0u32..6;
    r.nth(2);
    let mut v: Vec<u32> = Vec::new();
    v.extend(r);
    assert!(v.len() == 3);
}

#[kani::proof]
fn l4_extend_after_store_through_ref_bug() {
    let mut r = 0u32..5;
    {
        let rr = &mut r;
        rr.start = 4;
    }
    let mut v: Vec<u32> = Vec::new();
    v.extend(r);
    assert!(v.len() == 5);
}

#[kani::proof]
fn l4_extend_after_store_through_ref_safe() {
    let mut r = 0u32..5;
    {
        let rr = &mut r;
        rr.start = 4;
    }
    let mut v: Vec<u32> = Vec::new();
    v.extend(r);
    assert!(v.len() == 1);
}

#[kani::proof]
fn l5_extend_after_field_write_bug() {
    let mut r = 0u32..5;
    r.end = 2;
    let mut v: Vec<u32> = Vec::new();
    v.extend(r);
    assert!(v.len() == 5);
}

#[kani::proof]
fn l5_extend_after_field_write_safe() {
    let mut r = 0u32..5;
    r.end = 2;
    let mut v: Vec<u32> = Vec::new();
    v.extend(r);
    assert!(v.len() == 2);
}

#[inline(never)]
fn advance(r: &mut Range<u32>) {
    r.next();
}

#[kani::proof]
fn l6_extend_advanced_in_fn_bug() {
    let mut r = 0u32..5;
    advance(&mut r);
    let mut v: Vec<u32> = Vec::new();
    v.extend(r);
    assert!(v.len() == 5);
}

#[kani::proof]
fn l6_extend_advanced_in_fn_safe() {
    let mut r = 0u32..5;
    advance(&mut r);
    let mut v: Vec<u32> = Vec::new();
    v.extend(r);
    assert!(v.len() == 4);
}

#[kani::proof]
fn l7_extend_exhausted_inclusive_bug() {
    let mut r = 0u32..=0;
    r.next();
    let mut v: Vec<u32> = Vec::new();
    v.extend(r);
    assert!(v.len() == 1);
}

#[kani::proof]
fn l7_extend_exhausted_inclusive_safe() {
    let mut r = 0u32..=0;
    r.next();
    let mut v: Vec<u32> = Vec::new();
    v.extend(r);
    assert!(v.len() == 0);
}

#[kani::proof]
fn l8_extend_inclusive_next_back_bug() {
    let mut r = 0u32..=4;
    r.next_back();
    let mut v: Vec<u32> = Vec::new();
    v.extend(r);
    assert!(v.len() == 5);
}

#[kani::proof]
fn l8_extend_inclusive_next_back_safe() {
    let mut r = 0u32..=4;
    r.next_back();
    let mut v: Vec<u32> = Vec::new();
    v.extend(r);
    assert!(v.len() == 4);
}

#[kani::proof]
#[kani::unwind(7)]
fn l9_extend_literal_per_branch_bug() {
    let c: bool = kani::any();
    let r = if c { 0u32..3 } else { 1u32..5 };
    let mut v: Vec<u32> = Vec::new();
    v.extend(r);
    assert!(v.len() == 3);
}

#[kani::proof]
#[kani::unwind(7)]
fn l9_extend_literal_per_branch_safe() {
    let c: bool = kani::any();
    let r = if c { 0u32..3 } else { 1u32..5 };
    let mut v: Vec<u32> = Vec::new();
    v.extend(r);
    assert!(v.len() == if c { 3 } else { 4 });
}

#[kani::proof]
#[kani::unwind(7)]
fn l10_extend_bound_reassigned_bug() {
    let c: bool = kani::any();
    let mut s = 0u32;
    if c {
        s = 2;
    }
    let mut v: Vec<u32> = Vec::new();
    v.extend(s..5);
    assert!(v.len() == 5);
}

#[kani::proof]
#[kani::unwind(7)]
fn l10_extend_bound_reassigned_safe() {
    let c: bool = kani::any();
    let mut s = 0u32;
    if c {
        s = 2;
    }
    let mut v: Vec<u32> = Vec::new();
    v.extend(s..5);
    assert!(v.len() == if c { 3 } else { 5 });
}

#[kani::proof]
fn t1_slice_by_advanced_range_len_bug() {
    let a = [1u8, 2, 3, 4];
    let mut r = 0usize..2;
    r.next();
    let s = &a[r];
    assert!(s.len() == 2);
}

#[kani::proof]
fn t1_slice_by_advanced_range_len_safe() {
    let a = [1u8, 2, 3, 4];
    let mut r = 0usize..2;
    r.next();
    let s = &a[r];
    assert!(s.len() == 1);
}

#[kani::proof]
fn t2_slice_by_advanced_range_value_bug() {
    let a = [1u8, 2, 3, 4];
    let mut r = 0usize..2;
    r.next();
    let s = &a[r];
    assert!(s[0] == 1);
}

#[kani::proof]
fn t2_slice_by_advanced_range_value_safe() {
    let a = [1u8, 2, 3, 4];
    let mut r = 0usize..2;
    r.next();
    let s = &a[r];
    assert!(s[0] == 2);
}

#[kani::proof]
fn t3_slice_inclusive_empty_bug() {
    let a = [1u8, 2, 3, 4];
    let s = &a[2..=1];
    assert!(!s.is_empty());
}

#[kani::proof]
fn t3_slice_inclusive_empty_safe() {
    let a = [1u8, 2, 3, 4];
    let s = &a[2..=1];
    assert!(s.is_empty());
}

#[kani::proof]
fn t4_slice_exhausted_inclusive_bug() {
    let a = [1u8, 2, 3, 4];
    let mut r = 1usize..=1;
    r.next();
    let s = &a[r];
    assert!(s.len() == 1);
}

#[kani::proof]
fn t4_slice_exhausted_inclusive_safe() {
    let a = [1u8, 2, 3, 4];
    let mut r = 1usize..=1;
    r.next();
    let s = &a[r];
    assert!(s.is_empty());
}

#[kani::proof]
fn t5_slice_inclusive_reversed_bug() {
    let a = [1u8, 2, 3, 4];
    let lo: usize = kani::any();
    kani::assume(lo <= 3);
    let s = &a[lo..=1];
    assert!(s.len() <= 2);
}
