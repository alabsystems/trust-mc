// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (both directions) -- a collection's length, capacity or
//! membership after `mem::swap` and after a whole collection is stored into a
//! field (fix/chc-walker-fail-closed, repair round 4: the class of walker
//! fail-closed review 6 round 3 finding 7, a whole `Vec` stored through
//! `&mut Vec`).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, measured 2026-10-01):
//!   d3_mem_swap_len_bug                   -> VERIFICATION:- FAILED  ('v.len() == 0')
//!   d3_mem_swap_len_safe                  -> VERIFICATION:- SUCCESSFUL
//!   f7_swap_strings_len_bug               -> VERIFICATION:- FAILED  ('a.len() == 0')
//!   f7_swap_strings_len_safe              -> VERIFICATION:- SUCCESSFUL
//!   f8_swap_vec_cap_bug                   -> VERIFICATION:- FAILED  ('w.capacity() == 0')
//!   f9_swap_through_fn_bug                -> VERIFICATION:- FAILED  ('v.len() == 0')
//!   f10_swap_btreeset_len_bug             -> VERIFICATION:- FAILED  ('a.len() == 0')
//!   s3_vec_field_direct_store_bug         -> VERIFICATION:- FAILED  ('s.v.len() == 0')
//!   s3_vec_field_direct_store_safe        -> VERIFICATION:- SUCCESSFUL
//!   f1_field_store_len_bug                -> VERIFICATION:- FAILED  ('s.v.len() == 0')
//!   f1_field_store_len_safe               -> VERIFICATION:- SUCCESSFUL
//!   f2_tuple_store_len_bug                -> VERIFICATION:- FAILED  ('t.1.len() == 0')
//!   f2_tuple_store_len_safe               -> VERIFICATION:- SUCCESSFUL
//!   d5_ref_field_vec_store_bug            -> VERIFICATION:- FAILED  ('s.v.len() == 0')
//!   d5_ref_field_vec_store_safe           -> VERIFICATION:- SUCCESSFUL
//!   f4_ref_field_push_then_store_bug      -> VERIFICATION:- FAILED  ('s.v.len() == 2')
//!   f4_ref_field_push_then_store_safe     -> VERIFICATION:- SUCCESSFUL
//!   s4_push_then_ref_field_store_bug      -> VERIFICATION:- FAILED  ('s.v.len() == 1')
//!   f6_ref_string_field_store_bug         -> VERIFICATION:- FAILED  ('t.s.len() == 0')
//!
//! MECHANISM UNDER TEST. CHC: a collection's length, capacity and key
//! presence are side state keyed by its local. `mem::swap` exchanged the
//! locals' datatypes only (d3, f7-f10 bug rows clean on main, safe twins
//! certified Genuine); it now exchanges the side state too
//! (`misc_intrinsics_volatile.rs`, `swap_collection_side_state`). `Vec::len`
//! through a by-value field took the length of any tracked borrow of that
//! field, a drop-glue reborrow of the OLD value included (s3, f1, f2 safe
//! twins certified Genuine on main); only a field holding a reference is
//! chased now (`codegen_call_vec_ops_len.rs`). A store through a reference of
//! a value holding a collection (d5, f4, s4, f6) writes the target's memory
//! image and fails closed (`codegen_stmt_assign_simple_collection.rs`). BMC:
//! a field place is read under its derived name first, and a write of the
//! struct never reached that name, so the drop-glue borrow's stale value was
//! read (d5, f1, f2, f6, s3 bug rows clean on main); every derived field entry
//! is re-selected from its root's new value now (`statement/env/mod.rs`,
//! `refresh_derived_field_entries`).

struct S {
    v: Vec<u8>,
    n: u8,
}

#[kani::proof]
fn d3_mem_swap_len_bug() {
    let mut v: Vec<u8> = Vec::new();
    let mut w = vec![1u8, 2];
    std::mem::swap(&mut v, &mut w);
    assert!(v.len() == 0);
}

#[kani::proof]
fn d3_mem_swap_len_safe() {
    let mut v: Vec<u8> = Vec::new();
    let mut w = vec![1u8, 2];
    std::mem::swap(&mut v, &mut w);
    assert!(v.len() == 2 && w.len() == 0);
}

#[kani::proof]
fn f7_swap_strings_len_bug() {
    let mut a = String::new();
    let mut b = String::from("xy");
    std::mem::swap(&mut a, &mut b);
    assert!(a.len() == 0);
}

#[kani::proof]
fn f7_swap_strings_len_safe() {
    let mut a = String::new();
    let mut b = String::from("xy");
    std::mem::swap(&mut a, &mut b);
    assert!(a.len() == 2 && b.len() == 0);
}

#[kani::proof]
fn f8_swap_vec_cap_bug() {
    let mut v: Vec<u8> = Vec::with_capacity(8);
    let mut w: Vec<u8> = Vec::new();
    std::mem::swap(&mut v, &mut w);
    assert!(w.capacity() == 0);
}

#[kani::proof]
fn f9_swap_through_fn_bug() {
    fn sw(x: &mut Vec<u8>, y: &mut Vec<u8>) {
        std::mem::swap(x, y);
    }
    let mut v: Vec<u8> = Vec::new();
    let mut w = vec![1u8, 2];
    sw(&mut v, &mut w);
    assert!(v.len() == 0);
}

#[kani::proof]
fn f10_swap_btreeset_len_bug() {
    let mut a: std::collections::BTreeSet<u8> = std::collections::BTreeSet::new();
    let mut b: std::collections::BTreeSet<u8> = std::collections::BTreeSet::new();
    b.insert(1);
    std::mem::swap(&mut a, &mut b);
    assert!(a.len() == 0);
}

#[kani::proof]
fn s3_vec_field_direct_store_bug() {
    let mut s = S { v: Vec::new(), n: 0 };
    s.v = vec![1, 2];
    assert!(s.v.len() == 0);
}

#[kani::proof]
fn s3_vec_field_direct_store_safe() {
    let mut s = S { v: Vec::new(), n: 0 };
    s.v = vec![1, 2];
    assert!(s.v.len() == 2);
}

#[kani::proof]
fn f1_field_store_len_bug() {
    let mut s = S { v: Vec::new(), n: 0 };
    s.v = vec![1, 2, 3];
    assert!(s.v.len() == 0);
}

#[kani::proof]
fn f1_field_store_len_safe() {
    let mut s = S { v: Vec::new(), n: 0 };
    s.v = vec![1, 2, 3];
    assert!(s.v.len() == 3 && s.n == 0);
}

#[kani::proof]
fn f2_tuple_store_len_bug() {
    let mut t: (u8, Vec<u8>) = (0, Vec::new());
    t.1 = vec![1, 2];
    assert!(t.1.len() == 0);
}

#[kani::proof]
fn f2_tuple_store_len_safe() {
    let mut t: (u8, Vec<u8>) = (0, Vec::new());
    t.1 = vec![1, 2];
    assert!(t.1.len() == 2);
}

#[kani::proof]
fn d5_ref_field_vec_store_bug() {
    let mut s = S { v: Vec::new(), n: 0 };
    {
        let r = &mut s;
        r.v = vec![1, 2, 3];
    }
    assert!(s.v.len() == 0);
}

#[kani::proof]
fn d5_ref_field_vec_store_safe() {
    let mut s = S { v: Vec::new(), n: 0 };
    {
        let r = &mut s;
        r.v = vec![1, 2, 3];
    }
    assert!(s.v.len() == 3);
}

#[kani::proof]
fn f4_ref_field_push_then_store_bug() {
    let mut s = S { v: vec![7], n: 0 };
    {
        let r = &mut s;
        r.v.push(8);
        r.v = Vec::new();
    }
    assert!(s.v.len() == 2);
}

#[kani::proof]
fn f4_ref_field_push_then_store_safe() {
    let mut s = S { v: vec![7], n: 0 };
    {
        let r = &mut s;
        r.v.push(8);
        r.v = Vec::new();
    }
    assert!(s.v.len() == 0);
}

#[kani::proof]
fn s4_push_then_ref_field_store_bug() {
    let mut s = S { v: Vec::new(), n: 0 };
    s.v.push(3);
    {
        let r = &mut s;
        r.v = vec![1, 2, 3];
    }
    assert!(s.v.len() == 1);
}

#[kani::proof]
fn f6_ref_string_field_store_bug() {
    struct T {
        s: String,
    }
    let mut t = T { s: String::new() };
    let r = &mut t;
    r.s = String::from("abc");
    assert!(t.s.len() == 0);
}
