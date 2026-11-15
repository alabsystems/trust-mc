// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (both directions) -- a whole collection stored through a
//! reference (fix/chc-walker-fail-closed, repair round 3, walker fail-closed
//! review 6 round 3 finding 7; the review's probe `q1_md_writes.rs` `p1` /
//! `p2`, with twins).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, measured 2026-09-28):
//!   p1_plain_assign_through_cap_bug       -> VERIFICATION:- FAILED  ('v.capacity() == 1')
//!   p1_plain_assign_through_cap_safe      -> VERIFICATION:- SUCCESSFUL
//!   p2_plain_assign_through_len_bug       -> VERIFICATION:- FAILED  ('v.len() == 0')
//!   p2_plain_assign_through_len_safe      -> VERIFICATION:- SUCCESSFUL
//!   p3_assign_other_vec_through_len_bug   -> VERIFICATION:- FAILED  ('v.len() == 0')
//!   p3_assign_other_vec_through_len_safe  -> VERIFICATION:- SUCCESSFUL
//!   p4_reset_through_fn_len_bug           -> VERIFICATION:- FAILED  ('v.len() == 2')
//!   p5_string_assign_through_len_bug      -> VERIFICATION:- FAILED  ('s.len() == 0')
//!
//! MECHANISM UNDER TEST. A collection's length, capacity and presence live in
//! CHC side state keyed by its local, which `*r = value` (the deref store
//! handlers) never touched: `v.len()` read the value before the store, so
//! every bug row verified clean and every safe twin was certified a Genuine
//! failure, on main and on the branch. The store now fails closed where the
//! target carries such side state, or cannot be named and is a collection
//! (`chc/stmt/codegen_stmt_assign_simple_collection.rs`,
//! `deref_store_collection_side_state_unmodelled`). Propagating the stored
//! local's side state was measured and rejected (the temporary's is not live
//! across the blocks between): the safe twins are the fail-closed cost.
#[kani::proof]
fn p1_plain_assign_through_cap_bug() {
    let mut v = Vec::<u8>::with_capacity(1);
    {
        let r = &mut v;
        *r = Vec::with_capacity(8);
    }
    assert!(v.capacity() == 1);
}

#[kani::proof]
fn p1_plain_assign_through_cap_safe() {
    let mut v = Vec::<u8>::with_capacity(1);
    {
        let r = &mut v;
        *r = Vec::with_capacity(8);
    }
    assert!(v.capacity() >= 8);
}

#[kani::proof]
fn p2_plain_assign_through_len_bug() {
    let mut v = Vec::<u8>::new();
    {
        let r = &mut v;
        *r = vec![1, 2, 3];
    }
    assert!(v.len() == 0);
}

#[kani::proof]
fn p2_plain_assign_through_len_safe() {
    let mut v = Vec::<u8>::new();
    {
        let r = &mut v;
        *r = vec![1, 2, 3];
    }
    assert!(v.len() == 3);
}

#[kani::proof]
fn p3_assign_other_vec_through_len_bug() {
    let mut v = Vec::<u8>::new();
    let mut w = Vec::<u8>::new();
    w.push(7);
    w.push(8);
    {
        let r = &mut v;
        *r = w;
    }
    assert!(v.len() == 0);
}

#[kani::proof]
fn p3_assign_other_vec_through_len_safe() {
    let mut v = Vec::<u8>::new();
    let mut w = Vec::<u8>::new();
    w.push(7);
    w.push(8);
    {
        let r = &mut v;
        *r = w;
    }
    assert!(v.len() == 2);
}

#[inline(never)]
fn reset(v: &mut Vec<u8>) {
    *v = Vec::new();
}

#[kani::proof]
fn p4_reset_through_fn_len_bug() {
    let mut v = vec![1u8, 2];
    reset(&mut v);
    assert!(v.len() == 2);
}

#[kani::proof]
fn p5_string_assign_through_len_bug() {
    let mut s = String::new();
    {
        let r = &mut s;
        *r = String::from("abc");
    }
    assert!(s.len() == 0);
}
