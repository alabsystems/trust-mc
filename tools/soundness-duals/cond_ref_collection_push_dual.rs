// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (both directions) -- a collection mutated through a
//! reference that names one of two collections (fix/chc-walker-fail-closed,
//! walker fail-closed repair round 5, review finding 7, `c8`).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, measured 2026-10-01 to
//! 2026-10-02):
//!   c1_cond_ref_push_bug      -> VERIFICATION:- FAILED  ('assertion failed: v1.len() == 0')
//!   c1_cond_ref_push_safe     -> VERIFICATION:- SUCCESSFUL
//!   c2_cond_ref_clear_bug     -> VERIFICATION:- FAILED  ('assertion failed: v1.len() == 2')
//!   c3_cond_ref_len_read_safe -> VERIFICATION:- SUCCESSFUL
//!   c3_cond_ref_len_read_bug  -> VERIFICATION:- FAILED  ('assertion failed: r.len() == 2')
//!
//! MECHANISM UNDER TEST. A collection's side state is keyed by the local the
//! receiver reference points to, and a reference with two producers
//! (`if c { &mut v1 } else { &mut v2 }`) names one of them, or none: the push
//! updated the reference's own length var and neither `v1`'s nor `v2`'s, so
//! `v1.len() == 0` verified clean where Kani fails and the true
//! `v1.len() + v2.len() == 1` was certified a Genuine failure. A collection
//! method called through such a path-dependent reference fails closed.

#[kani::proof]
fn c1_cond_ref_push_bug() {
    let mut v1: Vec<u8> = Vec::new();
    let mut v2: Vec<u8> = Vec::new();
    let c: bool = kani::any();
    {
        let r: &mut Vec<u8> = if c { &mut v1 } else { &mut v2 };
        r.push(7);
    }
    assert!(v1.len() == 0);
}

#[kani::proof]
fn c1_cond_ref_push_safe() {
    let mut v1: Vec<u8> = Vec::new();
    let mut v2: Vec<u8> = Vec::new();
    let c: bool = kani::any();
    {
        let r: &mut Vec<u8> = if c { &mut v1 } else { &mut v2 };
        r.push(7);
    }
    assert!(v1.len() + v2.len() == 1);
}

#[kani::proof]
fn c2_cond_ref_clear_bug() {
    let mut v1: Vec<u8> = vec![1, 2];
    let mut v2: Vec<u8> = vec![3];
    let c: bool = kani::any();
    {
        let r: &mut Vec<u8> = if c { &mut v1 } else { &mut v2 };
        r.clear();
    }
    assert!(v1.len() == 2);
}

#[kani::proof]
fn c3_cond_ref_len_read_safe() {
    let v1: Vec<u8> = vec![1, 2];
    let v2: Vec<u8> = vec![3];
    let c: bool = kani::any();
    let r: &Vec<u8> = if c { &v1 } else { &v2 };
    assert!(r.len() == if c { 2 } else { 1 });
}

#[kani::proof]
fn c3_cond_ref_len_read_bug() {
    let v1: Vec<u8> = vec![1, 2];
    let v2: Vec<u8> = vec![3];
    let c: bool = kani::any();
    let r: &Vec<u8> = if c { &v1 } else { &v2 };
    assert!(r.len() == 2);
}
