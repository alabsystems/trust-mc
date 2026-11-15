// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (both directions) -- a slice local that holds an array's
//! slice view on one path of a walked body and another slice on the other
//! (fix/chc-walker-fail-closed, repair round 1, walker fail-closed review 6
//! finding 1; the review's probes `c3_len_in_walk_bug`, `s1_len_matches_safe`
//! and `r1_len_rev_bug`, promoted).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, measured 2026-09-28):
//!   c3_len_in_walk_bug           -> VERIFICATION:- FAILED  ('assertion failed: n == 4')
//!   s1_len_matches_safe          -> VERIFICATION:- SUCCESSFUL
//!   r1_len_rev_bug               -> VERIFICATION:- FAILED  ('assertion failed: s.len() == 4')
//!   l1_len_loop_reassign_bug     -> VERIFICATION:- FAILED  ('assertion failed: n == 4')
//!   l1_len_loop_reassign_safe    -> VERIFICATION:- SUCCESSFUL
//!
//! MECHANISM UNDER TEST. Package round 2 (item c) records an array slice
//! view's length, `&[T; N] as &[T]`, in the walker's side table
//! (`ref_resolution.subslice_len`) so `PtrMetadata` of the view reads `N`.
//! The table is keyed by local and was only ever inserted into: an entry
//! outlived the value it described. The walker walks every SwitchInt arm to
//! the body's return on a path of its own, and the table was not restored
//! between arms, so the array arm's `len(s) = 4` was read on the `s = v`
//! arm: `c3_len_in_walk_bug` proved clean (a missed bug) and
//! `s1_len_matches_safe` FAILED Genuine (a false certificate) on the round-2
//! bundle 5d66fe32. The arms now start from the table as it was at the
//! SwitchInt (`switchint.rs`), every whole-local write replaces the local's
//! entry (`statement_metadata.rs`), and the view's length is recorded only by
//! the walker, whose walk scopes the table to its body (`walker.rs`, both
//! front doors). The loop rows write the same local twice on ONE path: the
//! second iteration's `s = v` must not keep the first's array length.
//!
//! Lane scope: CHC only.
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options --harness-timeout=30s walker_stale_slice_len_dual.rs

/// Keeps its argument alive through rustc's MIR optimisations.
#[inline(never)]
fn sink<T>(_v: T) {}

pub struct Other;

pub trait PickLen { fn f(&self, c: bool, v: &[u8]) -> u8; }
impl PickLen for Other { fn f(&self, _c: bool, _v: &[u8]) -> u8 { 0 } }

// The array arm first in source order: `s.len()` is 2 on the `v` arm.
pub struct A3;
impl PickLen for A3 {
    fn f(&self, c: bool, v: &[u8]) -> u8 {
        let arr = [1u8, 2, 3, 4];
        let s: &[u8] = if c { &arr } else { v };
        let n = s.len();
        assert!(n == 4);
        0
    }
}
#[kani::proof]
fn c3_len_in_walk_bug() {
    let data: [u8; 2] = kani::any();
    let c: bool = kani::any();
    let o: Box<dyn PickLen> = if kani::any() { Box::new(A3) } else { Box::new(Other) };
    sink(o.f(c, &data));
}

// Each arm's length is the right one.
pub struct S1;
impl PickLen for S1 {
    fn f(&self, c: bool, v: &[u8]) -> u8 {
        let arr = [1u8, 2, 3, 4];
        let s: &[u8] = if c { &arr } else { v };
        let n = s.len();
        if !c { assert!(n == v.len()); } else { assert!(n == 4); }
        0
    }
}
#[kani::proof]
fn s1_len_matches_safe() {
    let data: [u8; 2] = kani::any();
    let c: bool = kani::any();
    let o: Box<dyn PickLen> = if kani::any() { Box::new(S1) } else { Box::new(Other) };
    sink(o.f(c, &data));
}

// The `v` arm first in source order.
pub struct Rev;
impl PickLen for Rev {
    fn f(&self, c: bool, v: &[u8]) -> u8 {
        let arr = [1u8, 2, 3, 4];
        let s: &[u8] = if c { v } else { &arr };
        assert!(s.len() == 4);
        0
    }
}
#[kani::proof]
fn r1_len_rev_bug() {
    let data: [u8; 2] = kani::any();
    let c: bool = kani::any();
    let o: Box<dyn PickLen> = if kani::any() { Box::new(Rev) } else { Box::new(Other) };
    sink(o.f(c, &data));
}

// One path writes the same slice local twice: the array view on the first
// iteration, `v` on the second.
pub trait Twice { fn f(&self, v: &[u8]) -> usize; }
impl Twice for Other { fn f(&self, _v: &[u8]) -> usize { 0 } }
pub struct L1;
impl Twice for L1 {
    fn f(&self, v: &[u8]) -> usize {
        let arr = [1u8, 2, 3, 4];
        let mut n = 0usize;
        let mut k = 0u8;
        while k < 2 {
            let s: &[u8] = if k == 0 { &arr } else { v };
            n = s.len();
            k += 1;
        }
        assert!(n == 4);
        n
    }
}
#[kani::proof]
fn l1_len_loop_reassign_bug() {
    let data: [u8; 2] = kani::any();
    let o: Box<dyn Twice> = if kani::any() { Box::new(L1) } else { Box::new(Other) };
    sink(o.f(&data));
}
pub struct L1s;
impl Twice for L1s {
    fn f(&self, v: &[u8]) -> usize {
        let arr = [1u8, 2, 3, 4];
        let mut n = 0usize;
        let mut k = 0u8;
        while k < 2 {
            let s: &[u8] = if k == 0 { &arr } else { v };
            n = s.len();
            k += 1;
        }
        assert!(n == v.len());
        n
    }
}
#[kani::proof]
fn l1_len_loop_reassign_safe() {
    let data: [u8; 2] = kani::any();
    let o: Box<dyn Twice> = if kani::any() { Box::new(L1s) } else { Box::new(Other) };
    sink(o.f(&data));
}
