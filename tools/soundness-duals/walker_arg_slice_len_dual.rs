// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (both directions) -- a walked body's ARGUMENT local and the
//! walker's local-keyed slice-length side table (fix/chc-walker-fail-closed,
//! repair round 2, walker fail-closed review 6 round 2 finding 3; the
//! review's probe `rp3b_slice_len_index.rs`, promoted).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, measured 2026-09-28):
//!   b_nested_arg_reads_caller_view_bug   -> VERIFICATION:- FAILED  ('assertion failed: n == 4')
//!   b_nested_arg_reads_caller_view_safe  -> VERIFICATION:- SUCCESSFUL
//!   c_walked_arg_reads_host_entry_bug    -> VERIFICATION:- FAILED  ('assertion failed: v.len() == 6')
//!   c_walked_arg_reads_host_entry_safe   -> VERIFICATION:- SUCCESSFUL
//!
//! MECHANISM UNDER TEST. The subslice side table (`ref_resolution.
//! subslice_len`) is keyed by local INDEX, and every walked body has its own
//! index space. Repair round 1 scoped a walk's entries to its body (save
//! and restore) but never cleared them on entry, so an argument local, which
//! the walk never writes, read whatever the caller walk or the host left at
//! the same index: (B) a nested callee's `_5` read the caller walk's `_5`,
//! an array view of length 4; (C) a walked method's `_3` read the harness's
//! `_3`, a six-element subslice. Both bug rows verified clean and both safe
//! rows were certified Genuine on the repair-round-1 bundle 8626027c (C's
//! missed bug is on main too). A walk now clears every entry of its body's
//! locals on entry and applies only the argument entries its front door
//! hands over (`walker.rs`, `enter_body_subslice_scope`).
//!
//! Lane scope: CHC only.
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options --harness-timeout=30s walker_arg_slice_len_dual.rs

/// Keeps its argument alive through rustc's MIR optimisations.
#[inline(never)]
fn sink<T>(_v: T) {}

pub struct Other;

pub trait PickLen {
    fn f(&self, c: bool, v: &[u8]) -> u8;
}
impl PickLen for Other {
    fn f(&self, _c: bool, _v: &[u8]) -> u8 {
        0
    }
}

#[inline(never)]
fn lenof(_x: usize, _y: usize, _z: usize, _w: usize, s: &[u8]) -> usize {
    s.len()
}

// B: in `f`, `_5` is `a` (the view of `arr`); in `lenof`, `_5` is `s`.
pub struct Bbug;
impl PickLen for Bbug {
    fn f(&self, _c: bool, v: &[u8]) -> u8 {
        let arr = [1u8, 2, 3, 4];
        let a: &[u8] = &arr;
        let k = a.len();
        let n = lenof(k, k, k, k, v);
        assert!(n == 4);
        0
    }
}
pub struct Bsafe;
impl PickLen for Bsafe {
    fn f(&self, _c: bool, v: &[u8]) -> u8 {
        let arr = [1u8, 2, 3, 4];
        let a: &[u8] = &arr;
        let k = a.len();
        let n = lenof(k, k, k, k, v);
        assert!(n == v.len());
        0
    }
}

#[kani::proof]
fn b_nested_arg_reads_caller_view_bug() {
    let data: [u8; 2] = kani::any();
    let c: bool = kani::any();
    let o: Box<dyn PickLen> = if kani::any() { Box::new(Bbug) } else { Box::new(Other) };
    sink(o.f(c, &data));
}

#[kani::proof]
fn b_nested_arg_reads_caller_view_safe() {
    let data: [u8; 2] = kani::any();
    let c: bool = kani::any();
    let o: Box<dyn PickLen> = if kani::any() { Box::new(Bsafe) } else { Box::new(Other) };
    sink(o.f(c, &data));
}

// C: `f`'s `v` is its `_3`; the harness's `_3` is `s6`, a 6-element subslice.
pub struct Cbug;
impl PickLen for Cbug {
    fn f(&self, _c: bool, v: &[u8]) -> u8 {
        assert!(v.len() == 6);
        0
    }
}
pub struct Csafe;
impl PickLen for Csafe {
    fn f(&self, _c: bool, v: &[u8]) -> u8 {
        assert!(v.len() == 2);
        0
    }
}

#[kani::proof]
fn c_walked_arg_reads_host_entry_bug() {
    let big: [u8; 8] = kani::any();
    let data: [u8; 2] = kani::any();
    let s6: &[u8] = &big[..6];
    let c: bool = kani::any();
    let o: Box<dyn PickLen> = if kani::any() { Box::new(Cbug) } else { Box::new(Other) };
    sink(s6.len());
    sink(o.f(c, &data));
}

#[kani::proof]
fn c_walked_arg_reads_host_entry_safe() {
    let big: [u8; 8] = kani::any();
    let data: [u8; 2] = kani::any();
    let s6: &[u8] = &big[..6];
    let c: bool = kani::any();
    let o: Box<dyn PickLen> = if kani::any() { Box::new(Csafe) } else { Box::new(Other) };
    sink(s6.len());
    sink(o.f(c, &data));
}
