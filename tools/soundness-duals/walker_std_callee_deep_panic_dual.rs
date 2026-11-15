// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (both directions) -- a safe standard-library callee the CHC
//! inline walker havocs, which can fail for its caller below its own body
//! (Mechanism B's family, review round).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, measured 2026-09-27):
//!   bug_windows_zero_multi           -> VERIFICATION:- FAILED  (`windows(0)` panics in Option::expect;
//!                                        Kani prints its runtime-formatted-message placeholder)
//!   safe_windows_nonzero_multi       -> VERIFICATION:- SUCCESSFUL
//!   bug_step_by_zero_multi           -> VERIFICATION:- FAILED  ('assertion failed: step != 0' in StepBy::new)
//!   bug_slice_range_multi            -> VERIFICATION:- FAILED  (the range bounds panic below Index::index;
//!                                        the same placeholder)
//!   bug_map_fn_pointer_multi         -> VERIFICATION:- FAILED  (overflow in the fn the pointer names)
//!   bug_map_closure_get_unchecked_multi  -> VERIFICATION:- FAILED  ('Rust intrinsic assumption failed')
//!   safe_map_closure_get_unchecked_multi -> VERIFICATION:- SUCCESSFUL
//!   safe_slice_get_ub_precondition_multi  -> VERIFICATION:- SUCCESSFUL
//!   safe_slice_iter_ub_precondition_multi -> VERIFICATION:- SUCCESSFUL
//!
//! MECHANISM UNDER TEST. Each callee's argument is an array element read at a
//! symbolic index, which the walker skips, so the nested-call fallback havocs
//! the call under the blessed `nested_call_overapprox`. The first cut of
//! fix/chc-walker-fail-closed refused the blessing for a safe callee in
//! another crate on a panic in its OWN body or an obligation in the crate's
//! code reached by DIRECT calls. A panic one or more calls down (`windows`,
//! `step_by`, `&s[..w]`) and a function pointer into the crate's code
//! (`Option::map(f)`) kept the blessing, and the bug rows verified SUCCESSFUL
//! clean on the a15de6272 base bundle and on that cut. A closure that calls an
//! `unsafe` std function owes that function's preconditions, whose checks sit
//! in the std body (`get_unchecked`'s `assume`). FIXED in the review round
//! (`obligation_free_walk::safe_foreign_callee_may_fail`): panics at any depth,
//! the crate's own code, the preconditions of `unsafe` functions it calls, and
//! any call the walk cannot follow refuse the blessing. The UB checks inside
//! safe std code do not (a safe function cannot reach UB for any argument):
//! `safe_slice_iter_ub_precondition_multi` holds that line (`Iter::new` reaches
//! `NonNull::new_unchecked`'s `assert_unsafe_precondition!`), with
//! `safe_slice_get_ub_precondition_multi` beside it. The other safe rows pay the
//! precision cost until the walker builds the array and walks the call.
//! Promoted from the review probe rv_stdcallee.rs.
//!
//! Lane scope: CHC only.
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options --harness-timeout=30s walker_std_callee_deep_panic_dual.rs

/// Keeps its argument alive through rustc's MIR optimisations and is
/// obligation-free by inspection (see `unchecked_arith_walker_dual.rs`).
#[inline(never)]
fn sink<T>(_value: T) {}

#[inline(never)]
fn add200(v: u8) -> u8 {
    v + 200
}

pub struct Other;

// `slice::windows(0)`: the panic is in Option::expect, one call below.
pub trait TWin {
    fn run(&self, a: u8, i: u8) -> u8;
}
pub struct CWin;
impl TWin for CWin {
    fn run(&self, a: u8, i: u8) -> u8 {
        let arr = [a, 1, 2, 3];
        let w = arr[(i % 4) as usize] as usize;
        let s: &[u8] = &[1, 2, 3, 4];
        sink(s.windows(w));
        a
    }
}
impl TWin for Other {
    fn run(&self, a: u8, _i: u8) -> u8 {
        a
    }
}

#[kani::proof]
fn bug_windows_zero_multi() {
    let a: u8 = kani::any();
    let i: u8 = kani::any();
    let o: Box<dyn TWin> = if kani::any() { Box::new(CWin) } else { Box::new(Other) };
    sink(o.run(a, i));
}

#[kani::proof]
fn safe_windows_nonzero_multi() {
    let a: u8 = kani::any();
    let i: u8 = kani::any();
    kani::assume(a != 0);
    let o: Box<dyn TWin> = if kani::any() { Box::new(CWin) } else { Box::new(Other) };
    sink(o.run(a, i));
}

// `Iterator::step_by(0)`: the assert is in StepBy::new.
pub trait TStep {
    fn run(&self, a: u8, i: u8) -> u8;
}
pub struct CStep;
impl TStep for CStep {
    fn run(&self, a: u8, i: u8) -> u8 {
        let arr = [a, 1, 2, 3];
        let w = arr[(i % 4) as usize] as usize;
        sink((0..10u8).step_by(w));
        a
    }
}
impl TStep for Other {
    fn run(&self, a: u8, _i: u8) -> u8 {
        a
    }
}

#[kani::proof]
fn bug_step_by_zero_multi() {
    let a: u8 = kani::any();
    let i: u8 = kani::any();
    let o: Box<dyn TStep> = if kani::any() { Box::new(CStep) } else { Box::new(Other) };
    sink(o.run(a, i));
}

// `&s[..w]`: the bounds panic is several calls below Index::index.
pub trait TRange {
    fn run(&self, a: u8, i: u8) -> u8;
}
pub struct CRange;
impl TRange for CRange {
    fn run(&self, a: u8, i: u8) -> u8 {
        let arr = [a, 1, 2, 3];
        let w = arr[(i % 4) as usize] as usize;
        let s: &[u8] = &[1, 2, 3, 4];
        sink(&s[..w]);
        a
    }
}
impl TRange for Other {
    fn run(&self, a: u8, _i: u8) -> u8 {
        a
    }
}

#[kani::proof]
fn bug_slice_range_multi() {
    let a: u8 = kani::any();
    let i: u8 = kani::any();
    let o: Box<dyn TRange> = if kani::any() { Box::new(CRange) } else { Box::new(Other) };
    sink(o.run(a, i));
}

// `Option::map` with a function pointer to a local fn that overflows.
pub trait TMapFp {
    fn run(&self, a: u8, i: u8) -> u8;
}
pub struct CMapFp;
impl TMapFp for CMapFp {
    fn run(&self, a: u8, i: u8) -> u8 {
        let arr = [Some(a), None, Some(1), Some(2)];
        let o = arr[(i % 4) as usize];
        let f: fn(u8) -> u8 = add200;
        sink(o.map(f));
        a
    }
}
impl TMapFp for Other {
    fn run(&self, a: u8, _i: u8) -> u8 {
        a
    }
}

#[kani::proof]
fn bug_map_fn_pointer_multi() {
    let a: u8 = kani::any();
    let i: u8 = kani::any();
    let o: Box<dyn TMapFp> = if kani::any() { Box::new(CMapFp) } else { Box::new(Other) };
    sink(o.run(a, i));
}

// `Option::map` with a closure that calls the `unsafe` `get_unchecked`: the
// precondition's `assume` sits in the std body.
pub trait TMapGu {
    fn run(&self, a: u8, i: u8) -> u8;
}
pub struct CMapGu;
impl TMapGu for CMapGu {
    fn run(&self, a: u8, i: u8) -> u8 {
        let arr = [Some(a), None, Some(1), Some(2)];
        let o = arr[(i % 4) as usize];
        let table: [u8; 4] = [10, 20, 30, 40];
        sink(o.map(|v| unsafe { *table.get_unchecked(v as usize) }));
        a
    }
}
impl TMapGu for Other {
    fn run(&self, a: u8, _i: u8) -> u8 {
        a
    }
}

#[kani::proof]
fn bug_map_closure_get_unchecked_multi() {
    let a: u8 = kani::any();
    let i: u8 = kani::any();
    let o: Box<dyn TMapGu> = if kani::any() { Box::new(CMapGu) } else { Box::new(Other) };
    sink(o.run(a, i));
}

#[kani::proof]
fn safe_map_closure_get_unchecked_multi() {
    let a: u8 = kani::any();
    let i: u8 = kani::any();
    kani::assume(a < 4);
    let o: Box<dyn TMapGu> = if kani::any() { Box::new(CMapGu) } else { Box::new(Other) };
    sink(o.run(a, i));
}

// Precision: `slice::get` is safe and cannot fail; the only failure its
// callees can reach is an `unsafe` helper's UB precondition check
// (`assert_unsafe_precondition!`), which cannot fail for a safe caller.
pub trait TGet {
    fn run(&self, a: u8, i: u8) -> u8;
}
pub struct CGet;
impl TGet for CGet {
    fn run(&self, a: u8, i: u8) -> u8 {
        let arr = [a, 1, 2, 3];
        let w = arr[(i % 4) as usize] as usize;
        let s: &[u8] = &[1, 2, 3, 4];
        sink(s.get(w));
        a
    }
}
impl TGet for Other {
    fn run(&self, a: u8, _i: u8) -> u8 {
        a
    }
}

#[kani::proof]
fn safe_slice_get_ub_precondition_multi() {
    let a: u8 = kani::any();
    let i: u8 = kani::any();
    let o: Box<dyn TGet> = if kani::any() { Box::new(CGet) } else { Box::new(Other) };
    sink(o.run(a, i));
}

// Precision: `slice::iter` is safe and cannot fail; `Iter::new` reaches
// `NonNull::new_unchecked`, whose `assert_unsafe_precondition!` check panics
// through `panic_nounwind` and cannot fail for a safe caller.
pub trait TIter {
    fn run(&self, a: u8, i: u8) -> u8;
}
pub struct CIter;
impl TIter for CIter {
    fn run(&self, a: u8, i: u8) -> u8 {
        let arr = [a, 1, 2, 3];
        let v = arr[(i % 4) as usize];
        let arr2 = [v, v, v];
        sink(arr2.iter());
        a
    }
}
impl TIter for Other {
    fn run(&self, a: u8, _i: u8) -> u8 {
        a
    }
}

#[kani::proof]
fn safe_slice_iter_ub_precondition_multi() {
    let a: u8 = kani::any();
    let i: u8 = kani::any();
    let o: Box<dyn TIter> = if kani::any() { Box::new(CIter) } else { Box::new(Other) };
    sink(o.run(a, i));
}
