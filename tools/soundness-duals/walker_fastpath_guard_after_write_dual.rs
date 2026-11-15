// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (KNOWN-RED missed-bug tracker) -- a `Drop::drop` body the CHC
//! walker walks at a `Box<dyn>` drop that records a check, then writes a field
//! of `*self`, then calls a KNOWN-CALL FAST PATH whose panic condition reads
//! that field: `Option::unwrap`, `Option::expect`, `Ord::clamp` on `u8` and on
//! `*const u8`.
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3; see the manifest entry):
//!   bug_early_check_then_write_unwrap     -> VERIFICATION:- FAILED  ('called `Option::unwrap()` on a `None` value')
//!   safe_early_check_then_write_unwrap    -> VERIFICATION:- SUCCESSFUL
//!   bug_write_unwrap_no_early_check       -> VERIFICATION:- FAILED  ('called `Option::unwrap()` on a `None` value'; control)
//!   safe_write_unwrap_no_early_check      -> VERIFICATION:- SUCCESSFUL
//!   bug_early_check_then_write_expect     -> VERIFICATION:- FAILED  (Kani's placeholder for the runtime-formatted expect message)
//!   safe_early_check_then_write_expect    -> VERIFICATION:- SUCCESSFUL
//!   bug_early_check_then_write_clamp      -> VERIFICATION:- FAILED  ('assertion failed: min <= max')
//!   safe_early_check_then_write_clamp     -> VERIFICATION:- SUCCESSFUL
//!   bug_early_check_then_write_ptr_clamp  -> VERIFICATION:- FAILED  ('assertion failed: min <= max')
//!   safe_early_check_then_write_ptr_clamp -> VERIFICATION:- SUCCESSFUL
//!
//! Measured 2026-09-24 at ay 5d900fd2f (CHC lane):
//!   harness                                branch 328b4a952027             main 72090d76d40a
//!   bug_early_check_then_write_unwrap      SUCCESSFUL clean                SUCCESSFUL clean
//!   safe_early_check_then_write_unwrap     SUCCESSFUL clean                SUCCESSFUL clean
//!   bug_write_unwrap_no_early_check        FAILED OverApproximation        SUCCESSFUL clean
//!   safe_write_unwrap_no_early_check       FAILED OverApproximation        SUCCESSFUL clean
//!   bug_early_check_then_write_expect      SUCCESSFUL clean                SUCCESSFUL clean
//!   safe_early_check_then_write_expect     SUCCESSFUL clean                SUCCESSFUL clean
//!   bug_early_check_then_write_clamp       SUCCESSFUL clean                SUCCESSFUL clean
//!   safe_early_check_then_write_clamp      SUCCESSFUL clean                SUCCESSFUL clean
//!   bug_early_check_then_write_ptr_clamp   SUCCESSFUL clean                FAILED (ay-chc inconclusive)
//!   safe_early_check_then_write_ptr_clamp  SUCCESSFUL clean                FAILED (ay-chc inconclusive)
//!
//! MECHANISM (a hole in the branch's walk_drop_body rule; the stale read is
//! pre-existing): the walker's nested-call arm (`call/codegen_call_virtual_inline/nested_call.rs`)
//! answers these callees from known-call fast paths that put the panic
//! condition in the returned VALUE as `ite(ok, v, __assert_fail_inline_*)`,
//! not as a deferred check: `try_inline_option_unwrap_call`
//! (`nested_option_unwrap.rs`, `__assert_fail_inline_option_unwrap`) for
//! unwrap and expect; `inline_known_call_expr_for_callee_path`
//! (`call/inline_known_calls.rs`, `__assert_fail_inline_bv_clamp`, and
//! `call/inline_known_calls_raw_ptr.rs`, `__assert_fail_inline_raw_ptr_clamp`)
//! for clamp. The guard reads the field as it was when the walk began: under
//! --debug on the branch bundle, Ord::clamp's result is
//! `(ite (bvule (select mem_u8 self) (select mem_u8 self+1)) .. __assert_fail_inline_bv_clamp_1)`
//! over a `mem_u8` with no store of the written `lo`, and the raw-pointer
//! clamp reads `lo` at `self+0` of `mem_ptr_u8` the same way.
//! `walk_drop_body` (`call/inline_body.rs`) records
//! `drop_body_check_after_walk_store` when the walk kept a deferred check
//! recorded after a store, or when it kept NO deferred check at all, stored,
//! and its value carries such a guard (`bare_guard_after_store`). An early
//! check recorded BEFORE the store (`self.b.unchecked_add(1)`) makes the list
//! non-empty with no check after the store, so neither arm fires and the stale
//! guard is proved: the bug_early_check_* rows are SUCCESSFUL clean. Without
//! the early check the bare-guard arm fires (--debug: `checks_after_store=0,
//! checks=0, bare_guard_after_store=true`) and both *_no_early_check rows FAIL
//! closed, the safe one as a precision cost.
//!
//! Not tracked: the false-certificate direction (entry None, written Some; the
//! verifier's p15_guard_false_cert.rs) is FAILED [AY:CTREX_CAT:OverApproximation]
//! on 'CHC verification: memory safety' (chc_sound_havoc_drop) on both bundles,
//! so it does not reach a Genuine certificate.
//!
//! Promoted from the 2026-09-24 walker drop-certificate verification (probe
//! p14_fastpath_guard.rs); the raw-pointer clamp pair is new.
//!
//! Lane scope: CHC only.
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options --harness-timeout=30s walker_fastpath_guard_after_write_dual.rs

/// Keeps its argument alive through rustc's MIR optimisations and is
/// obligation-free by inspection (see `unchecked_arith_walker_dual.rs`).
#[inline(never)]
fn sink<T>(_value: T) {}

fn below5() -> u8 {
    let x: u8 = kani::any();
    kani::assume(x < 5);
    x
}

// --- 1. an early check, a write of None, Option::unwrap ----------------------

pub trait T1 {
    fn id(&self) -> u8;
}
pub struct U1 {
    o: Option<u8>,
    b: u8,
    set: bool,
}
impl Drop for U1 {
    fn drop(&mut self) {
        sink(unsafe { self.b.unchecked_add(1) });
        self.o = if self.set { Some(3) } else { None };
        sink(self.o.unwrap());
    }
}
impl T1 for U1 {
    fn id(&self) -> u8 {
        1
    }
}

// --- 2. the same without the early check (the bare-guard rule applies) -------

pub trait T2 {
    fn id(&self) -> u8;
}
pub struct U2 {
    o: Option<u8>,
    set: bool,
}
impl Drop for U2 {
    fn drop(&mut self) {
        self.o = if self.set { Some(3) } else { None };
        sink(self.o.unwrap());
    }
}
impl T2 for U2 {
    fn id(&self) -> u8 {
        2
    }
}

// --- 3. an early check, a write of None, Option::expect ----------------------

pub trait T3 {
    fn id(&self) -> u8;
}
pub struct U3 {
    o: Option<u8>,
    b: u8,
    set: bool,
}
impl Drop for U3 {
    fn drop(&mut self) {
        sink(unsafe { self.b.unchecked_add(1) });
        self.o = if self.set { Some(3) } else { None };
        sink(self.o.expect("o is set"));
    }
}
impl T3 for U3 {
    fn id(&self) -> u8 {
        3
    }
}

// --- 4. an early check, a write of the lower bound, Ord::clamp ---------------

pub trait T4 {
    fn id(&self) -> u8;
}
pub struct U4 {
    lo: u8,
    hi: u8,
    v: u8,
    b: u8,
    k: u8,
}
impl Drop for U4 {
    fn drop(&mut self) {
        sink(unsafe { self.b.unchecked_add(1) });
        self.lo = self.lo.wrapping_add(self.k);
        sink(self.v.clamp(self.lo, self.hi));
    }
}
impl T4 for U4 {
    fn id(&self) -> u8 {
        4
    }
}

// --- 5. an early check, a write of a raw-pointer lower bound, Ord::clamp -----

static ARR: [u8; 32] = [0; 32];

pub trait T5 {
    fn id(&self) -> u8;
}
pub struct U5 {
    lo: *const u8,
    hi: *const u8,
    v: *const u8,
    b: u8,
    k: usize,
}
impl Drop for U5 {
    fn drop(&mut self) {
        sink(unsafe { self.b.unchecked_add(1) });
        self.lo = self.lo.wrapping_add(self.k);
        sink(self.v.clamp(self.lo, self.hi));
    }
}
impl T5 for U5 {
    fn id(&self) -> u8 {
        5
    }
}

#[kani::proof]
fn bug_early_check_then_write_unwrap() {
    let o: Box<dyn T1> = Box::new(U1 { o: Some(below5()), b: 1, set: false });
    sink(o.id());
}

#[kani::proof]
fn safe_early_check_then_write_unwrap() {
    let o: Box<dyn T1> = Box::new(U1 { o: Some(below5()), b: 1, set: true });
    sink(o.id());
}

#[kani::proof]
fn bug_write_unwrap_no_early_check() {
    let o: Box<dyn T2> = Box::new(U2 { o: Some(below5()), set: false });
    sink(o.id());
}

#[kani::proof]
fn safe_write_unwrap_no_early_check() {
    let o: Box<dyn T2> = Box::new(U2 { o: Some(below5()), set: true });
    sink(o.id());
}

#[kani::proof]
fn bug_early_check_then_write_expect() {
    let o: Box<dyn T3> = Box::new(U3 { o: Some(below5()), b: 1, set: false });
    sink(o.id());
}

#[kani::proof]
fn safe_early_check_then_write_expect() {
    let o: Box<dyn T3> = Box::new(U3 { o: Some(below5()), b: 1, set: true });
    sink(o.id());
}

#[kani::proof]
fn bug_early_check_then_write_clamp() {
    let o: Box<dyn T4> = Box::new(U4 { lo: below5(), hi: 10, v: 7, b: 1, k: 20 });
    sink(o.id());
}

#[kani::proof]
fn safe_early_check_then_write_clamp() {
    let o: Box<dyn T4> = Box::new(U4 { lo: below5(), hi: 10, v: 7, b: 1, k: 1 });
    sink(o.id());
}

#[kani::proof]
fn bug_early_check_then_write_ptr_clamp() {
    let base = ARR.as_ptr();
    let o: Box<dyn T5> = Box::new(U5 {
        lo: base.wrapping_add(below5() as usize),
        hi: base.wrapping_add(10),
        v: base.wrapping_add(7),
        b: 1,
        k: 20,
    });
    sink(o.id());
}

#[kani::proof]
fn safe_early_check_then_write_ptr_clamp() {
    let base = ARR.as_ptr();
    let o: Box<dyn T5> = Box::new(U5 {
        lo: base.wrapping_add(below5() as usize),
        hi: base.wrapping_add(10),
        v: base.wrapping_add(7),
        b: 1,
        k: 1,
    });
    sink(o.id());
}
