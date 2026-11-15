// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (KNOWN-RED missed-bug tracker) -- a `Drop::drop` body the
//! CHC walker walks at a `Box<dyn>` or `Rc` drop, whose checks are placed on
//! the wrong state or thrown away.
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3; see the manifest entry):
//!   bug_single_drop_write_check     -> VERIFICATION:- FAILED  ('attempt to compute `unchecked_add` which would overflow')
//!   safe_single_drop_write_check    -> VERIFICATION:- SUCCESSFUL
//!   safe_single_drop_entry_overflows -> VERIFICATION:- SUCCESSFUL
//!   bug_multi_drop_write_check      -> VERIFICATION:- FAILED  (same check)
//!   safe_multi_drop_write_check     -> VERIFICATION:- SUCCESSFUL
//!   bug_drop_write_assert           -> VERIFICATION:- FAILED  ('assertion failed: self.a < 250')
//!   bug_rc_drop_branch_bail         -> VERIFICATION:- FAILED  (same unchecked_add check; also Kani's unsupported InlineAsm check)
//!   bug_boxdyn_drop_branch_bail     -> VERIFICATION:- FAILED  (same)
//!   bug_rc_drop_branch_no_bail      -> VERIFICATION:- FAILED  ('attempt to compute `unchecked_add` which would overflow'; control)
//!
//! MECHANISMS (pre-existing; the first is now accounted, not fixed):
//! 1. A DROP BODY THAT WRITES A FIELD OF `*self` AND THEN CHECKS IT. The drop
//!    consumers emit the walked body's deferred checks
//!    (`rules/codegen_rules/transition_drop/dyn_dispatch.rs`, single candidate,
//!    and `dyn_dispatch_multi.rs`, multi candidate, both
//!    `emit_deferred_inline_checks_at`), but the walk reads `self.a` from the
//!    drop block's ENTRY heap cell, not the value it just wrote: for
//!    `self.a = self.a.wrapping_add(self.c); self.a.unchecked_add(self.b)` the
//!    error rule is `¬(bvadd mem_u8_at_A mem_u8_at_B ≥ mem_u8_at_A)` over the
//!    pre-write `a`, and it is proved. The assert! twin is missed on main too.
//!    The same read makes a correct program FAIL when the ENTRY value overflows
//!    and the written one does not (`safe_single_drop_entry_overflows`).
//!    ACCOUNTED: every drop consumer now walks through `walk_drop_body`
//!    (`call/inline_body.rs`), which records `drop_body_check_after_walk_store`
//!    (not blessed) when the walked body recorded a check after it wrote
//!    through a pointer. The checks are still emitted over the entry cell;
//!    the record keeps a counterexample from them from being certified
//!    Genuine and a proof resting on them from standing, so the bug_ rows
//!    FAIL closed (OverApproximation) and the safe_ rows are false failures.
//! 2. A SWITCHINT ARM OF A WALKED DROP BODY WHOSE WALK BAILS. The arm records
//!    its `unchecked_add` check, then hits a bail that books no FailClose of its
//!    own (an InlineAsm terminator: the unsupported-terminator arm).
//!    `switchint_branch_fallback` (`codegen_call_virtual_inline/switchint.rs`)
//!    replaces the arm with a fresh `switchint_branch_overapprox` value, a
//!    blessed SoundHavoc, and returns no deferred checks, so the check is lost
//!    and the proof is clean. Without the bail the drop is caught
//!    (`bug_rc_drop_branch_no_bail`).
//!
//! Promoted from the 2026-09-24 adversarial review (drop-and-closure lens,
//! drop-closure/p10_body_write_read.rs, p6_drop_state.rs,
//! p11_drop_write_assert.rs; verifier probes q1_stale_mechanism.rs,
//! q3_dyn_drop_branch_bail.rs and q4_bail_variants.rs).
//!
//! Lane scope: CHC only.
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options --harness-timeout=30s walker_drop_body_state_dual.rs

/// Keeps its argument alive through rustc's MIR optimisations and is
/// obligation-free by inspection (see `unchecked_arith_walker_dual.rs`).
#[inline(never)]
fn sink<T>(_value: T) {}

// --- one Drop impl behind the trait (single-candidate drop) -----------------

pub trait Single {
    fn id(&self) -> u8;
}
pub struct SW {
    a: u8,
    b: u8,
    c: u8,
}
impl Drop for SW {
    fn drop(&mut self) {
        self.a = self.a.wrapping_add(self.c);
        sink(unsafe { self.a.unchecked_add(self.b) });
    }
}
impl Single for SW {
    fn id(&self) -> u8 {
        3
    }
}

// --- three Drop impls behind the trait (multi-candidate drop) ---------------

pub trait Multi {
    fn id(&self) -> u8;
}
pub struct MA {
    a: u8,
    b: u8,
}
pub struct MB {
    a: u8,
    b: u8,
}
pub struct MW {
    a: u8,
    b: u8,
    c: u8,
}
impl Drop for MA {
    fn drop(&mut self) {
        sink(unsafe { self.a.unchecked_add(self.b) });
    }
}
impl Drop for MB {
    fn drop(&mut self) {
        sink(unsafe { self.a.unchecked_sub(self.b) });
    }
}
impl Drop for MW {
    fn drop(&mut self) {
        self.a = self.a.wrapping_add(self.c);
        sink(unsafe { self.a.unchecked_add(self.b) });
    }
}
impl Multi for MA {
    fn id(&self) -> u8 {
        1
    }
}
impl Multi for MB {
    fn id(&self) -> u8 {
        2
    }
}
impl Multi for MW {
    fn id(&self) -> u8 {
        3
    }
}

// --- an assert! after the write (single candidate) --------------------------

pub trait Asserting {
    fn id(&self) -> u8;
}
pub struct DX {
    a: u8,
    c: u8,
}
impl Drop for DX {
    fn drop(&mut self) {
        self.a = self.a.wrapping_add(self.c);
        assert!(self.a < 250);
    }
}
impl Asserting for DX {
    fn id(&self) -> u8 {
        3
    }
}

// --- a SwitchInt arm that bails after recording its check -------------------

pub trait Branchy {
    fn id(&self) -> u8;
}
pub struct Bail {
    a: u8,
    b: u8,
    c: bool,
}
impl Drop for Bail {
    fn drop(&mut self) {
        if self.c {
            let s = unsafe { self.a.unchecked_add(self.b) };
            unsafe { core::arch::asm!("nop") };
            sink(s);
        }
    }
}
pub struct NoBail {
    a: u8,
    b: u8,
    c: bool,
}
impl Drop for NoBail {
    fn drop(&mut self) {
        if self.c {
            let s = unsafe { self.a.unchecked_add(self.b) };
            sink(s);
        }
    }
}
impl Branchy for Bail {
    fn id(&self) -> u8 {
        1
    }
}
impl Branchy for NoBail {
    fn id(&self) -> u8 {
        2
    }
}

#[kani::proof]
fn bug_single_drop_write_check() {
    let x: u8 = kani::any();
    kani::assume(x < 50);
    let o: Box<dyn Single> = Box::new(SW { a: x, b: 1, c: 250 });
    sink(o.id());
}

#[kani::proof]
fn safe_single_drop_write_check() {
    let x: u8 = kani::any();
    kani::assume(x < 5);
    let o: Box<dyn Single> = Box::new(SW { a: x, b: 1, c: 250 });
    sink(o.id());
}

// Entry a = 255 would overflow, but the write makes a = 0 first.
#[kani::proof]
fn safe_single_drop_entry_overflows() {
    let o: Box<dyn Single> = Box::new(SW { a: 255, b: 1, c: 1 });
    sink(o.id());
}

#[kani::proof]
fn bug_multi_drop_write_check() {
    let x: u8 = kani::any();
    kani::assume(x < 50);
    let o: Box<dyn Multi> = Box::new(MW { a: x, b: 1, c: 250 });
    sink(o.id());
}

#[kani::proof]
fn safe_multi_drop_write_check() {
    let x: u8 = kani::any();
    kani::assume(x < 5);
    let o: Box<dyn Multi> = Box::new(MW { a: x, b: 1, c: 250 });
    sink(o.id());
}

#[kani::proof]
fn bug_drop_write_assert() {
    let x: u8 = kani::any();
    kani::assume(x < 50);
    let o: Box<dyn Asserting> = Box::new(DX { a: x, c: 250 });
    sink(o.id());
}

#[kani::proof]
fn bug_rc_drop_branch_bail() {
    let o = std::rc::Rc::new(Bail { a: kani::any(), b: kani::any(), c: kani::any() });
    sink(o.id());
}

#[kani::proof]
fn bug_boxdyn_drop_branch_bail() {
    let o: Box<dyn Branchy> = Box::new(Bail { a: kani::any(), b: kani::any(), c: kani::any() });
    sink(o.id());
}

#[kani::proof]
fn bug_rc_drop_branch_no_bail() {
    let o = std::rc::Rc::new(NoBail { a: kani::any(), b: kani::any(), c: kani::any() });
    sink(o.id());
}
