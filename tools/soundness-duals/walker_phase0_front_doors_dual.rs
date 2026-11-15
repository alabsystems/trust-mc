// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL -- Phase 0 of the dyn-walker write/read design
//! (docs/chc-hole-fix-designs-2026-09-24.md, section 2) across the walker's
//! front doors: a two-candidate dyn dispatch, a fn_inline body, an FnMut
//! closure, a walked Drop body, a reborrow inside a dyn body, and a fn_inline
//! read of a memory-backed referent.
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3; see the manifest entry):
//!   bug_dispatch_store_unguarded     -> VERIFICATION:- FAILED  ('assertion failed: unsafe { G } == 200')
//!   safe_dispatch_store_unguarded    -> VERIFICATION:- SUCCESSFUL
//!   bug_fninline_arm_store           -> VERIFICATION:- FAILED  ('assertion failed: unsafe { H } == 7')
//!   safe_fninline_arm_store          -> VERIFICATION:- SUCCESSFUL
//!   bug_closure_capture_write_read   -> VERIFICATION:- FAILED  ('assertion failed: r == 0')
//!   safe_closure_capture_write_read  -> VERIFICATION:- SUCCESSFUL
//!   bug_drop_static_write_read       -> VERIFICATION:- FAILED  ('attempt to compute `unchecked_add` which would overflow')
//!   bug_dyn_reborrow_write           -> VERIFICATION:- FAILED  ('assertion failed: p.f == 0')
//!   safe_dyn_reborrow_write          -> VERIFICATION:- SUCCESSFUL
//!   bug_fninline_mem_ref_read        -> VERIFICATION:- FAILED  ('assertion failed: r != a')
//!   safe_fninline_mem_ref_read       -> VERIFICATION:- SUCCESSFUL
//!
//! WHAT IT GUARDS. `bug_dispatch_store_unguarded` is a missed bug on main
//! (SUCCESSFUL clean at ay 6818b5d06): one of two dyn candidates stores a
//! static, the walk's store (and its mutable-static state-variable mirror) is
//! kept in the rule's heap state, and the host applies it on BOTH dispatch
//! paths, so `G == 200` after the call is proved although under the other
//! candidate nothing wrote G. Phase 0 records `walker_store_in_branch_arm`
//! for a memory effect made inside a multi-candidate dispatch arm (or a
//! multi-target SwitchInt arm), which is not blessed: the proof is demoted.
//! The safe twin records the same reason, a known-red false failure until a
//! guarded write-out (Phase 1) exists. The other rows are regression guards
//! for the other front doors; each matches on main and with Phase 0, except
//! `safe_dyn_reborrow_write`, which Phase 0 fails closed
//! (`walker_deref_read_after_write`: the second candidate's self-field map is
//! built after the first candidate's write).
//!
//! Lane scope: CHC only.
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options --harness-timeout=30s walker_phase0_front_doors_dual.rs

#[inline(never)]
fn sink<T>(_v: T) {}

static mut G: u8 = 0;
static mut H: u8 = 0;
static mut CNT: u8 = 0;

// ---- a two-candidate dyn dispatch, one candidate stores a static ----------
pub trait T {
    fn f(&self) -> u8;
}
pub struct A;
pub struct B;
impl T for A {
    fn f(&self) -> u8 {
        unsafe {
            G = 200;
        }
        0
    }
}
impl T for B {
    fn f(&self) -> u8 {
        0
    }
}

// Under B nothing writes G, so G == 0.
#[kani::proof]
fn bug_dispatch_store_unguarded() {
    let o: Box<dyn T> = if kani::any() { Box::new(A) } else { Box::new(B) };
    let _ = o.f();
    assert!(unsafe { G } == 200);
}

#[kani::proof]
fn safe_dispatch_store_unguarded() {
    let o: Box<dyn T> = if kani::any() { Box::new(A) } else { Box::new(B) };
    let _ = o.f();
    assert!(unsafe { G } == 200 || unsafe { G } == 0);
}

// ---- a fn_inline body stores a static on one arm --------------------------
#[inline(never)]
fn set_if(c: bool) {
    if c {
        unsafe {
            H = 7;
        }
    }
}

#[kani::proof]
fn bug_fninline_arm_store() {
    set_if(kani::any());
    assert!(unsafe { H } == 7);
}

#[kani::proof]
fn safe_fninline_arm_store() {
    set_if(kani::any());
    assert!(unsafe { H } == 7 || unsafe { H } == 0);
}

// ---- an FnMut closure writes its capture, then reads it -------------------
#[kani::proof]
fn bug_closure_capture_write_read() {
    let mut x: u8 = 0;
    let mut c = |v: u8| {
        x = v;
        x
    };
    let r = c(255);
    assert!(r == 0);
}

#[kani::proof]
fn safe_closure_capture_write_read() {
    let mut x: u8 = 0;
    let mut c = |v: u8| {
        x = v;
        x
    };
    let r = c(255);
    assert!(r == 255);
}

// ---- a Drop body writes a static, then reads it ---------------------------
pub struct D;
impl Drop for D {
    fn drop(&mut self) {
        unsafe {
            CNT = 255;
            let v = CNT;
            sink(v.unchecked_add(1));
        }
    }
}

#[kani::proof]
fn bug_drop_static_write_read() {
    let d = D;
    drop(d);
}

// ---- `let q = &mut *p; q.f = 1` through dyn -------------------------------
pub struct P {
    pub f: u8,
    pub g: u8,
}
pub trait Wq {
    fn w(&self, p: &mut P);
}
pub struct QA;
pub struct QB;
impl Wq for QA {
    fn w(&self, p: &mut P) {
        let q = &mut *p;
        q.f = 1;
    }
}
impl Wq for QB {
    fn w(&self, p: &mut P) {
        let q = &mut *p;
        q.f = 1;
    }
}

#[kani::proof]
fn bug_dyn_reborrow_write() {
    let mut p = P { f: 0, g: 0 };
    let o: Box<dyn Wq> = if kani::any() { Box::new(QA) } else { Box::new(QB) };
    o.w(&mut p);
    assert!(p.f == 0);
}

#[kani::proof]
fn safe_dyn_reborrow_write() {
    let mut p = P { f: 0, g: 0 };
    let o: Box<dyn Wq> = if kani::any() { Box::new(QA) } else { Box::new(QB) };
    o.w(&mut p);
    assert!(p.f == 1);
}

// ---- a fn_inline read of a memory-backed referent through `&u64` ----------
#[inline(never)]
fn read_it(x: &u64) -> u64 {
    *x
}

#[kani::proof]
fn bug_fninline_mem_ref_read() {
    let a: u64 = kani::any();
    let p = &a as *const u64;
    sink(p);
    let r = read_it(&a);
    assert!(r != a);
}

#[kani::proof]
fn safe_fninline_mem_ref_read() {
    let a: u64 = kani::any();
    let p = &a as *const u64;
    sink(p);
    let r = read_it(&a);
    assert!(r == a);
}
