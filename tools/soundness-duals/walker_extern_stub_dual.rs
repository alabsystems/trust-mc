// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (both directions) -- an `extern "C"` function stubbed with
//! `#[kani::stub]` and called from a body the CHC inline walker walks: a
//! direct call, and a call through a fn pointer to the extern item.
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3 with -Z stubbing,
//! measured 2026-09-27):
//!   bug_extern_stub_assert_multi -> VERIFICATION:- FAILED  ("extern stub assertion")
//!   safe_extern_stub_value_multi -> VERIFICATION:- SUCCESSFUL
//!   bug_extern_stub_value_multi  -> VERIFICATION:- FAILED  ("not 101")
//!   bug_extern_stub_fn_ptr_multi -> VERIFICATION:- FAILED  ("extern stub assertion")
//!   bug_extern_stub_harness_body -> VERIFICATION:- FAILED  ("extern stub assertion"; control)
//!
//! MECHANISM UNDER TEST. An extern original has no body, so Kani rewrites its
//! CALL SITES to the stub (`ExternFnStubPass`, now `CallSiteStubPass`). The
//! walker fetched callee bodies raw, where no call site is rewritten: the call
//! reached the extern item, whose fetch failed, and the call was havocked. On
//! main c22e1022e bug_extern_stub_assert_multi verified SUCCESSFUL clean (the
//! havoc was blessed) and safe_extern_stub_value_multi FAILED OverApproximation
//! (the havocked value is not odd). The first rounds of
//! fix/chc-walker-fail-closed caught the bug row only through the fail-closed
//! fetch and the stub-resolved callee scan. FIXED exactly in the package round
//! (item e): the walker's bodies come through `CalleeBody::callee_body`, which
//! applies the unit's call-site stub rewrites
//! (`kani_middle::transform::stub_aware_instance_body`), so the walk runs the
//! stub: every bug row FAILS Genuine and the safe row verifies.
//!
//! Lane scope: CHC only.
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options -Z stubbing --harness-timeout=30s walker_extern_stub_dual.rs

#[inline(never)]
fn sink<T>(_value: T) {}

pub struct Other;

extern "C" {
    fn ext_checked(x: u8) -> u8;
    fn ext_value(x: u8) -> u8;
}

pub fn ext_checked_stub(x: u8) -> u8 {
    assert!(x != 100, "extern stub assertion");
    x
}

pub fn ext_value_stub(x: u8) -> u8 {
    x | 1
}

// The stub's assertion, reached from a walked method.
pub trait TA {
    fn run(&self, a: u8) -> u8;
}
pub struct CA;
impl TA for CA {
    fn run(&self, a: u8) -> u8 {
        unsafe { ext_checked(a) }
    }
}
impl TA for Other {
    fn run(&self, a: u8) -> u8 {
        a
    }
}

#[kani::proof]
#[kani::stub(ext_checked, ext_checked_stub)]
fn bug_extern_stub_assert_multi() {
    let a: u8 = kani::any();
    let o: Box<dyn TA> = if kani::any() { Box::new(CA) } else { Box::new(Other) };
    sink(o.run(a));
}

// The stub's value feeds a check in the walked method: exact only when the
// walker runs the stub.
pub trait TV {
    fn run(&self, a: u8) -> u8;
}
pub struct CV;
impl TV for CV {
    fn run(&self, a: u8) -> u8 {
        let r = unsafe { ext_value(a) };
        assert!(r & 1 == 1, "odd");
        r
    }
}
impl TV for Other {
    fn run(&self, a: u8) -> u8 {
        a
    }
}

#[kani::proof]
#[kani::stub(ext_value, ext_value_stub)]
fn safe_extern_stub_value_multi() {
    let a: u8 = kani::any();
    let o: Box<dyn TV> = if kani::any() { Box::new(CV) } else { Box::new(Other) };
    sink(o.run(a));
}

pub trait TWr {
    fn run(&self, a: u8) -> u8;
}
pub struct CWr;
impl TWr for CWr {
    fn run(&self, a: u8) -> u8 {
        let r = unsafe { ext_value(a) };
        assert!(r != 101, "not 101");
        r
    }
}
impl TWr for Other {
    fn run(&self, a: u8) -> u8 {
        a
    }
}

#[kani::proof]
#[kani::stub(ext_value, ext_value_stub)]
fn bug_extern_stub_value_multi() {
    let a: u8 = kani::any();
    let o: Box<dyn TWr> = if kani::any() { Box::new(CWr) } else { Box::new(Other) };
    sink(o.run(a));
}

// Through a fn pointer to the extern item, inside the walked method.
pub trait TP {
    fn run(&self, a: u8) -> u8;
}
pub struct CP;
impl TP for CP {
    fn run(&self, a: u8) -> u8 {
        let f: unsafe extern "C" fn(u8) -> u8 = ext_checked;
        unsafe { f(a) }
    }
}
impl TP for Other {
    fn run(&self, a: u8) -> u8 {
        a
    }
}

#[kani::proof]
#[kani::stub(ext_checked, ext_checked_stub)]
fn bug_extern_stub_fn_ptr_multi() {
    let a: u8 = kani::any();
    let o: Box<dyn TP> = if kani::any() { Box::new(CP) } else { Box::new(Other) };
    sink(o.run(a));
}

// Control: the harness body.
#[kani::proof]
#[kani::stub(ext_checked, ext_checked_stub)]
fn bug_extern_stub_harness_body() {
    let a: u8 = kani::any();
    sink(unsafe { ext_checked(a) });
}
