// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (both directions) -- `#[kani::stub]` on a standard-library
//! function that trust-mc models by the PATH its call site names (the
//! known-call table, `Option::unwrap`, the `mem::forget` no-op table), in the
//! harness body and in a body the CHC inline walker walks.
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3 with -Z stubbing,
//! measured 2026-09-27):
//!   bug_stub_wrapping_add_multi         -> VERIFICATION:- FAILED  ("stubbed wrapping_add")
//!   bug_stub_wrapping_add_harness_body  -> VERIFICATION:- FAILED  ("stubbed wrapping_add")
//!   bug_stub_count_ones_multi           -> VERIFICATION:- FAILED  ("stubbed count_ones")
//!   bug_stub_unwrap_multi               -> VERIFICATION:- FAILED  (stubbed unwrap)
//!   bug_stub_unwrap_harness_body        -> VERIFICATION:- FAILED  (stubbed unwrap)
//!   safe_stub_unwrap_total_multi        -> VERIFICATION:- SUCCESSFUL
//!   safe_stub_unwrap_total_harness_body -> VERIFICATION:- SUCCESSFUL
//!   bug_stub_forget_multi               -> VERIFICATION:- FAILED  (stubbed forget)
//!
//! MECHANISM UNDER TEST. `FnStubPass` replaces a stubbed function's BODY; the
//! call site keeps naming the original. Both CHC paths model these std
//! functions from the call site's path and never fetch the body, so they
//! modelled the original: on main c22e1022e every bug row verified SUCCESSFUL
//! clean and both safe rows FAILED [AY:CTREX_CAT:Genuine] (false certificates:
//! the model's `unwrap` panics on `None`, the stub returns a value). FIXED in
//! the package round of fix/chc-walker-fail-closed (item a):
//! `CallSiteStubPass` rewrites every call site and fn-item operand naming a
//! stubbed function (it did so only for extern stubs), and every body the
//! walker and the statement path fetch raw goes through `CalleeBody::
//! callee_body`, which applies the unit's stubs (`kani_middle::transform::
//! stub_aware_instance_body`). No path model sees a stubbed function any more.
//! The two panicking-stub `_multi` rows fail OverApproximation: the stub's
//! `panic!` lowers to `kani::panic`, which the walker records as an
//! unmodelled diverging call (certification only).
//!
//! Lane scope: CHC only (the BMC lane has no dyn dispatch for the `_multi`
//! rows).
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options -Z stubbing --harness-timeout=30s stub_modelled_std_dual.rs

#[inline(never)]
fn sink<T>(_value: T) {}

pub struct Other;

pub fn stub_wrapping_add(a: u8, b: u8) -> u8 {
    assert!(a != 100, "stubbed wrapping_add");
    a ^ b
}
pub fn stub_count_ones(a: u8) -> u32 {
    assert!(a != 100, "stubbed count_ones");
    0
}
pub fn stub_unwrap_panics<T>(_o: Option<T>) -> T {
    panic!("stubbed unwrap")
}
pub fn stub_unwrap_total<T>(o: Option<T>) -> T {
    match o {
        Some(v) => v,
        None => unsafe { core::mem::zeroed() },
    }
}
pub fn stub_forget<T>(_t: T) {
    panic!("stubbed forget")
}

// `u8::wrapping_add`: the known-call table.
pub trait TW {
    fn run(&self, a: u8) -> u8;
}
pub struct CW;
impl TW for CW {
    fn run(&self, a: u8) -> u8 {
        a.wrapping_add(1)
    }
}
impl TW for Other {
    fn run(&self, a: u8) -> u8 {
        a
    }
}

#[kani::proof]
#[kani::stub(u8::wrapping_add, stub_wrapping_add)]
fn bug_stub_wrapping_add_multi() {
    let a: u8 = kani::any();
    let o: Box<dyn TW> = if kani::any() { Box::new(CW) } else { Box::new(Other) };
    sink(o.run(a));
}

#[kani::proof]
#[kani::stub(u8::wrapping_add, stub_wrapping_add)]
fn bug_stub_wrapping_add_harness_body() {
    let a: u8 = kani::any();
    sink(a.wrapping_add(1));
}

// `u8::count_ones`: a bit intrinsic in the known-call table.
pub trait TC {
    fn run(&self, a: u8) -> u32;
}
pub struct CC;
impl TC for CC {
    fn run(&self, a: u8) -> u32 {
        a.count_ones()
    }
}
impl TC for Other {
    fn run(&self, a: u8) -> u32 {
        a as u32
    }
}

#[kani::proof]
#[kani::stub(u8::count_ones, stub_count_ones)]
fn bug_stub_count_ones_multi() {
    let a: u8 = kani::any();
    let o: Box<dyn TC> = if kani::any() { Box::new(CC) } else { Box::new(Other) };
    sink(o.run(a));
}

// `Option::unwrap`, stubbed to always panic.
pub trait TU {
    fn run(&self, a: u8) -> u8;
}
pub struct CU;
impl TU for CU {
    fn run(&self, a: u8) -> u8 {
        Some(a).unwrap()
    }
}
impl TU for Other {
    fn run(&self, a: u8) -> u8 {
        a
    }
}

#[kani::proof]
#[kani::stub(std::option::Option::unwrap, stub_unwrap_panics)]
fn bug_stub_unwrap_multi() {
    let a: u8 = kani::any();
    let o: Box<dyn TU> = if kani::any() { Box::new(CU) } else { Box::new(Other) };
    sink(o.run(a));
}

#[kani::proof]
#[kani::stub(std::option::Option::unwrap, stub_unwrap_panics)]
fn bug_stub_unwrap_harness_body() {
    let a: u8 = kani::any();
    sink(Some(a).unwrap());
}

// The other direction: `Option::unwrap` stubbed to a total function.
pub trait TS {
    fn run(&self, a: u8) -> u8;
}
pub struct CS;
impl TS for CS {
    fn run(&self, a: u8) -> u8 {
        let o = if a > 10 { Some(a) } else { None };
        o.unwrap()
    }
}
impl TS for Other {
    fn run(&self, a: u8) -> u8 {
        a
    }
}

#[kani::proof]
#[kani::stub(std::option::Option::unwrap, stub_unwrap_total)]
fn safe_stub_unwrap_total_multi() {
    let a: u8 = kani::any();
    let o: Box<dyn TS> = if kani::any() { Box::new(CS) } else { Box::new(Other) };
    sink(o.run(a));
}

#[kani::proof]
#[kani::stub(std::option::Option::unwrap, stub_unwrap_total)]
fn safe_stub_unwrap_total_harness_body() {
    let a: u8 = kani::any();
    let o = if a > 10 { Some(a) } else { None };
    sink(o.unwrap());
}

// `mem::forget`: the no-op table.
pub trait TF {
    fn run(&self, a: u8) -> u8;
}
pub struct CF;
impl TF for CF {
    fn run(&self, a: u8) -> u8 {
        core::mem::forget(a);
        a
    }
}
impl TF for Other {
    fn run(&self, a: u8) -> u8 {
        a
    }
}

#[kani::proof]
#[kani::stub(core::mem::forget, stub_forget)]
fn bug_stub_forget_multi() {
    let a: u8 = kani::any();
    let o: Box<dyn TF> = if kani::any() { Box::new(CF) } else { Box::new(Other) };
    sink(o.run(a));
}
