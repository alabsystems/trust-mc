// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (both directions) -- an arm whose only check is a bounds
//! check that always holds, over an array the walked body builds
//! (fix/chc-walker-fail-closed, package round 2 items a and c; the review's
//! probes `c2_free_region_safe` and `c2_std_free_region_safe`, promoted).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, measured 2026-09-27):
//!   c2_free_region_safe          -> VERIFICATION:- SUCCESSFUL
//!   c2_free_region_bug           -> VERIFICATION:- FAILED  ('attempt to add with overflow')
//!   c2_std_free_region_safe      -> VERIFICATION:- SUCCESSFUL
//!   c2_std_free_region_bug       -> VERIFICATION:- FAILED  ('called `Option::unwrap()` on a `None` value')
//!
//! MECHANISM UNDER TEST. The arm builds `[a, 1, 2, 3]` and reads it at
//! `i % 4`. The first round skipped the array aggregate, so the element read
//! was untranslatable, the arm was abandoned, and the region scan counted the
//! read's bounds check (and `saturating_add`, a safe std call) as an
//! obligation: both safe rows FAILED OverApproximation on the first round's
//! bundle c6ea55deb, known-red precision costs. The array is built exactly
//! now (item c), so the arm is walked and the read is exact; were it
//! abandoned, the region scan's interval analysis (item a) proves the
//! `i % 4 < 4` bounds check. The bug twins keep a check that can fail in the
//! same arm: `v + 250` overflows for `v = a > 50`, and `checked_add(3)`
//! unwraps `None` for `a >= 253`; both FAIL Genuine on the round-2 bundle.
//!
//! Lane scope: CHC only.
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options --harness-timeout=30s walker_free_region_dual.rs

/// Keeps its argument alive through rustc's MIR optimisations.
#[inline(never)]
fn sink<T>(_v: T) {}

pub struct Other;

pub trait TFree { fn run(&self, a: u8, i: u8) -> u8; }
pub struct CFree;
impl TFree for CFree {
    fn run(&self, a: u8, i: u8) -> u8 {
        if a > 10 {
            let arr = [a, 1, 2, 3];
            let v = arr[(i % 4) as usize];
            if v > 50 { v.wrapping_add(3) } else { v }
        } else {
            a
        }
    }
}
impl TFree for Other { fn run(&self, a: u8, _i: u8) -> u8 { a } }
#[kani::proof]
fn c2_free_region_safe() {
    let a: u8 = kani::any();
    let i: u8 = kani::any();
    let o: Box<dyn TFree> = if kani::any() { Box::new(CFree) } else { Box::new(Other) };
    sink(o.run(a, i));
}

pub trait TFreeBug { fn run(&self, a: u8, i: u8) -> u8; }
pub struct CFreeBug;
impl TFreeBug for CFreeBug {
    fn run(&self, a: u8, i: u8) -> u8 {
        if a > 10 {
            let arr = [a, 1, 2, 3];
            let v = arr[(i % 4) as usize];
            if v > 50 { v + 250 } else { v }
        } else {
            a
        }
    }
}
impl TFreeBug for Other { fn run(&self, a: u8, _i: u8) -> u8 { a } }
#[kani::proof]
fn c2_free_region_bug() {
    let a: u8 = kani::any();
    let i: u8 = kani::any();
    let o: Box<dyn TFreeBug> = if kani::any() { Box::new(CFreeBug) } else { Box::new(Other) };
    sink(o.run(a, i));
}

pub trait TStdFree { fn run(&self, a: u8, i: u8) -> u8; }
pub struct CStdFree;
impl TStdFree for CStdFree {
    fn run(&self, a: u8, i: u8) -> u8 {
        if a > 10 {
            let arr = [a, 1, 2, 3];
            let v = arr[(i % 4) as usize];
            if v > 50 { v.saturating_add(3).min(200) } else { v }
        } else {
            a
        }
    }
}
impl TStdFree for Other { fn run(&self, a: u8, _i: u8) -> u8 { a } }
#[kani::proof]
fn c2_std_free_region_safe() {
    let a: u8 = kani::any();
    let i: u8 = kani::any();
    let o: Box<dyn TStdFree> = if kani::any() { Box::new(CStdFree) } else { Box::new(Other) };
    sink(o.run(a, i));
}

pub trait TStdFreeBug { fn run(&self, a: u8, i: u8) -> u8; }
pub struct CStdFreeBug;
impl TStdFreeBug for CStdFreeBug {
    fn run(&self, a: u8, i: u8) -> u8 {
        if a > 10 {
            let arr = [a, 1, 2, 3];
            let v = arr[(i % 4) as usize];
            if v > 50 { v.checked_add(3).unwrap().min(200) } else { v }
        } else {
            a
        }
    }
}
impl TStdFreeBug for Other { fn run(&self, a: u8, _i: u8) -> u8 { a } }
#[kani::proof]
fn c2_std_free_region_bug() {
    let a: u8 = kani::any();
    let i: u8 = kani::any();
    let o: Box<dyn TStdFreeBug> = if kani::any() { Box::new(CStdFreeBug) } else { Box::new(Other) };
    sink(o.run(a, i));
}
