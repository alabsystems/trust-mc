// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (both directions) -- `#[kani::stub]` on a function the CHC
//! inline walker reaches: walked directly, or in an arm it abandons.
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3 with -Z stubbing,
//! measured 2026-09-27):
//!   bug_stub_direct_multi        -> VERIFICATION:- FAILED  ('assertion failed: v != 100')
//!   bug_stub_region_multi        -> VERIFICATION:- FAILED  (same)
//!   bug_stub_bailed_arm_multi    -> VERIFICATION:- FAILED  (same)
//!   bug_stub_harness_body        -> VERIFICATION:- FAILED  (same; control, statement path)
//!   safe_stub_removes_panic_multi -> VERIFICATION:- SUCCESSFUL
//!
//! MECHANISM UNDER TEST. `FnStubPass` replaces a stubbed function's BODY with
//! the stub's. The walker fetched callee bodies raw (`walker_transformed_body`
//! opts in contract items only), so it walked `clean`'s own obligation-free
//! body where the unit runs `panicking`, and the new region scan and callee
//! scans of fix/chc-walker-fail-closed used an empty stub map, so an abandoned
//! region calling the stubbed `ident` read as obligation-free. The direct and
//! region bug rows verified SUCCESSFUL clean on the a15de6272 base bundle and
//! on the first cut of the branch. FIXED in the review round: the walker
//! fetches a stubbed instance through the transformer (the stub's body), and
//! every scan resolves through the unit's stub map
//! (`kani_middle::transform::walker_stub_map`). The safe row is the other
//! direction: a stub that REMOVES the panic must prove.
//! Promoted from the review probes rv_stub.rs and rv_arms3.rs.
//!
//! Lane scope: CHC only.
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options -Z stubbing --harness-timeout=30s walker_stub_dual.rs

/// Keeps its argument alive through rustc's MIR optimisations and is
/// obligation-free by inspection (see `unchecked_arith_walker_dual.rs`).
#[inline(never)]
fn sink<T>(_value: T) {}

#[inline(never)]
fn clean(v: u8) -> u8 {
    v.wrapping_add(1)
}

#[inline(never)]
fn ident(v: u8) -> u8 {
    v
}

#[inline(never)]
fn panicking(v: u8) -> u8 {
    assert!(v != 100);
    v
}

pub struct Other;

// A walked `dyn` method calls the stubbed function directly.
pub trait TDirect {
    fn run(&self, a: u8) -> u8;
}
pub struct CDirect;
impl TDirect for CDirect {
    fn run(&self, a: u8) -> u8 {
        clean(a)
    }
}
impl TDirect for Other {
    fn run(&self, a: u8) -> u8 {
        a
    }
}

#[kani::proof]
#[kani::stub(clean, panicking)]
fn bug_stub_direct_multi() {
    let a: u8 = kani::any();
    let o: Box<dyn TDirect> = if kani::any() { Box::new(CDirect) } else { Box::new(Other) };
    sink(o.run(a));
}

// The stubbed `ident` is the only call in an arm the walker abandons (the
// element is read before the switch).
pub trait TRegion {
    fn run(&self, a: u8, i: u8) -> u8;
}
pub struct CRegion;
impl TRegion for CRegion {
    fn run(&self, a: u8, i: u8) -> u8 {
        let arr = [a, 1, 2, 3];
        let v = arr[(i % 4) as usize];
        if a > 10 {
            if v > 50 { ident(v) } else { v }
        } else {
            a
        }
    }
}
impl TRegion for Other {
    fn run(&self, a: u8, _i: u8) -> u8 {
        a
    }
}

#[kani::proof]
#[kani::stub(ident, panicking)]
fn bug_stub_region_multi() {
    let a: u8 = kani::any();
    let i: u8 = kani::any();
    let o: Box<dyn TRegion> = if kani::any() { Box::new(CRegion) } else { Box::new(Other) };
    sink(o.run(a, i));
}

// The stubbed `clean` in an arm the walker abandons, after the element read.
pub trait TArm {
    fn run(&self, a: u8, i: u8) -> u8;
}
pub struct CArm;
impl TArm for CArm {
    fn run(&self, a: u8, i: u8) -> u8 {
        if a > 10 {
            let arr = [a, 1, 2, 3];
            let v = arr[(i % 4) as usize];
            if v > 50 { clean(v) } else { v }
        } else {
            a
        }
    }
}
impl TArm for Other {
    fn run(&self, a: u8, _i: u8) -> u8 {
        a
    }
}

#[kani::proof]
#[kani::stub(clean, panicking)]
fn bug_stub_bailed_arm_multi() {
    let a: u8 = kani::any();
    let i: u8 = kani::any();
    let o: Box<dyn TArm> = if kani::any() { Box::new(CArm) } else { Box::new(Other) };
    sink(o.run(a, i));
}

// Control: the stub on a call in the harness body itself.
#[kani::proof]
#[kani::stub(clean, panicking)]
fn bug_stub_harness_body() {
    let a: u8 = kani::any();
    sink(clean(a));
}

// The other direction: a walked method calls `panicking`, stubbed to the
// obligation-free `clean`.
pub trait TRemove {
    fn run(&self, a: u8) -> u8;
}
pub struct CRemove;
impl TRemove for CRemove {
    fn run(&self, a: u8) -> u8 {
        panicking(a)
    }
}
impl TRemove for Other {
    fn run(&self, a: u8) -> u8 {
        a
    }
}

#[kani::proof]
#[kani::stub(panicking, clean)]
fn safe_stub_removes_panic_multi() {
    let a: u8 = kani::any();
    let o: Box<dyn TRemove> = if kani::any() { Box::new(CRemove) } else { Box::new(Other) };
    sink(o.run(a));
}
