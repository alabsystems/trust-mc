// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (missed-bug tripwire) -- a MIR overflow `Assert` whose
//! condition the CHC inline walker cannot translate (Mechanism E).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3; see the manifest entry):
//!   bug_multi_impl        -> VERIFICATION:- FAILED  ('attempt to add with overflow')
//!   bug_single_impl_box   -> VERIFICATION:- FAILED  (same check)
//!   safe_single_impl_box  -> VERIFICATION:- SUCCESSFUL
//!   bug_direct_call       -> VERIFICATION:- FAILED  (same check; control)
//!   safe_direct_call      -> VERIFICATION:- SUCCESSFUL (control twin)
//!
//! MECHANISM (E of the 2026-09-23 walker investigation): `v + 200` reads `v`
//! from an array element the walker silently skipped, so the overflow `Assert`
//! condition is untranslatable. `execute_inline_assert` used to assume the
//! assertion passes (the "condition untranslatable, assuming pass (#4014)"
//! arm) while the method's RETURN value (`a`) still translated, so nothing
//! masked the loss. The BinOp is a checked `Add` (its overflow is the
//! `Assert`), so the walker's BinOp checks since `rvalue_ub.rs` do not touch
//! it. FIXED on fix/chc-walker-fail-closed (2026-09-26): an untranslatable
//! Assert is recorded as a check that fails wherever it is reached, never
//! certified (`uncertified_check.rs`); main closed it with Rule D's
//! fail-closed booking (decision REDS-FINAL), which the merge replaced with
//! this narrower check. The condition here translates now: the walker builds
//! the array literal and reads it at the symbolic index (package round 2
//! item c; decision TRUSTMC-OPEN-REDS on main), so the dyn bug rows fail on
//! Kani's message and the safe dyn row proves.
//!
//! Promoted from the blast-radius probe `p13_untranslatable_assert.rs`. The
//! direct-call pair (the same array read and `v + 200` in the harness body,
//! where the statement path translates the Assert) is the control that
//! localises the miss to the walker: it discriminates on both bundles (bug
//! FAILED, safe SUCCESSFUL), per the 2026-09-23 test review's rp_controls.rs.
//!
//! Lane scope: CHC only.
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options --harness-timeout=30s walker_untranslatable_assert_dual.rs

/// Keeps its argument alive through rustc's MIR optimisations and is
/// obligation-free by inspection (see `unchecked_arith_walker_dual.rs`).
#[inline(never)]
fn sink<T>(_value: T) {}

pub trait Op {
    fn op(&self, a: u8, i: u8) -> u8;
}
pub struct ImplA;
pub struct ImplB;
impl Op for ImplA {
    fn op(&self, a: u8, i: u8) -> u8 {
        let arr = [a, 1, 2, 3];
        let v = arr[(i % 4) as usize];
        sink(v + 200);
        a
    }
}
impl Op for ImplB {
    fn op(&self, a: u8, i: u8) -> u8 {
        let arr = [a, 4, 5, 6];
        let v = arr[(i % 4) as usize];
        sink(v + 200);
        a
    }
}

#[kani::proof]
fn bug_multi_impl() {
    let a: u8 = kani::any();
    let i: u8 = kani::any();
    let obj: Box<dyn Op> = if kani::any() { Box::new(ImplA) } else { Box::new(ImplB) };
    sink(obj.op(a, i));
}

#[kani::proof]
fn bug_single_impl_box() {
    let a: u8 = kani::any();
    let i: u8 = kani::any();
    let obj: Box<dyn Op> = Box::new(ImplA);
    sink(obj.op(a, i));
}

#[kani::proof]
fn safe_single_impl_box() {
    let a: u8 = kani::any();
    let i: u8 = kani::any();
    kani::assume(a < 50);
    let obj: Box<dyn Op> = Box::new(ImplA);
    sink(obj.op(a, i));
}

#[kani::proof]
fn bug_direct_call() {
    let a: u8 = kani::any();
    let i: u8 = kani::any();
    let arr = [a, 1, 2, 3];
    let v = arr[(i % 4) as usize];
    sink(v + 200);
}

#[kani::proof]
fn safe_direct_call() {
    let a: u8 = kani::any();
    let i: u8 = kani::any();
    kani::assume(a < 50);
    let arr = [a, 1, 2, 3];
    let v = arr[(i % 4) as usize];
    sink(v + 200);
}
