// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (missed-bug tripwire) -- obligations inside a SwitchInt arm
//! the CHC inline walker cannot finish (Mechanisms C and D).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3; see the manifest entry):
//!   bug_bailed_arm_multi_impl                   -> VERIFICATION:- FAILED  ('assertion failed: v != 100')
//!   bug_bailed_arm_single_impl_box              -> VERIFICATION:- FAILED  (same check)
//!   safe_bailed_arm_single_impl_box             -> VERIFICATION:- SUCCESSFUL
//!   bug_unreachable_unchecked_multi_impl        -> VERIFICATION:- FAILED  ('unreachable code')
//!   bug_unreachable_unchecked_single_impl_box   -> VERIFICATION:- FAILED  (same check)
//!   safe_unreachable_unchecked_single_impl_box  -> VERIFICATION:- SUCCESSFUL
//!   bug_unreachable_unchecked_direct            -> VERIFICATION:- FAILED  (control)
//!
//! MECHANISMS (C and D of the 2026-09-23 walker investigation, both FIXED on
//! fix/chc-walker-fail-closed, 2026-09-26):
//!  * C -- when the walker fails inside a SwitchInt arm, `switchint.rs` replaces
//!    that arm with a fresh `__switchint_branch_overapprox` value, recorded as a
//!    blessed SoundHavoc reason, and the arm's deferred checks were discarded
//!    with it: the `assert!(v != 100)` in the `a > 10` arm never reached the
//!    host (`bug_bailed_arm_*`). Now an arm whose abandoned region can carry
//!    an obligation is also recorded as a check that fails wherever the arm is
//!    taken, never certified, so those rows FAIL non-certified;
//!    `safe_bailed_arm_single_impl_box` pays the precision cost (known-red
//!    false-failure) until the walker builds the array exactly.
//!  * D -- a diverging call that is not panic machinery
//!    (`hint::unreachable_unchecked`) was an unsupported terminator in the
//!    walker (`terminator_exec.rs`), so its arm failed and fell into C
//!    (`bug_unreachable_unchecked_*`). FIXED on fix/chc-walker-fail-closed
//!    (2026-09-26): reaching it is Kani's "unreachable code" failure, recorded
//!    exactly, so those rows FAIL Genuine.
//!
//! FIXED: Rule D (decision REDS-FINAL) books both mechanisms fail-closed, and
//! decision TRUSTMC-OPEN-REDS walks them precisely: the arm's array literal and
//! symbolic index translate, and an arm reaching `unreachable_unchecked` is a
//! check arm (Kani's `unreachable code`). Both safe rows prove.
//!
//! Promoted from the blast-radius probe `p12_bailed_branch.rs`.
//!
//! Lane scope: CHC only.
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options --harness-timeout=30s walker_bailed_branch_dual.rs

/// Keeps its argument alive through rustc's MIR optimisations and is
/// obligation-free by inspection (see `unchecked_arith_walker_dual.rs`).
#[inline(never)]
fn sink<T>(_value: T) {}

pub trait Op {
    fn arm(&self, a: u8, i: u8) -> u8;
    fn unreach(&self, a: u8) -> u8;
}
pub struct ImplA;
pub struct ImplB;
impl Op for ImplA {
    fn arm(&self, a: u8, i: u8) -> u8 {
        if a > 10 {
            let arr = [a, 1, 2, 3];
            let v = arr[(i % 4) as usize];
            assert!(v != 100);
            v
        } else {
            a
        }
    }
    fn unreach(&self, a: u8) -> u8 {
        if a == 3 {
            unsafe { core::hint::unreachable_unchecked() }
        }
        a
    }
}
impl Op for ImplB {
    fn arm(&self, a: u8, i: u8) -> u8 {
        if a > 10 {
            let arr = [a, 4, 5, 6];
            let v = arr[(i % 4) as usize];
            assert!(v != 100);
            v
        } else {
            a
        }
    }
    fn unreach(&self, a: u8) -> u8 {
        if a == 3 {
            unsafe { core::hint::unreachable_unchecked() }
        }
        a
    }
}

#[kani::proof]
fn bug_bailed_arm_multi_impl() {
    let a: u8 = kani::any();
    let i: u8 = kani::any();
    let obj: Box<dyn Op> = if kani::any() { Box::new(ImplA) } else { Box::new(ImplB) };
    sink(obj.arm(a, i));
}

#[kani::proof]
fn bug_bailed_arm_single_impl_box() {
    let a: u8 = kani::any();
    let i: u8 = kani::any();
    let obj: Box<dyn Op> = Box::new(ImplA);
    sink(obj.arm(a, i));
}

#[kani::proof]
fn safe_bailed_arm_single_impl_box() {
    let a: u8 = kani::any();
    let i: u8 = kani::any();
    kani::assume(a != 100);
    let obj: Box<dyn Op> = Box::new(ImplA);
    sink(obj.arm(a, i));
}

#[kani::proof]
fn bug_unreachable_unchecked_multi_impl() {
    let a: u8 = kani::any();
    let obj: Box<dyn Op> = if kani::any() { Box::new(ImplA) } else { Box::new(ImplB) };
    sink(obj.unreach(a));
}

#[kani::proof]
fn bug_unreachable_unchecked_single_impl_box() {
    let a: u8 = kani::any();
    let obj: Box<dyn Op> = Box::new(ImplA);
    sink(obj.unreach(a));
}

#[kani::proof]
fn safe_unreachable_unchecked_single_impl_box() {
    let a: u8 = kani::any();
    kani::assume(a != 3);
    let obj: Box<dyn Op> = Box::new(ImplA);
    sink(obj.unreach(a));
}

#[kani::proof]
fn bug_unreachable_unchecked_direct() {
    let a: u8 = kani::any();
    if a == 3 {
        unsafe { core::hint::unreachable_unchecked() }
    }
    sink(a);
}
