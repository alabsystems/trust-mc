// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (missed-bug tripwire) -- an `unchecked_add` that overflows
//! only on a loop iteration PAST the CHC inline walker's replay budget.
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3; see the manifest entry):
//!   bug_overflow_after_budget_multi_impl       -> VERIFICATION:- FAILED  ('attempt to compute `unchecked_add` which would overflow')
//!   bug_overflow_after_budget_single_impl_box  -> VERIFICATION:- FAILED  (same check)
//!   bug_overflow_first_iteration_multi_impl    -> VERIFICATION:- FAILED  (same check; control)
//!   safe_loop_multi_impl                       -> VERIFICATION:- SUCCESSFUL
//!
//! MECHANISM (FIXED on fix/chc-walker-fail-closed, 2026-09-26). The walker
//! replays the constant-bound `while i < 10` loop with a per-header fuel of 5
//! (no declared unwind). Before the fix, the visit that found the fuel spent
//! jumped to the header SwitchInt's `otherwise` target without evaluating the
//! exit test -- for `while i < 10` that is the loop BODY -- then exceeded its
//! block-visit limit and bailed; the enclosing SwitchInt arm was replaced by
//! a fresh `__switchint_branch_overapprox` value (a blessed SoundHavoc reason)
//! and the arm's recorded checks were discarded with it. With `x <= 150` the
//! first five additions of 20 cannot overflow, so every check that survived
//! was valid and the harness verified SUCCESSFUL clean; iteration 6 and later
//! overflow whenever `x > 55`. Now the spent-fuel visit is the loop's last
//! pass (its exit test decides), and an iteration whose exit test folds to a
//! constant is refunded its visit, so all ten iterations replay exactly and
//! the bug rows FAIL Genuine on Kani's message. The first-iteration control
//! FAILS either way. `walker_loop_exit_test_dual.rs` guards the jump itself.
//! Promoted from the 2026-09-23 review probe r1_loop_exhaust.rs.
//!
//! FIXED: Rule D (decision REDS-FINAL) books the bailed arm fail-closed, and
//! decision TRUSTMC-OPEN-REDS replays a header whose exit condition folds to a
//! constant past its fuel along the branch the program takes, so every
//! iteration's check is kept and the safe row proves. A guessed exit that
//! leaves the loop ends in a failing check (walker_loop_fuel_exit_dual.rs).
//!
//! Lane scope: CHC only.
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options --harness-timeout=30s walker_loop_replay_dual.rs

/// Keeps its argument alive through rustc's MIR optimisations and is
/// obligation-free by inspection (see `unchecked_arith_walker_dual.rs`).
#[inline(never)]
fn sink<T>(_value: T) {}

pub trait Op {
    fn op(&self, x: u8) -> u8;
}
pub struct A;
pub struct B;
impl Op for A {
    fn op(&self, x: u8) -> u8 {
        let mut acc = x;
        let mut i: u8 = 0;
        while i < 10 {
            acc = unsafe { acc.unchecked_add(20) };
            i += 1;
        }
        acc
    }
}
impl Op for B {
    fn op(&self, x: u8) -> u8 {
        let mut acc = x;
        let mut i: u8 = 0;
        while i < 10 {
            acc = unsafe { acc.unchecked_add(20) };
            i += 1;
        }
        acc
    }
}

#[kani::proof]
fn bug_overflow_after_budget_multi_impl() {
    let x: u8 = kani::any();
    kani::assume(x <= 150);
    let obj: Box<dyn Op> = if kani::any() { Box::new(A) } else { Box::new(B) };
    sink(obj.op(x));
}

#[kani::proof]
fn bug_overflow_after_budget_single_impl_box() {
    let x: u8 = kani::any();
    kani::assume(x <= 150);
    let obj: Box<dyn Op> = Box::new(A);
    sink(obj.op(x));
}

#[kani::proof]
fn bug_overflow_first_iteration_multi_impl() {
    let x: u8 = kani::any();
    let obj: Box<dyn Op> = if kani::any() { Box::new(A) } else { Box::new(B) };
    sink(obj.op(x));
}

#[kani::proof]
fn safe_loop_multi_impl() {
    let x: u8 = kani::any();
    kani::assume(x <= 55);
    let obj: Box<dyn Op> = if kani::any() { Box::new(A) } else { Box::new(B) };
    sink(obj.op(x));
}
