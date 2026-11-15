// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL -- a loop in a dyn-dispatched method body that runs past the
//! CHC inline walker's replay fuel (5 visits per header, `loop_replay.rs`).
//!
//! Oracle (per harness; Rust semantics, confirmed by running the harness
//! bodies natively under Trust seal 9192 with every nondet input enumerated):
//!   bug_symbolic_bound_past_fuel      -> VERIFICATION:- FAILED  ('assertion failed: i != 7', n >= 8)
//!   bug_constant_bound_past_fuel      -> VERIFICATION:- FAILED  (same check, n = 12)
//!   bug_returns_count_past_fuel       -> VERIFICATION:- FAILED  ('assertion failed: obj.op(n) <= 5', n >= 6)
//!   safe_returns_count                -> VERIFICATION:- SUCCESSFUL
//!   safe_symbolic_bound_within_fuel   -> VERIFICATION:- SUCCESSFUL
//!   safe_constant_bound_past_fuel     -> VERIFICATION:- SUCCESSFUL
//!
//! WHY THIS FILE EXISTS. Found while landing the Rule D precision fixes
//! (decision TRUSTMC-OPEN-REDS in docs/DECISION_QUEUE.md). When a header's
//! fuel ran out, the walker took the SwitchInt's `otherwise` arm as the loop
//! exit and booked nothing. For `loop { if i >= n { break } .. }` that arm IS
//! the exit, so every iteration past the fifth was dropped silently and the
//! loop-carried locals kept the fifth iteration's values:
//! `bug_symbolic_bound_past_fuel`, `bug_constant_bound_past_fuel` and
//! `bug_returns_count_past_fuel` were PROVED, and `safe_returns_count` got a
//! counterexample certified Genuine (`op(n)` read as 5). Main ended a path past
//! the fuel in a check that fails whenever the path is reachable
//! (`walker_loop_fuel_truncated_check`), so `safe_returns_count` failed there.
//! The merged branch replays the loop to the caller's assumed bound instead
//! (`loop_replay.rs`, `raise_loop_fuel`): no iteration is dropped and the safe
//! rows prove. The replayed value of `safe_returns_count` is a 13-deep `ite`
//! chain over `n`, which ay `d80d17a90` needs about 5.5 minutes for, and in a
//! whole-file run the overrun starved the three bug rows into the driver's
//! watchdog (walker fail-closed review after the merge, finding 1;
//! `docs/ay-asks/2026-10-14-acyclic-8bit-ite-chain-takes-5-minutes-d80d17a90`).
//! The emit pipeline now names the chain's links with fresh variables, an exact
//! rewrite ay decides at once (trust-mc-core `chc_optimize_ite_chains.rs`), and
//! the file runs in about a second.
//!
//! Lane scope: CHC only (the walker is the CHC lane's).

/// Keeps its argument alive through rustc's MIR optimisations and is
/// obligation-free by inspection (see `unchecked_arith_walker_dual.rs`).
#[inline(never)]
fn sink<T>(_value: T) {}

pub trait Op {
    fn op(&self, n: u8) -> u8;
}
pub struct Breaks;
impl Op for Breaks {
    fn op(&self, n: u8) -> u8 {
        let mut i: u8 = 0;
        loop {
            if i >= n {
                break;
            }
            assert!(i != 7);
            i += 1;
        }
        i
    }
}
pub struct Counts;
impl Op for Counts {
    fn op(&self, n: u8) -> u8 {
        let mut i: u8 = 0;
        loop {
            if i >= n {
                break;
            }
            i += 1;
        }
        i
    }
}

#[kani::proof]
fn bug_symbolic_bound_past_fuel() {
    let n: u8 = kani::any();
    kani::assume(n <= 12);
    let obj: Box<dyn Op> = Box::new(Breaks);
    sink(obj.op(n));
}

#[kani::proof]
fn bug_constant_bound_past_fuel() {
    let obj: Box<dyn Op> = Box::new(Breaks);
    sink(obj.op(12));
}

#[kani::proof]
fn bug_returns_count_past_fuel() {
    let n: u8 = kani::any();
    kani::assume(n <= 12);
    let obj: Box<dyn Op> = Box::new(Counts);
    assert!(obj.op(n) <= 5);
}

#[kani::proof]
fn safe_returns_count() {
    let n: u8 = kani::any();
    kani::assume(n <= 12);
    let obj: Box<dyn Op> = Box::new(Counts);
    assert!(obj.op(n) == n);
}

#[kani::proof]
fn safe_symbolic_bound_within_fuel() {
    let n: u8 = kani::any();
    kani::assume(n <= 3);
    let obj: Box<dyn Op> = Box::new(Breaks);
    sink(obj.op(n));
}

#[kani::proof]
fn safe_constant_bound_past_fuel() {
    let obj: Box<dyn Op> = Box::new(Breaks);
    sink(obj.op(6));
}
