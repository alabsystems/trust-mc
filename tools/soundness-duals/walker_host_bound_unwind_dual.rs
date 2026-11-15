// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (both directions) -- Kani's unwinding assertion on a walked
//! obligation-free loop under a declared unwind, and the host's own bound on
//! its trip count (fix/chc-walker-fail-closed, repair round 3, walker
//! fail-closed review 6 round 3 finding 5, repair round 1's finding 6: the
//! review's `rv_loops.rs::l_free_sym_safe`).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, measured 2026-09-28):
//!   l_free_sym_safe                  -> VERIFICATION:- SUCCESSFUL
//!   l_free_sym_past_unwind_bug       -> VERIFICATION:- FAILED  ('unwinding assertion loop 0')
//!   l_free_sym_branch_assume_bug     -> VERIFICATION:- FAILED  ('unwinding assertion loop 0')
//!   l_free_sym_direct_safe           -> VERIFICATION:- SUCCESSFUL
//!
//! MECHANISM UNDER TEST. Under a declared `#[kani::unwind(U)]` the walker
//! replays a loop pass for pass and states Kani's unwinding assertion where a
//! path needs pass `U + 1`. That check was a second property of its own and
//! split the harness's solve budget: `l_free_sym_safe` (`n <= 10` under
//! `unwind(12)`) proved the unwinding row in 9 s and left the assertion row
//! too little time, a SolverError after 98 s every time, where main proves it
//! in 13 s. An unwinding check that the host's dominating assumptions on the
//! call's arguments make unviolable (decided exactly, in process, by
//! `¬check ∧ bounds` UNSAT) is no longer emitted
//! (`codegen_call_virtual_inline/host_bound_discharge.rs`); a bound that
//! allows pass `U + 1` (`past`), or an assumption on one branch only
//! (`branch`), keeps the check.
#[inline(never)]
fn sink<T>(_v: T) {}

pub struct Other;

pub trait TFree { fn run(&self, x: u8, n: u8) -> u8; }
pub struct CFree;
impl TFree for CFree {
    fn run(&self, x: u8, n: u8) -> u8 {
        let mut acc = x;
        let mut i: u8 = 0;
        while i < n {
            acc = acc.wrapping_add(1);
            i = i.wrapping_add(1);
        }
        acc
    }
}
impl TFree for Other { fn run(&self, x: u8, n: u8) -> u8 { x.wrapping_add(n) } }

#[kani::proof]
#[kani::unwind(12)]
fn l_free_sym_safe() {
    let x: u8 = kani::any();
    let n: u8 = kani::any();
    kani::assume(n <= 10);
    let o: Box<dyn TFree> = if kani::any() { Box::new(CFree) } else { Box::new(Other) };
    assert!(o.run(x, n) == x.wrapping_add(n));
}

#[kani::proof]
#[kani::unwind(12)]
fn l_free_sym_past_unwind_bug() {
    let x: u8 = kani::any();
    let n: u8 = kani::any();
    kani::assume(n <= 12);
    let o: Box<dyn TFree> = if kani::any() { Box::new(CFree) } else { Box::new(Other) };
    sink(o.run(x, n));
}

#[kani::proof]
#[kani::unwind(12)]
fn l_free_sym_branch_assume_bug() {
    let x: u8 = kani::any();
    let n: u8 = kani::any();
    if kani::any() {
        kani::assume(n <= 10);
    } else {
        kani::assume(n <= 12);
    }
    let o: Box<dyn TFree> = if kani::any() { Box::new(CFree) } else { Box::new(Other) };
    sink(o.run(x, n));
}

#[inline(never)]
fn free_loop(x: u8, n: u8) -> u8 {
    let mut acc = x;
    let mut i: u8 = 0;
    while i < n {
        acc = acc.wrapping_add(1);
        i = i.wrapping_add(1);
    }
    acc
}

#[kani::proof]
#[kani::unwind(12)]
fn l_free_sym_direct_safe() {
    let x: u8 = kani::any();
    let n: u8 = kani::any();
    kani::assume(n <= 10);
    assert!(free_loop(x, n) == x.wrapping_add(n));
}
