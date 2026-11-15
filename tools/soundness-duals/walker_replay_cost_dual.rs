// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! PRECISION DUAL -- walked loops whose state feeds its own update, under the
//! caller's `kani::assume(n < 20)` and under a declared unwind bound
//! (fix/chc-walker-fail-closed, repair round 1, walker fail-closed review 6
//! findings 5 and 6; the review's probes `rj_dep_safe20`, `rj_dep_scalar20`,
//! the region probe `g2_signed_rem_index_bug` and `l_free_sym_safe`,
//! promoted).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, measured 2026-09-28;
//! the four assume rows declare no bound and ran with --default-unwind 21):
//!   dep_table_safe               -> VERIFICATION:- SUCCESSFUL
//!   dep_scalar_safe              -> VERIFICATION:- SUCCESSFUL
//!   dep_signed_rem_index_bug     -> VERIFICATION:- FAILED  ('index out of bounds: the length is less than or equal to the given index')
//!   dep_obligation_safe          -> VERIFICATION:- SUCCESSFUL
//!   free_sym_unwind12_safe       -> VERIFICATION:- SUCCESSFUL
//!
//! MECHANISM UNDER TEST. Package round 2 raised the replay of every walked
//! loop under a host assume to 17 passes (`walker.rs`
//! `host_call_assumed_bound`). For a loop whose accumulator feeds its own
//! update more than once (through an index, `acc += table[acc % 4]`), the
//! written-out term doubles every pass: the walk finished, and compilation
//! then stalled (`dep_table_safe` and `dep_signed_rem_index_bug` hit a
//! CompileTimeout that took every harness of their file along, main proves
//! the first in about 10 s), or the solver gave up (`dep_scalar_safe`). The
//! raise now applies only where the abandoned region can carry an obligation
//! (elsewhere the arm past the replay is the sound value havoc), and a raised
//! walk whose terms written out as trees exceed 200,000 nodes is discarded
//! for the built-in replay. `dep_obligation_safe` is the cost of that
//! ceiling: its region carries a check that always holds (`j == n`), the
//! raised walk is too large, and the built-in replay's abandoned arm FAILS
//! uncertified, a known-red precision row (main proved it only because its
//! abandoned arm dropped the check).
//!
//! `free_sym_unwind12_safe` (finding 6): under `#[kani::unwind(12)]` the
//! walker records Kani's unwinding assertion exactly (package round 2 item
//! b), a second property. The per-harness budget of 30 s is then split: the
//! unwinding row proves in 9 s of 15, and the assertion row, which proves in
//! 12.6 s when given 110 s, is inconclusive at 20.3 s of 20.9, the solver's
//! schedule at that budget (measured 2026-09-28, ay 22db3bcc1; with
//! --harness-timeout=120s both rows prove in 23 s). Known-red, class unknown.
//!
//! Lane scope: CHC only.
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options --harness-timeout=30s walker_replay_cost_dual.rs

/// Keeps its argument alive through rustc's MIR optimisations.
#[inline(never)]
fn sink<T>(_v: T) {}

pub struct Other;
pub trait Run { fn run(&self, a: u8, n: u8) -> u8; }
impl Run for Other { fn run(&self, a: u8, _n: u8) -> u8 { a } }

pub struct Table;
impl Run for Table {
    fn run(&self, a: u8, n: u8) -> u8 {
        let table = [1u8, 2, 3, 4];
        let mut acc = a;
        let mut j: u8 = 0;
        while j < n {
            let k = (acc % 4) as usize;
            acc = acc.wrapping_add(table[k]);
            j = j.wrapping_add(1);
        }
        acc
    }
}
#[kani::proof]
fn dep_table_safe() {
    let a: u8 = kani::any();
    let n: u8 = kani::any();
    kani::assume(n < 20);
    let o: Box<dyn Run> = if kani::any() { Box::new(Table) } else { Box::new(Other) };
    sink(o.run(a, n));
}

pub trait RunS { fn run(&self, a: u8, n: u8) -> u8; }
impl RunS for Other { fn run(&self, a: u8, _n: u8) -> u8 { a } }
pub struct Scalar;
impl RunS for Scalar {
    fn run(&self, a: u8, n: u8) -> u8 {
        let mut acc = a;
        let mut j: u8 = 0;
        while j < n {
            let k = acc % 4;
            acc = acc.wrapping_add(k).wrapping_add(k >> 1);
            j = j.wrapping_add(1);
        }
        acc
    }
}
#[kani::proof]
fn dep_scalar_safe() {
    let a: u8 = kani::any();
    let n: u8 = kani::any();
    kani::assume(n < 20);
    let o: Box<dyn RunS> = if kani::any() { Box::new(Scalar) } else { Box::new(Other) };
    sink(o.run(a, n));
}

pub trait RunR { fn run(&self, a: u8, n: u8) -> u8; }
impl RunR for Other { fn run(&self, a: u8, _n: u8) -> u8 { a } }
pub struct SignedRem;
impl RunR for SignedRem {
    fn run(&self, a: u8, n: u8) -> u8 {
        let table = [1u8, 2, 3, 4];
        let mut acc = a;
        let mut j: u8 = 0;
        while j < n {
            let k = (acc as i8) % 4;
            acc = acc.wrapping_add(table[k as usize]);
            j = j.wrapping_add(1);
        }
        acc
    }
}
#[kani::proof]
fn dep_signed_rem_index_bug() {
    let a: u8 = kani::any();
    let n: u8 = kani::any();
    kani::assume(n < 20);
    let o: Box<dyn RunR> = if kani::any() { Box::new(SignedRem) } else { Box::new(Other) };
    sink(o.run(a, n));
}

pub trait RunO { fn run(&self, a: u8, n: u8) -> u8; }
impl RunO for Other { fn run(&self, a: u8, _n: u8) -> u8 { a } }
pub struct Obligation;
impl RunO for Obligation {
    fn run(&self, a: u8, n: u8) -> u8 {
        let table = [1u8, 2, 3, 4];
        let mut acc = a;
        let mut j: u8 = 0;
        while j < n {
            let k = (acc % 4) as usize;
            acc = acc.wrapping_add(table[k]);
            j = j.wrapping_add(1);
        }
        assert!(j == n);
        acc
    }
}
#[kani::proof]
fn dep_obligation_safe() {
    let a: u8 = kani::any();
    let n: u8 = kani::any();
    kani::assume(n < 20);
    let o: Box<dyn RunO> = if kani::any() { Box::new(Obligation) } else { Box::new(Other) };
    sink(o.run(a, n));
}

pub trait TFree { fn run(&self, x: u8, n: u8) -> u8; }
impl TFree for Other { fn run(&self, x: u8, n: u8) -> u8 { x.wrapping_add(n) } }
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
#[kani::proof]
#[kani::unwind(12)]
fn free_sym_unwind12_safe() {
    let x: u8 = kani::any();
    let n: u8 = kani::any();
    kani::assume(n <= 10);
    let o: Box<dyn TFree> = if kani::any() { Box::new(CFree) } else { Box::new(Other) };
    assert!(o.run(x, n) == x.wrapping_add(n));
}
