// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (both directions) -- a loop the CHC walker replays under a
//! declared unwind bound above its old replay ceiling, in a body it walks
//! (fix/chc-walker-fail-closed, walker fail-closed repair round 5, review
//! finding 8; the review's probe `rc_unwind.rs`, promoted).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, measured 2026-10-01 to
//! 2026-10-02):
//!   d1_unwind20_past_bug            -> VERIFICATION:- FAILED  ('unwinding assertion loop 0')
//!   d2_unwind17_past_bug            -> VERIFICATION:- FAILED  ('unwinding assertion loop 0')
//!   d3_unwind30_within_safe         -> VERIFICATION:- SUCCESSFUL
//!   d4_unwind19_within_safe         -> VERIFICATION:- SUCCESSFUL
//!   d5_unwind19_past_bug            -> VERIFICATION:- FAILED  ('unwinding assertion loop 0')
//!   d6_nested_unwind3_safe          -> VERIFICATION:- SUCCESSFUL
//!   d7_nested_second_entry_past_bug -> VERIFICATION:- FAILED  ('unwinding assertion loop 0')
//!
//! MECHANISM UNDER TEST. Under a declared unwind bound the walker replays a
//! loop exactly as Kani unwinds it, and records the pass past the bound as
//! Kani's unwinding failure (package round 2 item b). Its replay stopped at
//! 17 passes (fuel 16, and the SwitchInt depth limit of 16 a `while` takes
//! one level of per pass), and the abandoned loop failed closed (repair
//! round 1), so `d3` (26 of 30 passes) and `d4` (19 of 19) were false
//! failures where main, which dropped the loop's unwinding assertion and
//! missed `d1`, `d2` and `d5`, proved them. The declared fuel ceiling is now
//! 32 and the depth limit follows the declared fuel (`loop_replay.rs`
//! `MAX_INLINE_DECLARED_UNWIND_FUEL`, `switchint_depth_limit`); a caller's
//! assumed bound still raises the replay only to 16 (`MAX_INLINE_RAISED_FUEL`).
//!
//! Lane scope: CHC (the walker is the CHC lane's).
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options --harness-timeout=30s walker_declared_replay_dual.rs

#[inline(never)]
fn sink<T>(_v: T) {}

pub struct Other;

// An obligation-free loop body (wrapping arithmetic only).
pub trait Spin { fn run(&self, n: u8) -> u8; }
pub struct W;
impl Spin for W {
    fn run(&self, n: u8) -> u8 {
        let mut acc: u8 = 0;
        let mut i: u8 = 0;
        while i < n {
            acc = acc.wrapping_add(i);
            i = i.wrapping_add(1);
        }
        acc
    }
}
impl Spin for Other { fn run(&self, n: u8) -> u8 { n } }

// unwind(20): n up to 40 needs 41 header passes; Kani fails the unwinding
// assertion for n >= 20.
#[kani::proof]
#[kani::unwind(20)]
fn d1_unwind20_past_bug() {
    let n: u8 = kani::any();
    kani::assume(n <= 40);
    let o: Box<dyn Spin> = if kani::any() { Box::new(W) } else { Box::new(Other) };
    sink(o.run(n));
}
// unwind(17): the exact range; n >= 17 fails the unwinding assertion.
#[kani::proof]
#[kani::unwind(17)]
fn d2_unwind17_past_bug() {
    let n: u8 = kani::any();
    kani::assume(n <= 40);
    let o: Box<dyn Spin> = if kani::any() { Box::new(W) } else { Box::new(Other) };
    sink(o.run(n));
}
// unwind(30), n <= 25: every path within the bound.
#[kani::proof]
#[kani::unwind(30)]
fn d3_unwind30_within_safe() {
    let n: u8 = kani::any();
    kani::assume(n <= 25);
    let o: Box<dyn Spin> = if kani::any() { Box::new(W) } else { Box::new(Other) };
    sink(o.run(n));
}
// unwind(19), n <= 18: the last in-bound path needs 19 passes (within Kani's
// bound, past the walker's 18-pass replay).
#[kani::proof]
#[kani::unwind(19)]
fn d4_unwind19_within_safe() {
    let n: u8 = kani::any();
    kani::assume(n <= 18);
    let o: Box<dyn Spin> = if kani::any() { Box::new(W) } else { Box::new(Other) };
    sink(o.run(n));
}
// unwind(19), n <= 19: n == 19 needs pass 20 -> Kani unwinding failure.
#[kani::proof]
#[kani::unwind(19)]
fn d5_unwind19_past_bug() {
    let n: u8 = kani::any();
    kani::assume(n <= 19);
    let o: Box<dyn Spin> = if kani::any() { Box::new(W) } else { Box::new(Other) };
    sink(o.run(n));
}

// Nested loops under unwind(3).
pub trait Nest { fn run(&self, n: u8, m: u8) -> u8; }
pub struct Nst;
impl Nest for Nst {
    fn run(&self, n: u8, m: u8) -> u8 {
        let mut acc: u8 = 0;
        let mut i: u8 = 0;
        while i < n {
            let mut j: u8 = 0;
            while j < m {
                acc = acc.wrapping_add(1);
                j = j.wrapping_add(1);
            }
            i = i.wrapping_add(1);
        }
        acc
    }
}
impl Nest for Other { fn run(&self, n: u8, _m: u8) -> u8 { n } }
#[kani::proof]
#[kani::unwind(3)]
fn d6_nested_unwind3_safe() {
    let n: u8 = kani::any();
    let m: u8 = kani::any();
    kani::assume(n <= 2 && m <= 2);
    let o: Box<dyn Nest> = if kani::any() { Box::new(Nst) } else { Box::new(Other) };
    sink(o.run(n, m));
}
// The same nest, inner count 3 on the second outer iteration only.
pub struct Nst2;
impl Nest for Nst2 {
    fn run(&self, n: u8, m: u8) -> u8 {
        let mut acc: u8 = 0;
        let mut i: u8 = 0;
        while i < n {
            let lim = if i == 1 { m } else { 1 };
            let mut j: u8 = 0;
            while j < lim {
                acc = acc.wrapping_add(1);
                j = j.wrapping_add(1);
            }
            i = i.wrapping_add(1);
        }
        acc
    }
}
#[kani::proof]
#[kani::unwind(3)]
fn d7_nested_second_entry_past_bug() {
    let n: u8 = kani::any();
    let m: u8 = kani::any();
    kani::assume(n <= 2 && m <= 3);
    let o: Box<dyn Nest> = if kani::any() { Box::new(Nst2) } else { Box::new(Other) };
    sink(o.run(n, m));
}
