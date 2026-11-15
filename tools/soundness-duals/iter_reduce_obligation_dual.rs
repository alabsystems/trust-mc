// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (both directions) -- the statement path's iterator
//! reduction models (`Iterator::fold`, `try_fold`, `sum`), which walk the
//! closure with the inline walker or not at all.
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, measured 2026-09-27):
//!   bug_fold_large_closure       -> VERIFICATION:- FAILED  ("fold closure assertion")
//!   bug_fold_closure_assert      -> VERIFICATION:- FAILED  ("fold closure assertion")
//!   safe_fold_closure            -> VERIFICATION:- SUCCESSFUL
//!   bug_fold_past_replay_bound   -> VERIFICATION:- FAILED  ("fold bound assertion")
//!   bug_try_fold_closure_assert  -> VERIFICATION:- FAILED  ("try_fold closure assertion")
//!   bug_sum_overflow             -> VERIFICATION:- FAILED  (attempt to add with overflow)
//!   safe_sum_no_overflow         -> VERIFICATION:- SUCCESSFUL
//!   bug_sum_past_replay_bound    -> VERIFICATION:- FAILED  (attempt to add with overflow)
//!
//! Repair round 1 rows (walker fail-closed review 6, finding 7), the same
//! Kani, measured 2026-09-28:
//!   safe_sum_past_replay_bound   -> VERIFICATION:- SUCCESSFUL
//!   safe_fold_past_replay_bound  -> VERIFICATION:- SUCCESSFUL
//!   bug_walked_fold              -> VERIFICATION:- FAILED  (attempt to add with overflow)
//!   safe_walked_fold             -> VERIFICATION:- SUCCESSFUL
//!
//! The chain over an array of constant length `N` is now replayed to `N`
//! steps (up to the cap of 32, `fold_precise.rs` `iterator_static_len`), so
//! a step past the old bound of 8 is exact. On main c22e1022e the sum row
//! proves only because main drops the step's check, and the fold row FAILS
//! uncertified; the review measured the sum shape (`f3_sum_ninth_safe`)
//! FAILED uncertified on the round-2 bundle 5d66fe32. The `walked` rows fold
//! inside a body the walker walks, where `Iterator::fold` is a std callee the
//! walker havocs: its closure's check makes the havoc a sighting
//! (`nested_call_dropped_obligation`), so the bug row FAILS where main missed
//! it, and the safe row FAILS uncertified, a known-red precision cost (the
//! walker has no reduction model; the statement path's is not reachable
//! from a walked body).
//!
//! MECHANISM UNDER TEST (package round of fix/chc-walker-fail-closed, item c).
//! `fold` replays its closure per element with the inline walker, up to a
//! replay bound (8 by default); everything it does not replay is a fresh
//! value booked on the non-demoting aggregate-gap channel. That is sound for
//! the VALUE and drops the step's obligations: a closure the walker could not
//! walk (`bug_fold_large_closure`), a `try_fold` closure, which was never
//! walked, and every `sum` step, which added with `bvadd` and checked no
//! overflow at all (`bug_sum_overflow`), and the steps past the bound
//! (`bug_sum_past_replay_bound`). On main c22e1022e those four bug rows
//! verified SUCCESSFUL clean. FIXED: a replayed step's obligations are
//! emitted under its range condition (the walked closure's checks; `sum`'s
//! overflow, Kani's "attempt to add with overflow"), and a step that can
//! carry an obligation but is not replayed records an uncertified reach check
//! under the condition that it runs (`iter_reduce_step_uncertified`, the
//! walker's argument: fails wherever such a step can run, never certified).
//! The safe rows keep their proofs.
//!
//! Lane scope: CHC only.
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options --harness-timeout=30s iter_reduce_obligation_dual.rs

#[inline(never)]
fn sink<T>(_value: T) {}

#[inline(never)] fn g1(x: u8) -> u8 { x ^ 1 }
#[inline(never)] fn g2(x: u8) -> u8 { x ^ 2 }
#[inline(never)] fn g3(x: u8) -> u8 { x ^ 3 }
#[inline(never)] fn g4(x: u8) -> u8 { x ^ 4 }
#[inline(never)] fn g5(x: u8) -> u8 { x ^ 5 }
#[inline(never)] fn g6(x: u8) -> u8 { x ^ 6 }
#[inline(never)] fn g7(x: u8) -> u8 { x ^ 7 }
#[inline(never)] fn g8(x: u8) -> u8 { x ^ 8 }
#[inline(never)] fn g9(x: u8) -> u8 { x ^ 9 }
#[inline(never)] fn g10(x: u8) -> u8 { x ^ 10 }
#[inline(never)] fn g11(x: u8) -> u8 { x ^ 11 }
#[inline(never)] fn g12(x: u8) -> u8 { x ^ 12 }
#[inline(never)] fn g13(x: u8) -> u8 { x ^ 13 }
#[inline(never)] fn g14(x: u8) -> u8 { x ^ 14 }
#[inline(never)] fn g15(x: u8) -> u8 { x ^ 15 }
#[inline(never)] fn g16(x: u8) -> u8 { x ^ 16 }
#[inline(never)] fn g17(x: u8) -> u8 { x ^ 17 }
#[inline(never)] fn g18(x: u8) -> u8 { x ^ 18 }
#[inline(never)] fn g19(x: u8) -> u8 { x ^ 19 }
#[inline(never)] fn g20(x: u8) -> u8 { x ^ 20 }
#[inline(never)] fn g21(x: u8) -> u8 { x ^ 21 }
#[inline(never)] fn g22(x: u8) -> u8 { x ^ 22 }
#[inline(never)] fn g23(x: u8) -> u8 { x ^ 23 }
#[inline(never)] fn g24(x: u8) -> u8 { x ^ 24 }
#[inline(never)] fn g25(x: u8) -> u8 { x ^ 25 }
#[inline(never)] fn g26(x: u8) -> u8 { x ^ 26 }
#[inline(never)] fn g27(x: u8) -> u8 { x ^ 27 }
#[inline(never)] fn g28(x: u8) -> u8 { x ^ 28 }
#[inline(never)] fn g29(x: u8) -> u8 { x ^ 29 }
#[inline(never)] fn g30(x: u8) -> u8 { x ^ 30 }
#[inline(never)] fn g31(x: u8) -> u8 { x ^ 31 }
#[inline(never)] fn g32(x: u8) -> u8 { x ^ 32 }
#[inline(never)] fn g33(x: u8) -> u8 { x ^ 33 }
#[inline(never)] fn g34(x: u8) -> u8 { x ^ 34 }
#[inline(never)] fn g35(x: u8) -> u8 { x ^ 35 }
#[inline(never)] fn g36(x: u8) -> u8 { x ^ 36 }
#[inline(never)] fn g37(x: u8) -> u8 { x ^ 37 }
#[inline(never)] fn g38(x: u8) -> u8 { x ^ 38 }
#[inline(never)] fn g39(x: u8) -> u8 { x ^ 39 }
#[inline(never)] fn g40(x: u8) -> u8 { x ^ 40 }

// The closure body itself is too large for the walker.
#[kani::proof]
fn bug_fold_large_closure() {
    let a: u8 = kani::any();
    let v = [a, 1, 2];
    let s = v.iter().fold(0u8, |acc, &x| {
        assert!(x != 100, "fold closure assertion");
        let x = x;
        let x = g1(x);
        let x = g2(x);
        let x = g3(x);
        let x = g4(x);
        let x = g5(x);
        let x = g6(x);
        let x = g7(x);
        let x = g8(x);
        let x = g9(x);
        let x = g10(x);
        let x = g11(x);
        let x = g12(x);
        let x = g13(x);
        let x = g14(x);
        let x = g15(x);
        let x = g16(x);
        let x = g17(x);
        let x = g18(x);
        let x = g19(x);
        let x = g20(x);
        let x = g21(x);
        let x = g22(x);
        let x = g23(x);
        let x = g24(x);
        let x = g25(x);
        let x = g26(x);
        let x = g27(x);
        let x = g28(x);
        let x = g29(x);
        let x = g30(x);
        let x = g31(x);
        let x = g32(x);
        let x = g33(x);
        let x = g34(x);
        let x = g35(x);
        let x = g36(x);
        let x = g37(x);
        let x = g38(x);
        let x = g39(x);
        let x = g40(x);
        acc ^ x
    });
    sink(s);
}

#[kani::proof]
fn bug_fold_closure_assert() {
    let a: u8 = kani::any();
    let v = [a, 1u8];
    let s = v.iter().fold(0u8, |acc, &x| {
        assert!(x != 100, "fold closure assertion");
        acc ^ x
    });
    sink(s);
}

#[kani::proof]
fn safe_fold_closure() {
    let a: u8 = kani::any();
    let v = [a, 1u8];
    let s = v.iter().fold(0u8, |acc, &x| acc ^ x);
    assert!(s == a ^ 1);
}

// Past the replay bound (8 by default), the tenth element fails.
#[kani::proof]
fn bug_fold_past_replay_bound() {
    let a: u8 = kani::any();
    let v = [0u8, 1, 2, 3, 4, 5, 6, 7, 8, a];
    let s = v.iter().fold(0u8, |acc, &x| {
        assert!(x != 100, "fold bound assertion");
        acc ^ x
    });
    sink(s);
}

#[kani::proof]
fn bug_try_fold_closure_assert() {
    let a: u8 = kani::any();
    let v = [a, 1u8];
    let r: Option<u8> = v.iter().try_fold(0u8, |acc, &x| {
        assert!(x != 100, "try_fold closure assertion");
        Some(acc ^ x)
    });
    sink(r);
}

#[kani::proof]
fn bug_sum_overflow() {
    let a: u8 = kani::any();
    let v = [a, 200u8];
    let s: u8 = v.iter().sum();
    sink(s);
}

#[kani::proof]
fn safe_sum_no_overflow() {
    let a: u8 = kani::any();
    kani::assume(a <= 55);
    let v = [a, 200u8];
    let s: u8 = v.iter().sum();
    assert!(s >= 200);
}

#[kani::proof]
fn bug_sum_past_replay_bound() {
    let a: u8 = kani::any();
    let v = [0u8, 0, 0, 0, 0, 0, 0, 0, 0, a, 200];
    let s: u8 = v.iter().sum();
    sink(s);
}

// Repair round 1 (review 6, finding 7): steps past the old replay bound of
// 8 that cannot fail, and a fold inside a walked body.
#[kani::proof]
fn safe_sum_past_replay_bound() {
    let mut a = [0u8; 9];
    a[8] = kani::any();
    kani::assume(a[8] < 50);
    a[0] = 200;
    sink(a.iter().sum::<u8>());
}
#[kani::proof]
fn safe_fold_past_replay_bound() {
    let a: u8 = kani::any();
    kani::assume(a != 100);
    let v = [0u8, 1, 2, 3, 4, 5, 6, 7, 8, a];
    let s = v.iter().fold(0u8, |acc, &x| {
        assert!(x != 100, "fold bound assertion");
        acc ^ x
    });
    sink(s);
}
pub trait Red { fn r(&self, a: u8) -> u8; }
pub struct RedOther;
impl Red for RedOther { fn r(&self, a: u8) -> u8 { a } }
pub struct RedFold;
impl Red for RedFold {
    fn r(&self, a: u8) -> u8 {
        let arr = [a, 200, 3];
        arr.iter().fold(0u8, |acc, x| acc + x)
    }
}
#[kani::proof]
fn bug_walked_fold() {
    let a: u8 = kani::any();
    let o: Box<dyn Red> = if kani::any() { Box::new(RedFold) } else { Box::new(RedOther) };
    sink(o.r(a));
}
#[kani::proof]
fn safe_walked_fold() {
    let a: u8 = kani::any();
    kani::assume(a < 50);
    let o: Box<dyn Red> = if kani::any() { Box::new(RedFold) } else { Box::new(RedOther) };
    sink(o.r(a));
}
