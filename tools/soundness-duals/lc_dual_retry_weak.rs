// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// kani-flags: -Z loop-contracts
//
// A valid but WEAK loop invariant fails the harness under Kani's loop-contract
// semantics, even when the loop is bounded and the concrete program is correct:
// the invariant replaces the loop, so whatever it does not say about the state
// after the loop is havocked. `lc_dual_weak.rs` pins that for an unbounded
// loop. These two bound the loop, so a bounded unroll of the concrete program
// proves the assertion.
//
// Before AY alignment review round 3 the loop-contract retry had a properties
// lane that proved the user's assertions on exactly that bounded unroll, with
// the loop contract switched off, and it printed both harnesses SUCCESSFUL in
// both lanes on main's bundle and the branch alike. The retry now proves every
// check with the loop contract on, in one lane.
//
// Oracles (Kani 0.67.0, measured 2026-09-28):
//   weak_bounded   MUST FAIL  (assertion; the first lane's counterexample is certified Genuine)
//   weak_compound  MUST FAIL  (assertion; the first lane fails on the compound `hi - lo` measure,
//                              an encoding gap, not a certified counterexample)
//
// Kani also fails weak_compound's decreases check. Its CBMC trace evaluates the
// measure to 2 both before and after a step that takes `lo` from 1 to 2 with
// `hi` = 2, i.e. it reads `lo` as it was before the loop. That check is not what
// this file is about: the assertion fails under the loop contract either way.
#![feature(stmt_expr_attributes)]
#![feature(proc_macro_hygiene)]

#[kani::proof]
fn weak_bounded() {
    let mut x: u8 = kani::any_where(|i| *i >= 2 && *i <= 3);
    #[kani::loop_invariant(x >= 1)]
    while x > 2 {
        x = x - 1;
    }
    assert!(x == 2);
}

#[kani::proof]
fn weak_compound() {
    let mut lo: u8 = 0;
    let hi: u8 = kani::any_where(|h| *h >= 1 && *h <= 2);
    let mut c: u8 = 0;
    #[kani::loop_invariant(lo <= hi)]
    #[kani::loop_decreases(hi - lo)]
    while lo < hi {
        lo = lo + 1;
        c = c.wrapping_add(1);
    }
    assert!(c == hi);
}
