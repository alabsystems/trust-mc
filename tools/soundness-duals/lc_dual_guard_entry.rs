// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// kani-flags: -Z loop-contracts
//
// Loop-contract BASE obligation vs. the loop guard on entry.
//
// Kani (0.67.0, measured) checks `#[kani::loop_invariant]` on entry only when the
// loop is ENTERED: a loop whose guard is false on entry runs zero iterations, its
// invariant is neither checked nor assumed, and the state after it is the entry
// state. The CHC loop rule used to assert the base on every entry edge, which
// refuted tests/expected/loop-contract/function_with_loop_no_assertion.rs with a
// counterexample certified Genuine (Kani: VERIFICATION:- SUCCESSFUL).
//
// Oracles (each confirmed with Kani 0.67.0):
//   skipped_loop_checks_no_base        NOT-GENUINE  (Kani SUCCESSFUL: x == 7 never enters)
//   entered_loop_checks_base           MUST FAIL    (base, only on the entered x == 7 path)
//   skipped_loop_assumes_no_invariant  MUST FAIL    (x == 0 skips the loop; nothing assumed)
//   function_loop_guard_false_on_entry NOT-GENUINE  (the corpus shape, without contracts)
//   constant_entered_loop_checks_base   MUST FAIL   (guard true on entry: the gate is
//                                                    dropped and the base must still bind)
//   constant_skipped_loop_checks_no_base NOT-GENUINE (guard false on entry from a constant)
#![feature(stmt_expr_attributes)]
#![feature(proc_macro_hygiene)]

#[kani::proof]
fn skipped_loop_checks_no_base() {
    let mut x: u8 = kani::any();
    // x == 7 violates the invariant but does not enter the loop.
    #[kani::loop_invariant(x != 7)]
    while x > 7 {
        x = 6;
    }
}

#[kani::proof]
fn entered_loop_checks_base() {
    let mut x: u8 = kani::any();
    // x == 7 violates the invariant AND enters the loop: the only failing
    // obligation is the base case. Step: x != 7 && x > 5 ==> 5 != 7.
    #[kani::loop_invariant(x != 7)]
    while x > 5 {
        x = 5;
    }
}

#[kani::proof]
fn skipped_loop_assumes_no_invariant() {
    let mut i: u16 = kani::any();
    #[kani::loop_invariant(i >= 2)]
    while i > 2 {
        i = i - 1;
    }
    // i == 0 and i == 1 skip the loop: the invariant must not be assumed there.
    assert!(i >= 2);
}

fn has_loop(mut i: u16) -> u16 {
    #[kani::loop_invariant(i >= 2)]
    while i > 2 {
        i = i - 1;
    }
    i
}

#[kani::proof]
fn function_loop_guard_false_on_entry() {
    let i: u16 = kani::any();
    let _j = has_loop(i);
}

#[kani::proof]
fn constant_entered_loop_checks_base() {
    let mut x: u8 = 7;
    #[kani::loop_invariant(x != 7)]
    while x > 5 {
        x = 5;
    }
}

#[kani::proof]
fn constant_skipped_loop_checks_no_base() {
    let mut x: u8 = 7;
    #[kani::loop_invariant(x != 7)]
    while x > 7 {
        x = 6;
    }
}
