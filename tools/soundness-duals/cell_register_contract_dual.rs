// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL -- the Cell store lane's register rebinding inside a
//! `#[kani::modifies]` frame (FC-06).
//!
//! The Cell store lane binds the referent's state variable to the stored value
//! (codegen_call_cell_register.rs). Inside a contract-checked function that
//! rebinding reached the FC-06 frame net as a write the net could not classify
//! (a non-constant footprint), and every `proof_for_contract` harness whose
//! function mutates a Cell was demoted, including the plainest idioms
//! `modifies(c.as_ptr())` with `c.replace(0)` and `modifies(&p.a)` with
//! `p.a.set(3)` (review of fix/chc-cell-set-write, 2026-09-26). The rebinding
//! mirrors exactly the bytes of the store, whose own precise frame check
//! already classified them, so it is excused with that store; a store outside
//! the footprint still fails its precise check.
//!
//! Oracle: the corpus-rev Kani 4c0fce8c3 (Kani 0.67.0) verifies every check_
//! row and fails every bad_ row (manifest entry). Run with -Z function-contracts.
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options -Z function-contracts --harness-timeout=30s cell_register_contract_dual.rs

use std::cell::Cell;

struct Pair {
    a: Cell<u32>,
    b: Cell<u32>,
}

#[kani::modifies(&p.a)]
#[kani::ensures(|_| true)]
fn set_a_ref(p: &Pair) {
    p.a.set(3)
}

#[kani::proof_for_contract(set_a_ref)]
fn check_set_a_ref() {
    let p = Pair { a: Cell::new(kani::any()), b: Cell::new(kani::any()) };
    set_a_ref(&p);
}

#[kani::modifies(p.a.as_ptr())]
#[kani::ensures(|_| true)]
fn set_a_ptr(p: &Pair) {
    p.a.set(3)
}

#[kani::proof_for_contract(set_a_ptr)]
fn check_set_a_ptr() {
    let p = Pair { a: Cell::new(kani::any()), b: Cell::new(kani::any()) };
    set_a_ptr(&p);
}

#[kani::requires(p.a.get() < 100)]
#[kani::modifies(&p.a)]
#[kani::ensures(|r: &u32| *r < 100)]
fn take_a_ref(p: &Pair) -> u32 {
    p.a.replace(0)
}

#[kani::proof_for_contract(take_a_ref)]
fn check_take_a_ref() {
    let p = Pair { a: Cell::new(kani::any()), b: Cell::new(kani::any()) };
    let _ = take_a_ref(&p);
}

#[kani::requires(c.get() < 100)]
#[kani::modifies(c.as_ptr())]
#[kani::ensures(|r: &u32| *r < 100)]
fn take_plain(c: &Cell<u32>) -> u32 {
    c.replace(0)
}

#[kani::proof_for_contract(take_plain)]
fn check_take_plain() {
    let c = Cell::new(kani::any());
    let _ = take_plain(&c);
}

#[kani::requires(c.get() < 100)]
#[kani::modifies(c.as_ptr())]
#[kani::ensures(|r: &u32| *r < 50)]
fn take_plain_bad(c: &Cell<u32>) -> u32 {
    c.replace(0)
}

#[kani::proof_for_contract(take_plain_bad)]
fn bad_take_plain_ensures() {
    let c = Cell::new(kani::any());
    let _ = take_plain_bad(&c);
}

#[kani::modifies(&p.a)]
#[kani::ensures(|_| true)]
fn set_b_wrong_frame(p: &Pair) {
    p.b.set(3)
}

#[kani::proof_for_contract(set_b_wrong_frame)]
fn bad_set_b_wrong_frame() {
    let p = Pair { a: Cell::new(kani::any()), b: Cell::new(kani::any()) };
    set_b_wrong_frame(&p);
}
