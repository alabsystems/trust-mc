// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z function-contracts
//
// DUAL: a write made by a HELPER the checked function calls, not by the
// checked function's own body. The helper's store reaches the harness through
// the inliner or the CHC nested call walker (a closure call is dispatched
// through the walker), so the modifies frame check must follow it there.
//
// Written 2026-09-15 with the walker modifies-frame fix
// (fix/walker-modifies-frame): before it the CHC walker never ran the frame
// check for writes inside inlined callee bodies.
//
// Oracle (per harness):
//   helper_outside_must_fail           -> VERIFICATION:- FAILED (frame)
//   closure_helper_outside_must_fail   -> VERIFICATION:- FAILED (frame)
//   helper_inside_safe                 -> VERIFICATION:- SUCCESSFUL
//   closure_helper_inside_safe         -> VERIFICATION:- SUCCESSFUL
//   dyn_helper_outside_must_fail       -> VERIFICATION:- FAILED (frame)
//   dyn_helper_inside_safe             -> VERIFICATION:- SUCCESSFUL
//   rec_helper_outside_must_fail       -> VERIFICATION:- FAILED (frame)
//   rec_helper_inside_safe             -> VERIFICATION:- SUCCESSFUL
//
// Measured before the fix (2026-09-14 probe, CHC): the dyn and recursive
// must-fail rows verified SUCCESSFUL.

#[repr(C)]
struct Pair {
    a: u32,
    b: u32,
}

fn poke(q: &mut u32) {
    *q = 7;
}

fn poke_a(p: &mut Pair) {
    p.a = 3;
}

#[kani::modifies(&p.a)]
fn helper_outside(p: &mut Pair, q: &mut u32) {
    poke_a(p);
    poke(q);
}

#[kani::proof_for_contract(helper_outside)]
fn helper_outside_must_fail() {
    let mut p = Pair { a: kani::any(), b: kani::any() };
    let mut q: u32 = kani::any();
    helper_outside(&mut p, &mut q);
}

#[kani::modifies(&p.a)]
fn closure_helper_outside(p: &mut Pair, q: &mut u32) {
    p.a = 1;
    let mut set = |x: &mut u32| *x = 9;
    set(q);
}

#[kani::proof_for_contract(closure_helper_outside)]
fn closure_helper_outside_must_fail() {
    let mut p = Pair { a: kani::any(), b: kani::any() };
    let mut q: u32 = kani::any();
    closure_helper_outside(&mut p, &mut q);
}

#[kani::modifies(&p.a)]
fn helper_inside(p: &mut Pair, q: &mut u32) {
    poke_a(p);
    let _read = *q;
}

#[kani::proof_for_contract(helper_inside)]
fn helper_inside_safe() {
    let mut p = Pair { a: kani::any(), b: kani::any() };
    let mut q: u32 = kani::any();
    helper_inside(&mut p, &mut q);
}

#[kani::modifies(&p.a)]
fn closure_helper_inside(p: &mut Pair) {
    let mut set = |x: &mut Pair| x.a = 9;
    set(p);
}

#[kani::proof_for_contract(closure_helper_inside)]
fn closure_helper_inside_safe() {
    let mut p = Pair { a: kani::any(), b: kani::any() };
    closure_helper_inside(&mut p);
}

trait Setter {
    fn set(&mut self, v: u32);
}

struct Slot {
    v: u32,
}

impl Setter for Slot {
    fn set(&mut self, v: u32) {
        self.v = v;
    }
}

#[kani::modifies(&p.a)]
fn dyn_helper_outside(p: &mut Pair, s: &mut dyn Setter) {
    p.a = 1;
    s.set(9);
}

#[kani::proof_for_contract(dyn_helper_outside)]
fn dyn_helper_outside_must_fail() {
    let mut p = Pair { a: kani::any(), b: kani::any() };
    let mut slot = Slot { v: kani::any() };
    dyn_helper_outside(&mut p, &mut slot);
}

#[kani::modifies(s)]
fn dyn_helper_inside(s: &mut Slot) {
    let d: &mut dyn Setter = s;
    d.set(9);
}

#[kani::proof_for_contract(dyn_helper_inside)]
fn dyn_helper_inside_safe() {
    let mut slot = Slot { v: kani::any() };
    dyn_helper_inside(&mut slot);
}

fn rec_write(q: &mut u32, n: u32) {
    if n == 0 {
        *q = 5;
    } else {
        rec_write(q, n - 1);
    }
}

#[kani::modifies(&p.a)]
fn rec_helper_outside(p: &mut Pair, q: &mut u32) {
    p.a = 1;
    rec_write(q, 1);
}

#[kani::proof_for_contract(rec_helper_outside)]
fn rec_helper_outside_must_fail() {
    let mut p = Pair { a: kani::any(), b: kani::any() };
    let mut q: u32 = kani::any();
    rec_helper_outside(&mut p, &mut q);
}

#[kani::modifies(q)]
fn rec_helper_inside(q: &mut u32) {
    rec_write(q, 1);
}

#[kani::proof_for_contract(rec_helper_inside)]
fn rec_helper_inside_safe() {
    let mut q: u32 = kani::any();
    rec_helper_inside(&mut q);
}
