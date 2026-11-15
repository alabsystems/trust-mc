// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (both directions) -- `kani::panic` in a walked body
//! (fix/chc-walker-fail-closed, package round 2 item d).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, measured 2026-09-27):
//!   d_panic_arm_multi_bug          -> VERIFICATION:- FAILED  ('seven is not allowed')
//!   d_panic_arm_multi_safe         -> VERIFICATION:- SUCCESSFUL
//!   d_unreachable_macro_safe       -> VERIFICATION:- SUCCESSFUL
//!   d_nested_straight_panic_bug    -> VERIFICATION:- FAILED  ('fail_hard reached')
//!   d_nested_straight_panic_safe   -> VERIFICATION:- SUCCESSFUL
//!
//! MECHANISM UNDER TEST. trust-mc's `library/std` lowers `panic!`,
//! `unreachable!`, `todo!` and `unimplemented!` to `kani::panic(msg)`, the
//! `PanicHook`, which Kani's `codegen_panic` makes a failing assertion with
//! the message. The walker did not know the hook: a `kani::panic` arm was
//! walked as an unmodelled diverging call. On main that call dropped the
//! panic (`d_panic_arm_multi_bug` SUCCESSFUL clean, a missed bug); the first
//! round made it an uncertified reach check (FAILED, never Genuine). The
//! walker now records it exactly (`terminator_exec.rs` `is_kani_panic_callee`,
//! `switchint.rs` `is_panic_arm`): an arm's "not taken" condition, or `false`
//! on a straight-line path, with the panic's message, so the bug rows FAIL
//! Genuine.
//!
//! Lane scope: CHC only.
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options --harness-timeout=30s walker_kani_panic_dual.rs

#[inline(never)]
fn sink<T>(_v: T) {}

pub trait Op { fn op(&self, a: u8) -> u8; }
pub struct A; pub struct B;
impl Op for A {
    fn op(&self, a: u8) -> u8 {
        if a == 7 { panic!("seven is not allowed"); }
        a
    }
}
impl Op for B { fn op(&self, a: u8) -> u8 { a.wrapping_add(1) } }

#[kani::proof]
fn d_panic_arm_multi_bug() {
    let a: u8 = kani::any();
    let o: Box<dyn Op> = if kani::any() { Box::new(A) } else { Box::new(B) };
    sink(o.op(a));
}
#[kani::proof]
fn d_panic_arm_multi_safe() {
    let a: u8 = kani::any();
    kani::assume(a != 7);
    let o: Box<dyn Op> = if kani::any() { Box::new(A) } else { Box::new(B) };
    sink(o.op(a));
}

pub trait Op2 { fn op(&self, a: u8) -> u8; }
pub struct C;
impl Op2 for C {
    fn op(&self, a: u8) -> u8 {
        match a % 3 {
            0 => a,
            1 => a.wrapping_mul(2),
            2 => a.wrapping_add(5),
            _ => unreachable!("mod three"),
        }
    }
}
impl Op2 for B { fn op(&self, a: u8) -> u8 { a } }
#[kani::proof]
fn d_unreachable_macro_safe() {
    let a: u8 = kani::any();
    let o: Box<dyn Op2> = if kani::any() { Box::new(C) } else { Box::new(B) };
    sink(o.op(a));
}

#[inline(never)]
fn fail_hard(v: u8) -> u8 {
    panic!("fail_hard reached");
}
pub trait Op3 { fn op(&self, a: u8) -> u8; }
pub struct D;
impl Op3 for D {
    fn op(&self, a: u8) -> u8 {
        if a > 200 { fail_hard(a) } else { a }
    }
}
impl Op3 for B { fn op(&self, a: u8) -> u8 { a } }
#[kani::proof]
fn d_nested_straight_panic_bug() {
    let a: u8 = kani::any();
    let o: Box<dyn Op3> = if kani::any() { Box::new(D) } else { Box::new(B) };
    sink(o.op(a));
}
#[kani::proof]
fn d_nested_straight_panic_safe() {
    let a: u8 = kani::any();
    kani::assume(a <= 200);
    let o: Box<dyn Op3> = if kani::any() { Box::new(D) } else { Box::new(B) };
    sink(o.op(a));
}
