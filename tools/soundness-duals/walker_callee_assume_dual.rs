// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL -- a `kani::assume` inside a body reached through a fn
//! pointer or a `dyn` dispatch constrains the caller's path, from the design
//! 3 review (2026-09-26).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3; see the manifest entry):
//!   safe_assume_direct               -> VERIFICATION:- SUCCESSFUL  (control)
//!   safe_assume_fnptr_exact          -> VERIFICATION:- SUCCESSFUL
//!   safe_assume_fnptr_exact_noinline -> VERIFICATION:- SUCCESSFUL
//!   safe_assume_fnptr_ret            -> VERIFICATION:- SUCCESSFUL
//!   safe_assume_fnptr_both_arms      -> VERIFICATION:- SUCCESSFUL
//!   safe_assume_fnptr_from_call      -> VERIFICATION:- SUCCESSFUL
//!   safe_assume_nested_exact         -> VERIFICATION:- SUCCESSFUL
//!   safe_assume_nested_multi         -> VERIFICATION:- SUCCESSFUL
//!   safe_assume_dyn_single           -> VERIFICATION:- SUCCESSFUL
//!   safe_assume_dyn_multi            -> VERIFICATION:- SUCCESSFUL
//!   safe_assume_dyn_fn               -> VERIFICATION:- SUCCESSFUL
//!   bug_assume_fnptr_weaker          -> VERIFICATION:- FAILED  ('assertion failed: a < 9')
//!   bug_assume_dyn_weaker            -> VERIFICATION:- FAILED  ('assertion failed: a < 9')
//!
//! MECHANISM (main 25905b622 and the first design 3 bundle ba0988f16445):
//! the inline walk folds an assume into the callee's value as
//! `ite(cond, value, __assume_pruned_inline)`, and a host emit must add
//! `cond` as a transition constraint and strip the pruned leaf. The direct
//! inline emit did; the fn-pointer, virtual, closure and `block_on` emits took
//! only the assert guard, so the assume was lost and the caller's assertion
//! of the assumed fact failed, certified Genuine. They now share
//! `take_inline_result_guards` (`codegen_call_fn_inline_emit.rs`). The bug_
//! rows keep the fix from over-constraining: the assumed fact is weaker than
//! the assertion.
//!
//! Lane scope: CHC only.
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options --harness-timeout=30s walker_callee_assume_dual.rs

fn a_assume(a: u8, b: u8) -> u8 {
    kani::assume(a < 10);
    a.wrapping_add(b)
}
fn a_assume2(a: u8, b: u8) -> u8 {
    kani::assume(a < 10);
    a.wrapping_sub(b)
}
#[inline(never)]
fn a_assume_noinline(a: u8, b: u8) -> u8 {
    kani::assume(a < 10);
    a.wrapping_add(b)
}
fn ret_assume(a: u8) -> u8 {
    kani::assume(a < 10);
    a
}

#[kani::proof]
fn safe_assume_direct() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let _r = a_assume(a, b);
    assert!(a < 10);
}

#[kani::proof]
fn safe_assume_fnptr_exact() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let f: fn(u8, u8) -> u8 = a_assume;
    let _r = f(a, b);
    assert!(a < 10);
}

#[kani::proof]
fn safe_assume_fnptr_exact_noinline() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let f: fn(u8, u8) -> u8 = a_assume_noinline;
    let _r = f(a, b);
    assert!(a < 10);
}

// The assume reaches the caller through the return value alone.
#[kani::proof]
fn safe_assume_fnptr_ret() {
    let a: u8 = kani::any();
    let f: fn(u8) -> u8 = ret_assume;
    let r = f(a);
    assert!(r < 10);
}

#[kani::proof]
fn safe_assume_fnptr_both_arms() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let f: fn(u8, u8) -> u8 = if kani::any() { a_assume } else { a_assume2 };
    let _r = f(a, b);
    assert!(a < 10);
}

#[inline(never)]
fn get_assume() -> fn(u8, u8) -> u8 {
    a_assume
}

#[kani::proof]
fn safe_assume_fnptr_from_call() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let f = get_assume();
    let _r = f(a, b);
    assert!(a < 10);
}

#[inline(never)]
fn call_p(f: fn(u8, u8) -> u8, a: u8, b: u8) -> u8 {
    f(a, b)
}

#[kani::proof]
fn safe_assume_nested_exact() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let _r = call_p(a_assume, a, b);
    assert!(a < 10);
}

#[kani::proof]
fn safe_assume_nested_multi() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let f: fn(u8, u8) -> u8 = if kani::any() { a_assume } else { a_assume2 };
    let _r = call_p(f, a, b);
    assert!(a < 10);
}

pub trait Tr {
    fn m(&self, a: u8, b: u8) -> u8;
}
pub struct SA;
pub struct SB;
impl Tr for SA {
    fn m(&self, a: u8, b: u8) -> u8 {
        kani::assume(a < 10);
        a.wrapping_add(b)
    }
}
impl Tr for SB {
    fn m(&self, a: u8, b: u8) -> u8 {
        kani::assume(a < 10);
        a.wrapping_sub(b)
    }
}

#[kani::proof]
fn safe_assume_dyn_single() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let o: Box<dyn Tr> = Box::new(SA);
    let _r = o.m(a, b);
    assert!(a < 10);
}

#[kani::proof]
fn safe_assume_dyn_multi() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let o: Box<dyn Tr> = if kani::any() { Box::new(SA) } else { Box::new(SB) };
    let _r = o.m(a, b);
    assert!(a < 10);
}

#[kani::proof]
fn safe_assume_dyn_fn() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let f: Box<dyn Fn(u8, u8) -> u8> = Box::new(|x: u8, y: u8| {
        kani::assume(x < 10);
        x.wrapping_add(y)
    });
    let _r = f(a, b);
    assert!(a < 10);
}

#[kani::proof]
fn bug_assume_fnptr_weaker() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let f: fn(u8, u8) -> u8 = if kani::any() { a_assume } else { a_assume2 };
    let _r = f(a, b);
    assert!(a < 9);
}

#[kani::proof]
fn bug_assume_dyn_weaker() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let o: Box<dyn Tr> = if kani::any() { Box::new(SA) } else { Box::new(SB) };
    let _r = o.m(a, b);
    assert!(a < 9);
}
