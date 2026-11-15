// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (missed-bug tripwire) -- `core::intrinsics::unchecked_div`
//! UB inside a dyn-dispatched method body, reached through the CHC INLINE WALKER.
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3; see the manifest entry):
//!   bug_div_zero_multi_impl             -> VERIFICATION:- FAILED  ('attempt to divide by zero')
//!   bug_div_zero_single_impl_box        -> VERIFICATION:- FAILED  (same check)
//!   safe_div_multi_impl                 -> VERIFICATION:- SUCCESSFUL
//!   bug_signed_div_overflow_multi_impl  -> VERIFICATION:- FAILED  ('attempt to divide with overflow')
//!   safe_signed_div_multi_impl          -> VERIFICATION:- SUCCESSFUL
//!   bug_div_zero_direct_call            -> VERIFICATION:- FAILED  (control, 'attempt to divide by zero')
//!
//! MECHANISM UNDER TEST (Mechanism A of the 2026-09-23 walker investigation),
//! for Div. `intrinsics::unchecked_div` lowers to a plain `BinOp::Div` with NO
//! preceding MIR `Assert` (the `a / b` operator carries one; the intrinsic does
//! not), so the only obligation is the BinOp's own: Kani checks it in
//! `check_div_overflow` (divisor zero, and signed `MIN / -1`). The walker used
//! to record nothing for it. `bug_signed_div_overflow_multi_impl` assumes a
//! non-zero divisor, so only `i8::MIN / -1` can fail: it exercises the signed
//! overflow check alone. Each `safe_` twin is a precision guard.
//! `bug_div_zero_direct_call` puts the Div in the harness body, where the
//! statement path checks it.
//!
//! New shape: the investigation suspected integer Div/Rem with no preceding
//! MIR Assert and did not probe it.
//!
//! Lane scope: CHC only.
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options --harness-timeout=30s walker_unchecked_div_intrinsic_dual.rs

#![allow(internal_features)]
#![feature(core_intrinsics)]

/// Keeps its argument alive through rustc's MIR optimisations and is
/// obligation-free by inspection (see `unchecked_arith_walker_dual.rs`).
#[inline(never)]
fn sink<T>(_value: T) {}

pub trait Op {
    fn div(&self, a: u8, b: u8) -> u8;
    fn sdiv(&self, a: i8, b: i8) -> i8;
}
pub struct ImplA;
pub struct ImplB;
impl Op for ImplA {
    fn div(&self, a: u8, b: u8) -> u8 {
        unsafe { core::intrinsics::unchecked_div(a, b) }
    }
    fn sdiv(&self, a: i8, b: i8) -> i8 {
        unsafe { core::intrinsics::unchecked_div(a, b) }
    }
}
impl Op for ImplB {
    fn div(&self, a: u8, b: u8) -> u8 {
        unsafe { core::intrinsics::unchecked_div(a, b) }
    }
    fn sdiv(&self, a: i8, b: i8) -> i8 {
        unsafe { core::intrinsics::unchecked_div(a, b) }
    }
}

#[kani::proof]
fn bug_div_zero_multi_impl() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let obj: Box<dyn Op> = if kani::any() { Box::new(ImplA) } else { Box::new(ImplB) };
    sink(obj.div(a, b));
}

#[kani::proof]
fn bug_div_zero_single_impl_box() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let obj: Box<dyn Op> = Box::new(ImplA);
    sink(obj.div(a, b));
}

#[kani::proof]
fn safe_div_multi_impl() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    kani::assume(b != 0);
    let obj: Box<dyn Op> = if kani::any() { Box::new(ImplA) } else { Box::new(ImplB) };
    sink(obj.div(a, b));
}

#[kani::proof]
fn bug_signed_div_overflow_multi_impl() {
    let a: i8 = kani::any();
    let b: i8 = kani::any();
    kani::assume(b != 0);
    let obj: Box<dyn Op> = if kani::any() { Box::new(ImplA) } else { Box::new(ImplB) };
    sink(obj.sdiv(a, b));
}

#[kani::proof]
fn safe_signed_div_multi_impl() {
    let a: i8 = kani::any();
    let b: i8 = kani::any();
    kani::assume(b != 0 && a != i8::MIN);
    let obj: Box<dyn Op> = if kani::any() { Box::new(ImplA) } else { Box::new(ImplB) };
    sink(obj.sdiv(a, b));
}

#[kani::proof]
fn bug_div_zero_direct_call() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    sink(unsafe { core::intrinsics::unchecked_div(a, b) });
}
