// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (missed-bug tripwire) -- `core::intrinsics::unchecked_rem` and
//! a SIGNED `unchecked_shl` distance inside a dyn-dispatched method body, reached
//! through the CHC INLINE WALKER.
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3; see the manifest entry):
//!   bug_rem_zero               -> VERIFICATION:- FAILED  ('attempt to calculate the remainder with a divisor of zero', and the MIN % -1 check)
//!   bug_rem_min_neg1           -> VERIFICATION:- FAILED  ('attempt to calculate the remainder with overflow')
//!   safe_rem                   -> VERIFICATION:- SUCCESSFUL
//!   bug_shl_negative_distance  -> VERIFICATION:- FAILED  ('attempt to shift by negative distance')
//!   safe_shl_signed_distance   -> VERIFICATION:- SUCCESSFUL
//!
//! MECHANISM UNDER TEST (Mechanism A of the 2026-09-23 walker investigation):
//! the Rem arm of the walker's BinOp checks (`inline_shared/rvalue_ub.rs`),
//! which `walker_unchecked_div_intrinsic_dual.rs` does not reach, and the
//! SIGNED shift-distance form (`distance < 32 && distance >= 0`), which the
//! unsigned-distance shift duals do not. `bug_rem_min_neg1` assumes a non-zero
//! divisor, so only `i8::MIN % -1` can fail. For a negative distance the CHC
//! lane reports its one shift check, 'attempt to shift by excessive shift
//! distance', where Kani says 'negative distance'; the verdict is the same.
//! Promoted from the 2026-09-23 review probe rp_rem_shift.rs.
//!
//! Lane scope: CHC only.
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options --harness-timeout=30s walker_unchecked_rem_shift_dual.rs

#![allow(internal_features)]
#![feature(core_intrinsics)]

/// Keeps its argument alive through rustc's MIR optimisations and is
/// obligation-free by inspection (see `unchecked_arith_walker_dual.rs`).
#[inline(never)]
fn sink<T>(_value: T) {}

pub trait Op {
    fn rem(&self, a: i8, b: i8) -> i8;
    fn shl(&self, a: i32, b: i32) -> i32;
}
pub struct ImplA;
pub struct ImplB;
impl Op for ImplA {
    fn rem(&self, a: i8, b: i8) -> i8 {
        unsafe { core::intrinsics::unchecked_rem(a, b) }
    }
    fn shl(&self, a: i32, b: i32) -> i32 {
        unsafe { core::intrinsics::unchecked_shl(a, b) }
    }
}
impl Op for ImplB {
    fn rem(&self, a: i8, b: i8) -> i8 {
        unsafe { core::intrinsics::unchecked_rem(a, b) }
    }
    fn shl(&self, a: i32, b: i32) -> i32 {
        unsafe { core::intrinsics::unchecked_shl(a, b) }
    }
}

fn pick() -> Box<dyn Op> {
    if kani::any() { Box::new(ImplA) } else { Box::new(ImplB) }
}

#[kani::proof]
fn bug_rem_zero() {
    let a: i8 = kani::any();
    let b: i8 = kani::any();
    sink(pick().rem(a, b));
}

#[kani::proof]
fn bug_rem_min_neg1() {
    let a: i8 = kani::any();
    let b: i8 = kani::any();
    kani::assume(b != 0);
    sink(pick().rem(a, b));
}

#[kani::proof]
fn safe_rem() {
    let a: i8 = kani::any();
    let b: i8 = kani::any();
    kani::assume(b != 0 && a != i8::MIN);
    sink(pick().rem(a, b));
}

#[kani::proof]
fn bug_shl_negative_distance() {
    let a: i32 = kani::any();
    let b: i32 = kani::any();
    kani::assume(b < 0);
    sink(pick().shl(a, b));
}

#[kani::proof]
fn safe_shl_signed_distance() {
    let a: i32 = kani::any();
    let b: i32 = kani::any();
    kani::assume(b >= 0 && b < 32);
    sink(pick().shl(a, b));
}
