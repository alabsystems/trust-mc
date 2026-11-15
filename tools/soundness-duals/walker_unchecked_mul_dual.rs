// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (missed-bug tripwire) -- `u8::unchecked_mul` UB inside a
//! dyn-dispatched method body, reached through the CHC INLINE WALKER.
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3; see the manifest entry):
//!   bug_multi_impl       -> VERIFICATION:- FAILED  ('attempt to compute `unchecked_mul` which would overflow')
//!   bug_single_impl_box  -> VERIFICATION:- FAILED  (same check)
//!   safe_multi_impl      -> VERIFICATION:- SUCCESSFUL
//!   bug_direct_call      -> VERIFICATION:- FAILED  (control, same check)
//!
//! MECHANISM UNDER TEST (Mechanism A of the 2026-09-23 walker investigation).
//! Core's `unchecked_mul` wrapper guards the operation with
//! `assert_unsafe_precondition!(check_language_ub, ..)`, whose branch is DEAD in
//! both tools (`check_language_ub()` folds to `false`, as Kani compiles every
//! `RuntimeChecks` flag), so the obligation both tools report is the BinOp in
//! the wrapper's body (`MulUnchecked`). The statement path checks that BinOp
//! (`emit_assignment_safety_checks`); the inline walker used to translate it as
//! plain bitvector arithmetic and record nothing, so the dyn rows verified
//! SUCCESSFUL. The walker now records the same check on its deferred-check
//! channel (`call/inline_shared/rvalue_ub.rs`).
//!
//! THE SHAPE. Promoted from the blast-radius probe `p2_unchecked_mul.rs`. The receiver is a
//! SYMBOLIC choice between two non-parametric impls into a `Box<dyn Op>`, so the
//! concrete type is not statically known and the call reaches the walker's
//! dispatch; `bug_single_impl_box` boxes one impl, but the crate still has two,
//! so the encoder sees two candidates for it as well (it takes the
//! constant-vtable short-circuit, not a one-impl path). The only obligation in
//! each bug harness is the UB, so a SUCCESSFUL is a missed bug and cannot be a
//! failing user assert. `safe_multi_impl` is the precision guard: the assumption
//! makes the operation defined, so a FAILED there is a false positive of the
//! new check. `bug_direct_call` runs the same operation with no dispatch; the
//! fn_inline path refuses core's unchecked wrappers
//! (`callee_uses_special_arithmetic_handler`) and `step_wrapping.rs` emits the
//! check, so it is the control that localises a miss to the walker.
//!
//! Lane scope: CHC only. BMC has its own inline machinery, not investigated here.
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options --harness-timeout=30s walker_unchecked_mul_dual.rs

/// Keeps its argument alive through rustc's MIR optimisations and is
/// obligation-free by inspection (see `unchecked_arith_walker_dual.rs`).
#[inline(never)]
fn sink<T>(_value: T) {}

pub trait Op {
    fn op(&self, a: u8, b: u8) -> u8;
}
pub struct ImplA;
pub struct ImplB;
impl Op for ImplA {
    fn op(&self, a: u8, b: u8) -> u8 {
        unsafe { a.unchecked_mul(b) }
    }
}
impl Op for ImplB {
    fn op(&self, a: u8, b: u8) -> u8 {
        unsafe { a.unchecked_mul(b) }
    }
}

#[kani::proof]
fn bug_multi_impl() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let obj: Box<dyn Op> = if kani::any() { Box::new(ImplA) } else { Box::new(ImplB) };
    sink(obj.op(a, b));
}

#[kani::proof]
fn bug_single_impl_box() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let obj: Box<dyn Op> = Box::new(ImplA);
    sink(obj.op(a, b));
}

#[kani::proof]
fn safe_multi_impl() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    kani::assume(a < 16 && b < 16);
    let obj: Box<dyn Op> = if kani::any() { Box::new(ImplA) } else { Box::new(ImplB) };
    sink(obj.op(a, b));
}

#[kani::proof]
fn bug_direct_call() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    sink(unsafe { a.unchecked_mul(b) });
}
