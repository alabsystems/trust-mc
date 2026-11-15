// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (missed-bug tripwire) -- arithmetic UB one call DEEPER than
//! the dyn-dispatched method, in a helper the method calls.
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3; see the manifest entry):
//!   bug_nested_plain_add_multi_impl     -> VERIFICATION:- FAILED  ('attempt to add with overflow')
//!   safe_nested_plain_add_multi_impl    -> VERIFICATION:- SUCCESSFUL
//!   bug_nested_unchecked_multi_impl     -> VERIFICATION:- FAILED  ('attempt to compute `unchecked_add` which would overflow')
//!   safe_nested_unchecked_multi_impl    -> VERIFICATION:- SUCCESSFUL
//!   bug_unchecked_helper_direct_call    -> VERIFICATION:- FAILED  (same check; NOT a clean control, below)
//!
//! MECHANISM UNDER TEST (Mechanism A of the 2026-09-23 walker investigation).
//! The walker walks the dyn method, then the helper as a NESTED walk, then
//! core's `unchecked_add` wrapper; a check recorded two levels down reaches the
//! host only if every nested walk absorbs it (`absorb_nested_deferred_checks`)
//! and every merge weakens it by its dispatch guard. Before the fix the
//! `AddUnchecked` BinOp at the bottom recorded nothing, so
//! `bug_nested_unchecked_multi_impl` verified SUCCESSFUL.
//! `bug_nested_plain_add_multi_impl` is the MIR-`Assert` route through the same
//! nesting (`a + b` with overflow checks on), which already worked: it guards
//! the channel the fix rides on. Each `safe_` twin is a precision guard.
//! `bug_unchecked_helper_direct_call` calls the helper with no dispatch. It was
//! meant as the control, but MEASURED 2026-09-23 it is not one: on the unfixed
//! bundle it verified SUCCESSFUL too, because the direct call of a local helper
//! that wraps `u8::unchecked_add` also reaches the walker (unlike
//! `walker_unchecked_add_nondyn_dual.rs::bug_plain_helper_control`, which the
//! unfixed bundle already failed). It is kept as one more walker route.
//!
//! Promoted from the blast-radius probe `p10_nested_in_dyn.rs`;
//! `safe_nested_unchecked_multi_impl` and the direct-call control are new.
//!
//! Lane scope: CHC only.
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options --harness-timeout=30s walker_nested_helper_dual.rs

/// Keeps its argument alive through rustc's MIR optimisations and is
/// obligation-free by inspection (see `unchecked_arith_walker_dual.rs`).
#[inline(never)]
fn sink<T>(_value: T) {}

fn plain_add(a: u8, b: u8) -> u8 {
    a + b
}
fn unchecked_helper(a: u8, b: u8) -> u8 {
    unsafe { a.unchecked_add(b) }
}

pub trait Op {
    fn plain(&self, a: u8, b: u8) -> u8;
    fn unchecked(&self, a: u8, b: u8) -> u8;
}
pub struct ImplA;
pub struct ImplB;
impl Op for ImplA {
    fn plain(&self, a: u8, b: u8) -> u8 { plain_add(a, b) }
    fn unchecked(&self, a: u8, b: u8) -> u8 { unchecked_helper(a, b) }
}
impl Op for ImplB {
    fn plain(&self, a: u8, b: u8) -> u8 { plain_add(a, b) }
    fn unchecked(&self, a: u8, b: u8) -> u8 { unchecked_helper(a, b) }
}

#[kani::proof]
fn bug_nested_plain_add_multi_impl() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let obj: Box<dyn Op> = if kani::any() { Box::new(ImplA) } else { Box::new(ImplB) };
    sink(obj.plain(a, b));
}

#[kani::proof]
fn safe_nested_plain_add_multi_impl() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    kani::assume(a < 100 && b < 100);
    let obj: Box<dyn Op> = if kani::any() { Box::new(ImplA) } else { Box::new(ImplB) };
    sink(obj.plain(a, b));
}

#[kani::proof]
fn bug_nested_unchecked_multi_impl() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let obj: Box<dyn Op> = if kani::any() { Box::new(ImplA) } else { Box::new(ImplB) };
    sink(obj.unchecked(a, b));
}

#[kani::proof]
fn safe_nested_unchecked_multi_impl() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    kani::assume(a < 100 && b < 100);
    let obj: Box<dyn Op> = if kani::any() { Box::new(ImplA) } else { Box::new(ImplB) };
    sink(obj.unchecked(a, b));
}

#[kani::proof]
fn bug_unchecked_helper_direct_call() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    sink(unchecked_helper(a, b));
}
