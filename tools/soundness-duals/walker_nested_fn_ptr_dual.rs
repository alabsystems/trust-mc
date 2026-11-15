// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (missed-bug tripwire) -- a call through a fn POINTER inside a
//! dyn-dispatched method body, reached through the CHC INLINE WALKER.
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3; see the manifest entry):
//!   bug_symbolic_fnptr_in_dyn -> VERIFICATION:- FAILED  ('attempt to compute `unchecked_add` which would overflow')
//!   bug_decoy_fnptr_in_dyn    -> VERIFICATION:- FAILED  (same check)
//!   bug_single_fnptr_in_dyn   -> VERIFICATION:- FAILED  (same check; control)
//!   safe_decoy_fnptr_in_dyn   -> VERIFICATION:- SUCCESSFUL
//!
//! MECHANISM UNDER TEST. The walker cannot trace which function a fn-pointer
//! operand holds, and it used to walk the body of the FIRST `ReifyFnPointer`
//! cast in the HOST body (`resolve_any_fn_ptr_body`) unconditionally. When the
//! host reifies a decoy first (`bug_decoy_fnptr_in_dyn`) or chooses between two
//! pointers symbolically with the UB target second (`bug_symbolic_fnptr_in_dyn`),
//! the walked body is `add_safe`, the overflowing `add_ub` is never walked, and
//! the harness verified SUCCESSFUL clean. The walker now resolves the pointer by
//! its VALUE when it is one of the ids the host's reifications carry, and
//! otherwise walks every function the host reifies and merges the results under
//! `pointer == id`, as a dyn dispatch does (`nested_call.rs`, FnPtr arm).
//!
//! `bug_single_fnptr_in_dyn` reifies only `add_ub`: it was caught before and is
//! the control. `safe_decoy_fnptr_in_dyn` is the precision guard: the merge
//! must not fire `add_ub`'s check when its operands are small.
//!
//! Lane scope: CHC only.
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options --harness-timeout=30s walker_nested_fn_ptr_dual.rs

/// Keeps its argument alive through rustc's MIR optimisations and is
/// obligation-free by inspection (see `unchecked_arith_walker_dual.rs`).
#[inline(never)]
fn sink<T>(_value: T) {}

fn add_safe(a: u8, b: u8) -> u8 {
    a.wrapping_add(b)
}
fn add_ub(a: u8, b: u8) -> u8 {
    unsafe { a.unchecked_add(b) }
}

pub trait Op {
    fn op(&self, f: fn(u8, u8) -> u8, a: u8, b: u8) -> u8;
}
pub struct A;
pub struct B;
impl Op for A {
    fn op(&self, f: fn(u8, u8) -> u8, a: u8, b: u8) -> u8 {
        f(a, b)
    }
}
impl Op for B {
    fn op(&self, f: fn(u8, u8) -> u8, a: u8, b: u8) -> u8 {
        f(a, b)
    }
}

fn pick() -> Box<dyn Op> {
    if kani::any() { Box::new(A) } else { Box::new(B) }
}

#[kani::proof]
fn bug_symbolic_fnptr_in_dyn() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let f: fn(u8, u8) -> u8 = if kani::any() { add_safe } else { add_ub };
    sink(pick().op(f, a, b));
}

#[kani::proof]
fn bug_decoy_fnptr_in_dyn() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let decoy: fn(u8, u8) -> u8 = add_safe;
    sink(decoy);
    let f: fn(u8, u8) -> u8 = add_ub;
    sink(pick().op(f, a, b));
}

#[kani::proof]
fn bug_single_fnptr_in_dyn() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let f: fn(u8, u8) -> u8 = add_ub;
    sink(pick().op(f, a, b));
}

#[kani::proof]
fn safe_decoy_fnptr_in_dyn() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    kani::assume(a < 100 && b < 100);
    let decoy: fn(u8, u8) -> u8 = add_safe;
    sink(decoy);
    let f: fn(u8, u8) -> u8 = add_ub;
    sink(pick().op(f, a, b));
}
