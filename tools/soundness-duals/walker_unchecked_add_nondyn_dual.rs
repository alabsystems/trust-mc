// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (missed-bug tripwire) -- `u8::unchecked_add` UB inside a body
//! the CHC INLINE WALKER reaches WITHOUT dyn dispatch.
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3; see the manifest entry):
//!   bug_recursive_helper        -> VERIFICATION:- FAILED  ('attempt to compute `unchecked_add` which would overflow')
//!   safe_recursive_helper       -> VERIFICATION:- SUCCESSFUL
//!   bug_fn_ptr_symbolic_choice  -> VERIFICATION:- FAILED  (same check)
//!   safe_fn_ptr_symbolic_choice -> VERIFICATION:- SUCCESSFUL
//!   bug_box_dyn_fn_closure      -> VERIFICATION:- FAILED  (same check)
//!   safe_box_dyn_fn_closure     -> VERIFICATION:- SUCCESSFUL
//!   bug_plain_helper_control    -> VERIFICATION:- FAILED  (control, same check)
//!
//! MECHANISM UNDER TEST (Mechanism A of the 2026-09-23 walker investigation):
//! the walker translated the `AddUnchecked` BinOp in core's `unchecked_add`
//! wrapper as plain bitvector arithmetic and recorded no check. The walker is
//! not only the dyn-dispatch path; three other hosts walk a body and emit its
//! deferred checks, and each harness below reaches one of them:
//!  * `bug_recursive_helper` -- a recursive helper stays a Call terminator
//!    (rustc's MIR inliner skips recursive callees), so fn_inline walks its body
//!    (`codegen_call_fn_inline_emit.rs`);
//!  * `bug_fn_ptr_symbolic_choice` -- a symbolic choice between two fn items
//!    through a `fn` pointer (`codegen_call_fn_ptr.rs`);
//!  * `bug_box_dyn_fn_closure` -- a `Box<dyn Fn>` closure body
//!    (`codegen_call_closure/mod.rs`).
//! Each `safe_` twin assumes the operands small enough that the add is defined:
//! a FAILED there is a false positive of the new walker check.
//! `bug_plain_helper_control` calls a non-recursive helper, which the MIR
//! inliner or the statement path handles without the walker.
//!
//! Promoted from the blast-radius probe `p8_nondyn_walker.rs`; the fn-pointer
//! and closure safe twins are new.
//!
//! Lane scope: CHC only.
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options --harness-timeout=30s walker_unchecked_add_nondyn_dual.rs

/// Keeps its argument alive through rustc's MIR optimisations and is
/// obligation-free by inspection (see `unchecked_arith_walker_dual.rs`).
#[inline(never)]
fn sink<T>(_value: T) {}

// Recursive: FunctionInlinePass skips recursive callees, so the call stays a
// Call terminator and fn_inline walks the body.
fn rec_add(a: u8, b: u8, n: u8) -> u8 {
    if n == 0 { unsafe { a.unchecked_add(b) } } else { rec_add(a, b, n - 1) }
}

fn add_helper_a(a: u8, b: u8) -> u8 {
    unsafe { a.unchecked_add(b) }
}
fn add_helper_b(a: u8, b: u8) -> u8 {
    unsafe { a.unchecked_add(b) }
}

#[kani::proof]
fn bug_recursive_helper() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    sink(rec_add(a, b, 1));
}

#[kani::proof]
fn safe_recursive_helper() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    kani::assume(a < 100 && b < 100);
    sink(rec_add(a, b, 1));
}

#[kani::proof]
fn bug_fn_ptr_symbolic_choice() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let f: fn(u8, u8) -> u8 = if kani::any() { add_helper_a } else { add_helper_b };
    sink(f(a, b));
}

#[kani::proof]
fn safe_fn_ptr_symbolic_choice() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    kani::assume(a < 100 && b < 100);
    let f: fn(u8, u8) -> u8 = if kani::any() { add_helper_a } else { add_helper_b };
    sink(f(a, b));
}

#[kani::proof]
fn bug_box_dyn_fn_closure() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let f: Box<dyn Fn(u8, u8) -> u8> = Box::new(|x: u8, y: u8| unsafe { x.unchecked_add(y) });
    sink(f(a, b));
}

#[kani::proof]
fn safe_box_dyn_fn_closure() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    kani::assume(a < 100 && b < 100);
    let f: Box<dyn Fn(u8, u8) -> u8> = Box::new(|x: u8, y: u8| unsafe { x.unchecked_add(y) });
    sink(f(a, b));
}

#[kani::proof]
fn bug_plain_helper_control() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    sink(add_helper_a(a, b));
}
