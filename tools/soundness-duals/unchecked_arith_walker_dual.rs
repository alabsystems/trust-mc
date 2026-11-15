// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (missed-bug tripwire) — unchecked-arithmetic UB reached
//! through the INLINE WALKER instead of the statement path.
//!
//! Oracle (per harness):
//!   bug_unchecked_add_overflow_in_dyn_body   -> VERIFICATION:- FAILED  (multi-impl ITE)
//!   bug_unchecked_add_overflow_single_impl_box -> VERIFICATION:- FAILED
//!   safe_unchecked_add_assumed_in_dyn_body   -> VERIFICATION:- SUCCESSFUL
//!   bug_unchecked_add_overflow_direct_call   -> VERIFICATION:- FAILED  (control)
//!
//! MECHANISM UNDER TEST (traced 2026-09-23; this replaces the 2026-09-18
//! suspicion this header first carried, which blamed the wrong mechanism).
//! `u8::unchecked_add` is UB on overflow. Core's wrapper body guards it with
//! `assert_unsafe_precondition!(check_language_ub, ..)`, but that branch is
//! DEAD in both tools: `check_language_ub()` folds to `false`, as Kani compiles
//! every `RuntimeChecks` flag. The obligation Kani reports is the wrapper's
//! `_0 = AddUnchecked(_1, _2)` BinOp itself
//! (`codegen_binop_with_overflow_check`). Two encoder paths reach it:
//!
//!  * the fn_inline path REFUSES to inline these wrappers
//!    (`callee_uses_special_arithmetic_handler`, consulted in
//!    `codegen_call_fn_inline.rs`), so the call falls through to
//!    `codegen_wrapping_arithmetic` (`step_wrapping.rs`), which emits a real
//!    error rule for overflow. That is the CONTROL harness below. Its
//!    description is still the generic "CHC verification: memory safety"
//!    (`emit_error_rule_for_condition`'s default), not Kani's message.
//!  * the inline WALKER (`codegen_call_virtual_inline/`) walks the wrapper body
//!    when the call sits inside a dyn-dispatched method. It translated the
//!    BinOp as a plain `bvadd` (`translate_binop`) and recorded NO check, so the
//!    host emitted nothing and the dyn rows verified SUCCESSFUL `clean`. The
//!    walker does NOT turn Assert terminators into mere ite guards (it records
//!    each as a real deferred check as well), and this path has no Assert
//!    terminator anyway. Fixed 2026-09-23: the walker records the statement
//!    path's check for the BinOp (`call/inline_shared/rvalue_ub.rs`) with Kani's
//!    class and message, so the dyn rows now FAIL on
//!    "attempt to compute `unchecked_add` which would overflow".
//!
//! WHY THE SHAPE IS WHAT IT IS.
//!  * MEASURED 2026-09-18: a `&OnlyImpl` receiver with one impl produced ZERO
//!    devirtualisation and ZERO walker events at debug -- it was devirtualised
//!    before the encoder ever saw a virtual call, so that shape tests nothing.
//!    The receiver below is therefore the device `drop_dual_d_mixed_vtable.rs`
//!    proved: a SYMBOLIC choice between two impls into a `Box<dyn Adder>`, whose
//!    concrete type is not statically known. That takes the walker's MULTI-IMPL
//!    ITE dispatch (`dispatch_multi_impl_virtual`). `bug_..._single_impl_box`
//!    boxes one impl, but the crate has two, so the encoder sees two candidates
//!    for it too (`impl_count=2` in the 2026-09-23 walker trace) and takes the
//!    constant-vtable short-circuit. NO harness here exercises a true one-impl
//!    path.
//!  * Neither impl is parametric: a parametric sibling would trip
//!    `single_candidate_set_is_incomplete` (missed-bug C) and route to the sound
//!    over-approximation instead of the walker. That is why
//!    `devirt_missed_bug_1.rs` is the WRONG template here.
//!  * NO user assertion guards the overflow. The only obligation in the bug
//!    harness is the `unchecked_add` UB, so a SUCCESSFUL verdict is a missed bug
//!    and cannot be mistaken for a failing user assert.
//!  * The control calls the SAME operation directly. Direct FAILED with dyn
//!    SUCCESSFUL localises the gap to the walker path; BOTH succeeding means the
//!    harness or the lane is at fault, not the walker.
//!  * `u8` keeps the state space small; the corpus rows that motivated this
//!    (`kani/Intrinsics/Count/{ctlz,cttz}.rs`) carry the `u32` spelling
//!    `core::num::<impl u32>::unchecked_add::precondition_check`.
//!
//! Lane scope: CHC only. The mechanism is in the CHC walker; the BMC lane has
//! its own inline machinery that this file has not investigated.
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options --harness-timeout=30s
//!        unchecked_arith_walker_dual.rs

/// Keeps its argument alive through rustc's MIR optimisations, and is
/// obligation-free by inspection. Copied deliberately from
/// `obligation_free_stmt_dual.rs`, which MEASURED the alternative: a pure rvalue
/// whose result nothing reads "is removed by rustc's own MIR optimisations
/// before either the encoder or the walk sees it -- UB is not a side effect",
/// and its first draft emitted ZERO checks for five harnesses as a result.
///
/// NOT `std::hint::black_box`: that is an intrinsic whose MIR the encoder has
/// been observed to lack (`core::std::intrinsics::black_box::<i32>` appears in
/// this corpus's "Stdlib function MIR unavailable" set), so the consumer itself
/// could become an over-approximated call -- a poor foundation for a soundness
/// dual, whose whole point is that nothing in the harness is approximated
/// except the thing under test.
#[inline(never)]
fn sink<T>(_value: T) {}

pub trait Adder {
    fn add_unchecked(&self, a: u8, b: u8) -> u8;
}

/// Two NON-parametric impls. The add is identical in both, so the verdict cannot
/// depend on which one the dispatch picks -- only on whether the UB obligation
/// inside the wrapper body survives the walker.
pub struct AdderA;
pub struct AdderB;

impl Adder for AdderA {
    fn add_unchecked(&self, a: u8, b: u8) -> u8 {
        unsafe { a.unchecked_add(b) }
    }
}

impl Adder for AdderB {
    fn add_unchecked(&self, a: u8, b: u8) -> u8 {
        unsafe { a.unchecked_add(b) }
    }
}

#[kani::proof]
fn bug_unchecked_add_overflow_in_dyn_body() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let obj: Box<dyn Adder> = if kani::any() { Box::new(AdderA) } else { Box::new(AdderB) };
    sink(obj.add_unchecked(a, b));
}

#[kani::proof]
fn bug_unchecked_add_overflow_single_impl_box() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let obj: Box<dyn Adder> = Box::new(AdderA);
    sink(obj.add_unchecked(a, b));
}

#[kani::proof]
fn safe_unchecked_add_assumed_in_dyn_body() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    kani::assume(a < 100);
    kani::assume(b < 100);
    let obj: Box<dyn Adder> = if kani::any() { Box::new(AdderA) } else { Box::new(AdderB) };
    sink(obj.add_unchecked(a, b));
}

#[kani::proof]
fn bug_unchecked_add_overflow_direct_call() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    sink(unsafe { a.unchecked_add(b) });
}
