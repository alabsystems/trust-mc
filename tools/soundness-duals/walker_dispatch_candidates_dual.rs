// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (missed-bug tracker, closed by design 3) -- a dyn call whose CANDIDATE
//! SET the CHC walker gets wrong: a candidate it cannot walk is dropped
//! silently, or the candidate that runs is never a candidate at all.
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3; see the manifest entry):
//!   bug_multi_impl_big_body        -> VERIFICATION:- FAILED  ('attempt to compute `unchecked_add` which would overflow')
//!   safe_multi_impl_big_body       -> VERIFICATION:- SUCCESSFUL
//!   bug_multi_impl_small_body      -> VERIFICATION:- FAILED  (same check; control)
//!   bug_ref_closure_then_fnitem    -> VERIFICATION:- FAILED  (same check)
//!   bug_ref_fnitem_then_closure    -> VERIFICATION:- FAILED  (same check)
//!   bug_closure_then_fnitem_value  -> VERIFICATION:- FAILED  ('assertion failed: r == a.wrapping_add(b)')
//!   bug_ref_two_fnitems            -> VERIFICATION:- FAILED  ('attempt to compute `unchecked_add` which would overflow'; control)
//!   bug_subtrait_boxed             -> VERIFICATION:- FAILED  (same check)
//!   bug_subtrait_value             -> VERIFICATION:- FAILED  ('assertion failed: r == a.wrapping_mul(b)')
//!
//! STATUS (2026-09-25): closed by design 3 of
//! `docs/chc-hole-fix-designs-2026-09-24.md`. A virtual call dispatches over
//! the receiver's principal trait, whose list the stored vtable ids index; a
//! fn item behind `&dyn Fn` is a candidate; a lone candidate is walked
//! unconditionally only when the harness's dyn-coercion universe (from the
//! reachability collector) says it is the only runtime type; a merge whose
//! arms miss a recorded runtime type, or a runtime-type candidate that cannot
//! be walked, fails closed (`dyn_dispatch_scope.rs`,
//! `kani_middle/dyn_universe.rs`). Every bug_ row FAILS;
//! safe_multi_impl_big_body is the predicted known-red false failure.
//!
//! MECHANISMS (as found; main 25905b622 still missed each the same way):
//! 1. A MULTI-IMPL CANDIDATE THAT FAILS TO WALK. `build_dispatch_ite_chain_impl`
//!    (`codegen_call_virtual_inline/dispatch.rs`) skips an impl whose walk
//!    returns None (here the 16-block inline limit) and records only
//!    `record_aggregate_gap("inline_dispatch_skipped_impls")`, a
//!    counterexample-classification counter, not a FailClose; the skipped vtable
//!    id falls to the merge's fresh default arm with no checks
//!    (`bug_multi_impl_big_body`). With a body small enough to walk the same
//!    dispatch is caught (`bug_multi_impl_small_body`). The Fn-trait merge fails
//!    closed on the same event (`fn_trait_dispatch_unguarded_candidate`).
//! 2. A CLOSURE AND A FN ITEM BEHIND ONE `&dyn Fn`. `try_dispatch_call_closure`
//!    runs first; `callable_body_matches_expected_params`
//!    (`codegen_call_closure/dyn_callable_resolver.rs`) accepts only bodies with
//!    a closure's environment slot, so the fn item is filtered out, the lone
//!    closure is "unique" and walked unconditionally, and the guarded Fn-trait
//!    merge is never reached. It proves an ordinary false assertion too
//!    (`bug_closure_then_fnitem_value`). Two fn items are caught
//!    (`bug_ref_two_fnitems`).
//! 3. A `Box<dyn SubTrait>` WHERE `SubTrait: Fn`. The call is `Fn::call`, and
//!    `resolve_unique_dyn_callable_body` collects candidates for `Fn` without
//!    checking that the receiver's dyn principal IS `Fn`; Phase 2 of
//!    `collect_dyn_trait_candidates` (`dyn_coercion.rs`) keeps only coercions to
//!    `dyn Fn`, so one unrelated closure coerced to `dyn Fn` becomes the unique
//!    callable and is walked in place of the real one (`bug_subtrait_boxed`,
//!    and with no UB at all `bug_subtrait_value`).
//!
//! Promoted from the 2026-09-24 adversarial review (merges-and-dispatch lens,
//! merge/big_body.rs, dynfn_fnitem.rs and dynfn_super.rs; verifier probes
//! small_ctl.rs, plain.rs and variants.rs).
//!
//! Lane scope: CHC only.
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options --harness-timeout=30s walker_dispatch_candidates_dual.rs

/// Keeps its argument alive through rustc's MIR optimisations and is
/// obligation-free by inspection (see `unchecked_arith_walker_dual.rs`).
#[inline(never)]
fn sink<T>(_value: T) {}

pub trait Op2 {
    fn op2(&self, a: u8, b: u8) -> u8;
}
pub struct Small;
pub struct Big;
pub struct BigSafe;
pub struct SmallUb;
impl Op2 for Small {
    fn op2(&self, a: u8, b: u8) -> u8 {
        a.wrapping_add(b)
    }
}
impl Op2 for Big {
    fn op2(&self, a: u8, b: u8) -> u8 {
        let mut r = a;
        if b == 1 { r ^= 1; }
        if b == 2 { r ^= 2; }
        if b == 3 { r ^= 3; }
        if b == 4 { r ^= 4; }
        if b == 5 { r ^= 5; }
        if b == 6 { r ^= 6; }
        if b == 7 { r ^= 7; }
        if b == 8 { r ^= 8; }
        if b == 9 { r ^= 9; }
        if b == 10 { r ^= 10; }
        if b == 11 { r ^= 11; }
        if b == 12 { r ^= 12; }
        if b == 13 { r ^= 13; }
        if b == 14 { r ^= 14; }
        unsafe { r.unchecked_add(b) }
    }
}
impl Op2 for BigSafe {
    fn op2(&self, a: u8, b: u8) -> u8 {
        let mut r = a;
        if b == 1 { r ^= 1; }
        if b == 2 { r ^= 2; }
        if b == 3 { r ^= 3; }
        if b == 4 { r ^= 4; }
        if b == 5 { r ^= 5; }
        if b == 6 { r ^= 6; }
        if b == 7 { r ^= 7; }
        if b == 8 { r ^= 8; }
        if b == 9 { r ^= 9; }
        if b == 10 { r ^= 10; }
        if b == 11 { r ^= 11; }
        if b == 12 { r ^= 12; }
        if b == 13 { r ^= 13; }
        if b == 14 { r ^= 14; }
        r.wrapping_add(b)
    }
}
impl Op2 for SmallUb {
    fn op2(&self, a: u8, b: u8) -> u8 {
        unsafe { a.unchecked_add(b) }
    }
}

fn add_safe(x: u8, y: u8) -> u8 {
    x.wrapping_add(y)
}
fn add_ub(x: u8, y: u8) -> u8 {
    unsafe { x.unchecked_add(y) }
}
fn sub_item(x: u8, y: u8) -> u8 {
    x.wrapping_sub(y)
}

pub trait MyFn: Fn(u8, u8) -> u8 {}
impl<T: Fn(u8, u8) -> u8> MyFn for T {}

#[kani::proof]
fn bug_multi_impl_big_body() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let o: Box<dyn Op2> = if kani::any() { Box::new(Small) } else { Box::new(Big) };
    sink(o.op2(a, b));
}

#[kani::proof]
fn safe_multi_impl_big_body() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let o: Box<dyn Op2> = if kani::any() { Box::new(Small) } else { Box::new(BigSafe) };
    sink(o.op2(a, b));
}

#[kani::proof]
fn bug_multi_impl_small_body() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let o: Box<dyn Op2> = if kani::any() { Box::new(Small) } else { Box::new(SmallUb) };
    sink(o.op2(a, b));
}

#[kani::proof]
fn bug_ref_closure_then_fnitem() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let c1 = |x: u8, y: u8| x.wrapping_add(y);
    let f: &dyn Fn(u8, u8) -> u8 = if kani::any() { &c1 } else { &add_ub };
    sink(f(a, b));
}

#[kani::proof]
fn bug_ref_fnitem_then_closure() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let c1 = |x: u8, y: u8| x.wrapping_add(y);
    let f: &dyn Fn(u8, u8) -> u8 = if kani::any() { &add_ub } else { &c1 };
    sink(f(a, b));
}

#[kani::proof]
fn bug_closure_then_fnitem_value() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    kani::assume(b != 0);
    let c1 = |x: u8, y: u8| x.wrapping_add(y);
    let f: &dyn Fn(u8, u8) -> u8 = if kani::any() { &c1 } else { &sub_item };
    let r = f(a, b);
    assert!(r == a.wrapping_add(b));
    sink(r);
}

#[kani::proof]
fn bug_ref_two_fnitems() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let f: &dyn Fn(u8, u8) -> u8 = if kani::any() { &add_safe } else { &add_ub };
    sink(f(a, b));
}

#[kani::proof]
fn bug_subtrait_boxed() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let f: Box<dyn MyFn> = if kani::any() {
        Box::new(|x: u8, y: u8| x.wrapping_add(y))
    } else {
        Box::new(|x: u8, y: u8| unsafe { x.unchecked_add(y) })
    };
    let d: Box<dyn Fn(u8, u8) -> u8> = Box::new(|x: u8, y: u8| x.wrapping_mul(y));
    sink(d);
    sink(f(a, b));
}

#[kani::proof]
fn bug_subtrait_value() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let f: Box<dyn MyFn> = Box::new(|x: u8, y: u8| x.wrapping_add(y));
    let d: Box<dyn Fn(u8, u8) -> u8> = Box::new(|x: u8, y: u8| x.wrapping_mul(y));
    sink(d);
    let r = f(a, b);
    assert!(r == a.wrapping_mul(b));
}
