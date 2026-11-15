// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (missed-bug tripwire) -- checks inside a closure body walked
//! by a VALUE-ONLY consumer: `Iterator::fold` replay and `kani::any_where`.
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3; see the manifest entry):
//!   bug_fold_unchecked_add   -> VERIFICATION:- FAILED  ('attempt to compute `unchecked_add` which would overflow')
//!   bug_fold_plain_add       -> VERIFICATION:- FAILED  ('attempt to add with overflow')
//!   bug_fold_user_assert     -> VERIFICATION:- FAILED  ('assertion failed: x != 7')
//!   bug_any_where_unchecked  -> VERIFICATION:- FAILED  ('attempt to compute `unchecked_add` which would overflow')
//!   bug_any_where_plain_add  -> VERIFICATION:- FAILED  ('attempt to add with overflow')
//!   safe_fold_unchecked_add  -> VERIFICATION:- SUCCESSFUL
//!   safe_any_where_pred      -> VERIFICATION:- SUCCESSFUL
//!
//! MECHANISM UNDER TEST. `translate_closure_inline_body` walks the closure and
//! returns only its VALUE; its consumers (the `any_where` predicate lowering,
//! `fold` replay, the map/collect templates, `RefCell::replace_with`) dropped
//! the walk's `deferred_checks`, and every bug row verified SUCCESSFUL clean --
//! not only the new walker BinOp checks but the MIR Assert of a plain `acc + x`
//! and a user `assert!` too (the `fold` fallback through the quantifier
//! closure-body walk dropped its no-panic guard the same way). The `any_where`
//! lowering now EMITS the predicate's checks at its call (the predicate runs on
//! the nondet value, so a check must hold for every value): Genuine, Kani's
//! message. The consumers with no host site for them FAIL CLOSED when a dropped
//! check is not valid on its own (`inline_closure_deferred_checks_dropped`,
//! `iter_fold_closure_guard_dropped`): the fold bug rows become non-certified
//! FAILED, which is sound, and the safe fold is demoted too (the precision
//! cost, tracked on its row). `bug_any_where_plain_add` is still missed, by a
//! different mechanism (E: its captured `k` is not found, the Assert condition
//! is untranslatable and assumed to pass), tracked known-red.
//!
//! Lane scope: CHC only.
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options --harness-timeout=30s walker_value_only_closure_dual.rs

/// Keeps its argument alive through rustc's MIR optimisations and is
/// obligation-free by inspection (see `unchecked_arith_walker_dual.rs`).
#[inline(never)]
fn sink<T>(_value: T) {}

#[kani::proof]
fn bug_fold_unchecked_add() {
    let arr: [u8; 2] = [kani::any(), kani::any()];
    let s = arr.iter().fold(0u8, |acc, &x| unsafe { acc.unchecked_add(x) });
    sink(s);
}

#[kani::proof]
fn bug_fold_plain_add() {
    let arr: [u8; 2] = [kani::any(), kani::any()];
    let s = arr.iter().fold(0u8, |acc, &x| acc + x);
    sink(s);
}

#[kani::proof]
fn bug_fold_user_assert() {
    let arr: [u8; 2] = [kani::any(), kani::any()];
    let s = arr.iter().fold(0u8, |acc, &x| {
        assert!(x != 7);
        acc.wrapping_add(x)
    });
    sink(s);
}

#[kani::proof]
fn bug_any_where_unchecked() {
    let v: u8 = kani::any_where(|x: &u8| unsafe { x.unchecked_add(200) } > 10);
    sink(v);
}

#[kani::proof]
fn bug_any_where_plain_add() {
    let k: u8 = kani::any();
    let v: u8 = kani::any_where(|x: &u8| *x + k > 3);
    sink(v);
}

#[kani::proof]
fn safe_fold_unchecked_add() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    kani::assume(a < 100 && b < 100);
    let arr: [u8; 2] = [a, b];
    let s = arr.iter().fold(0u8, |acc, &x| unsafe { acc.unchecked_add(x) });
    sink(s);
}

#[kani::proof]
fn safe_any_where_pred() {
    let v: u8 = kani::any_where(|x: &u8| *x < 50);
    sink(v);
}
