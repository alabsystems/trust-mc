// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CERTIFICATION DUAL -- a counterexample built on an iterator adapter's
//! fresh value (fix/chc-walker-fail-closed, repair round 3, walker fail-closed
//! review 6 round 3 finding 9; the review's `q2_reduce_shapes.rs`
//! `c1_filter_fold_n4_u4_safe`, and `Wrapping` folds found with finding 4).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, measured 2026-09-28):
//!   c1_filter_fold_n4_u4_safe       -> VERIFICATION:- SUCCESSFUL
//!   c2_filter_fold_nounwind_safe    -> VERIFICATION:- SUCCESSFUL
//!   c3_filter_fold_some_pass_safe   -> VERIFICATION:- SUCCESSFUL
//!   wf1_wrapping_fold_safe          -> VERIFICATION:- SUCCESSFUL
//!   wf1_wrapping_fold_bug           -> VERIFICATION:- FAILED  ('s.0 == 45')
//!   wf3_wrapping_fold_owned_safe    -> VERIFICATION:- SUCCESSFUL
//!
//! MECHANISM UNDER TEST. Where the statement path's reduction and adapter
//! models have no exact term they bind a fresh symbol
//! (`codegen_call_iterator_adapter/helpers.rs`, `fresh_adapter_symbol`). It
//! recorded only `aggregate_encoding_gap`, which the driver never reads, so a
//! counterexample through it was certified Genuine: every safe row here was a
//! false certificate on main. It is an identified sound havoc now
//! (`iter_adapter_symbol_overapprox`): a proof over it stays clean, and a
//! counterexample that reads it is never certified. The safe rows still fail
//! (the fold over a `Filter`, or over a `Wrapping` accumulator, keeps the
//! over-approximation): a false failure, not a false certificate.
use std::num::Wrapping;

#[kani::proof]
#[kani::unwind(4)]
fn c1_filter_fold_n4_u4_safe() {
    let a = [1u8, 2, 3, 4];
    let s = a.iter().filter(|x| **x > 100).fold(0u8, |acc, x| acc.wrapping_add(*x));
    assert!(s == 0);
}

#[kani::proof]
fn c2_filter_fold_nounwind_safe() {
    let a = [1u8, 2, 3, 4];
    let s = a.iter().filter(|x| **x > 100).fold(0u8, |acc, x| acc.wrapping_add(*x));
    assert!(s == 0);
}

#[kani::proof]
fn c3_filter_fold_some_pass_safe() {
    let a = [1u8, 200, 3, 4];
    let s = a.iter().filter(|x| **x > 100).fold(0u8, |acc, x| acc.wrapping_add(*x));
    assert!(s == 200);
}

#[kani::proof]
fn wf1_wrapping_fold_safe() {
    let a = [Wrapping(200u8), Wrapping(100u8), Wrapping(0u8)];
    let s = a.iter().fold(Wrapping(0u8), |x, y| x + y);
    assert!(s.0 == 44);
}

#[kani::proof]
fn wf1_wrapping_fold_bug() {
    let a = [Wrapping(200u8), Wrapping(100u8), Wrapping(0u8)];
    let s = a.iter().fold(Wrapping(0u8), |x, y| x + y);
    assert!(s.0 == 45);
}

#[kani::proof]
fn wf3_wrapping_fold_owned_safe() {
    let a = [Wrapping(200u8), Wrapping(100u8), Wrapping(0u8)];
    let s = a.iter().fold(Wrapping(0u8), |x, y| x + *y);
    assert!(s.0 == 44);
}
