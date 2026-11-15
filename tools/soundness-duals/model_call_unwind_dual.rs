// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (both directions) -- a std call a MODEL replaces, under a
//! declared unwind bound smaller than the std loop's trip count
//! (fix/chc-walker-fail-closed, repair round 4: the class of walker
//! fail-closed review 6 round 3 finding 6, whose instance was the
//! string-iterator rewrite pass).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, measured 2026-10-01):
//!   u2_vec_sort_u2_bug           -> VERIFICATION:- FAILED  ('unwinding assertion loop 0')
//!   u2_vec_sort_u6_safe          -> VERIFICATION:- SUCCESSFUL
//!   u3_vec_retain_u2_bug         -> VERIFICATION:- FAILED  ('unwinding assertion loop 0')
//!   u3_vec_retain_u8_safe        -> VERIFICATION:- SUCCESSFUL
//!   u4_vec_dedup_u2_bug          -> VERIFICATION:- FAILED  ('unwinding assertion loop 1')
//!   u4_vec_dedup_u8_safe         -> VERIFICATION:- SUCCESSFUL
//!   u5_iter_eq_u2_bug            -> VERIFICATION:- FAILED  ('unwinding assertion loop 0')
//!   u5_iter_eq_u7_safe           -> VERIFICATION:- SUCCESSFUL
//!   u6_vec_contains_u2_bug       -> VERIFICATION:- FAILED  ('unwinding assertion loop 0')
//!   u6_vec_contains_u8_safe      -> VERIFICATION:- SUCCESSFUL
//!   w1_vec_push_len_u2_safe      -> VERIFICATION:- SUCCESSFUL
//!
//! MECHANISM UNDER TEST. A stub or pre-inline model replaces the std code of
//! `Vec::contains`, `sort`, `retain`, `dedup` and `Iterator::eq`, and with it
//! the loop Kani unwinds: under `#[kani::unwind(2)]` every bug row verified
//! clean on main (CHC: u2, u3, u4, u5, u6; BMC: u6; the array form of
//! `contains`, CHC only, is `model_call_unwind_slice_dual.rs`). A modelled call whose
//! callee may loop (`obligation_free_walk::instance_may_loop`) now states
//! Kani's unwinding assertion, uncertified (CHC `codegen_call.rs`
//! `model_call_unwinding_check`; BMC `terminator.rs`
//! `bmc_model_call_unwinding_check`, fail-closed), under a declared bound with
//! unwinding assertions on. The `_safe` rows with a large enough bound are the
//! measured precision cost; `Vec::push` runs no loop and keeps its proof.

#[kani::proof]
#[kani::unwind(2)]
fn u2_vec_sort_u2_bug() {
    let mut v = vec![3u8, 1, 2, kani::any()];
    v.sort();
}

#[kani::proof]
#[kani::unwind(6)]
fn u2_vec_sort_u6_safe() {
    let mut v = vec![3u8, 1, 2, kani::any()];
    v.sort();
}

#[kani::proof]
#[kani::unwind(2)]
fn u3_vec_retain_u2_bug() {
    let mut v = vec![1u8, 2, 3, 4, 5, 6];
    let x: u8 = kani::any();
    v.retain(|y| *y != x);
}

#[kani::proof]
#[kani::unwind(8)]
fn u3_vec_retain_u8_safe() {
    let mut v = vec![1u8, 2, 3, 4, 5, 6];
    let x: u8 = kani::any();
    v.retain(|y| *y != x);
}

#[kani::proof]
#[kani::unwind(2)]
fn u4_vec_dedup_u2_bug() {
    let mut v = vec![1u8, 1, 2, 3, 3, kani::any()];
    v.dedup();
}

#[kani::proof]
#[kani::unwind(8)]
fn u4_vec_dedup_u8_safe() {
    let mut v = vec![1u8, 1, 2, 3, 3, kani::any()];
    v.dedup();
}

#[kani::proof]
#[kani::unwind(2)]
fn u5_iter_eq_u2_bug() {
    let a = [1u8, 2, 3, 4, 5];
    let b = [1u8, 2, 3, 4, kani::any()];
    let _ = a.iter().eq(b.iter());
}

#[kani::proof]
#[kani::unwind(7)]
fn u5_iter_eq_u7_safe() {
    let a = [1u8, 2, 3, 4, 5];
    let b = [1u8, 2, 3, 4, kani::any()];
    let _ = a.iter().eq(b.iter());
}

#[kani::proof]
#[kani::unwind(2)]
fn u6_vec_contains_u2_bug() {
    let x: u8 = kani::any();
    let v = vec![1u8, 2, 3, 4, 5, 6];
    let _ = v.contains(&x);
}

#[kani::proof]
#[kani::unwind(8)]
fn u6_vec_contains_u8_safe() {
    let x: u8 = kani::any();
    let v = vec![1u8, 2, 3, 4, 5, 6];
    let _ = v.contains(&x);
}

#[kani::proof]
#[kani::unwind(2)]
fn w1_vec_push_len_u2_safe() {
    let mut v: Vec<u8> = Vec::new();
    v.push(1);
    v.push(2);
    v.push(3);
    assert!(v.len() == 3);
}
