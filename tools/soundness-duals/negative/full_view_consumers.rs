// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// NEGATIVE PACK (bmc): a FULL slice view, and slice equality, reaching a model
// that reads the SOURCE array rather than the view.
//
// `negative/subslice_consumers_bmc.rs` covers a RANGE-built view with a nonzero
// start. A full view `&a[..]` is not range-built, so nothing recorded it and the
// denylist never saw it; `PartialEq` was in no list at all. Measured on
// m3/soundness-fixes-2 at 547f714bb and on origin/main (fourth adversarial
// review, 2026-09-14, defect M5/D6):
//   `let s = &a[..]; assert!(s.contains(&1) && s.contains(&3))` FAILED
//   [AY:CTREX_CAT:Genuine] on a program with no bug, and so did
//   `let s = &a[1..3]; assert!(s == &[2, 3][..])`.
//
// Ground truth for every harness here was compiled and run natively on the
// frozen nightly-2025-12-03 rustc.
//
// Oracle (per harness):
//   *_must_fail   -> VERIFICATION:- FAILED; never SUCCESSFUL
//   *_safe        -> never a Genuine counterexample

#[kani::proof]
fn full_view_contains_safe() {
    let a = [1u8, 2, 3];
    let s = &a[..];
    assert!(s.contains(&1) && s.contains(&3));
}

#[kani::proof]
fn full_view_contains_must_fail() {
    let a = [1u8, 2, 3];
    let s = &a[..];
    assert!(!s.contains(&1)); // truth: it does contain 1
}

#[kani::proof]
fn sub_eq_slice_safe() {
    let a = [1u8, 2, 3];
    let s = &a[1..3];
    assert!(s == &[2u8, 3][..]);
}

#[kani::proof]
fn sub_eq_slice_must_fail() {
    let a = [1u8, 2, 3];
    let s = &a[1..3];
    assert!(s == &[1u8, 2][..]); // truth: it is [2, 3]
}

#[kani::proof]
fn full_view_eq_safe() {
    let a = [1u8, 2, 3];
    let s = &a[..];
    assert!(s == &[1u8, 2, 3][..]);
}

#[kani::proof]
fn full_view_eq_must_fail() {
    let a = [1u8, 2, 3];
    let s = &a[..];
    assert!(s == &[3u8, 2, 1][..]); // truth: it is [1, 2, 3]
}

#[kani::proof]
fn zero_start_contains_safe() {
    let a = [1u8, 2, 3];
    let s = &a[0..2];
    assert!(s.contains(&1));
}

#[kani::proof]
fn full_view_len_safe() {
    let a = [1u8, 2, 3];
    let s = &a[..];
    assert!(s.len() == 3);
}
