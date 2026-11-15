// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// NEGATIVE PACK: the two directions of `ty_copy_can_go_stale`, the test that
// decides whether a slice VIEW may be modelled as a copy of the referent.
//
// Written while fixing defects 1 and 6 of the adversarial review of
// m3/soundness-fixes-2 (2026-09-13).
//
// The guard used to be `Freeze`, which let a view of POINTERS to cells be
// copied (frozen_views_indirect.rs pins that half). The obvious
// over-correction — refuse to copy any view holding a pointer — is sound but
// costs every ordinary `&[&str]` proof, so the predicate recurses through the
// POINTEE instead. This pack pins both edges:
//
//   * `*_exact_safe`      a view the copy models exactly must still be PROVED;
//                         a fail-closed demotion here is a proof regression.
//   * `*_stale_must_fail` a view the copy CANNOT model must never verify.
//   * `*_stale_safe`      and must never carry a Genuine counterexample.
//
// It also pins the sub-slice length fold: `&a[1..3]` has a constant length, so
// the shifted backing must be built and the view read exactly, rather than
// taking the "no bound on its length" fail-closed exit.
//
// Oracle (per harness):
//   *_must_fail   -> VERIFICATION:- FAILED (assertion); never SUCCESSFUL
//   *_safe        -> never a Genuine counterexample

use std::cell::Cell;

// --- views whose copy is exact: these must stay PROVED ---------------------

#[kani::proof]
fn plain_elems_view_exact_safe() {
    let a = [1u8, 2, 3, 4];
    let v: &[u8] = &a[..];
    assert!(v.len() == 4 && v[0] == 1 && v[3] == 4);
}

#[kani::proof]
fn plain_elems_view_exact_must_fail() {
    let a = [1u8, 2, 3, 4];
    let v: &[u8] = &a[..];
    assert!(v[0] == 2);
}

#[kani::proof]
fn tuple_elems_view_exact_safe() {
    let a = [(1u8, 2u8), (3, 4)];
    let v: &[(u8, u8)] = &a[..];
    assert!(v.len() == 2 && v[1].0 == 3 && v[1].1 == 4);
}

#[kani::proof]
fn tuple_elems_view_exact_must_fail() {
    let a = [(1u8, 2u8), (3, 4)];
    let v: &[(u8, u8)] = &a[..];
    assert!(v[1].0 == 1);
}

#[kani::proof]
fn str_refs_view_exact_safe() {
    // `&str` is a POINTER, but to plain data: the copy is as good as the
    // original, so this view must not fail closed.
    let a: [&str; 2] = ["ab", "cde"];
    let v: &[&str] = &a[..];
    assert!(v.len() == 2 && v[0].len() == 2 && v[1].len() == 3);
}

#[kani::proof]
fn str_refs_view_exact_must_fail() {
    let a: [&str; 2] = ["ab", "cde"];
    let v: &[&str] = &a[..];
    assert!(v[1].len() == 2);
}

#[kani::proof]
fn u8_refs_view_exact_safe() {
    let x = 5u8;
    let y = 6u8;
    let a: [&u8; 2] = [&x, &y];
    let v: &[&u8] = &a[..];
    assert!(*v[0] == 5 && *v[1] == 6);
}

#[kani::proof]
fn u8_refs_view_exact_must_fail() {
    let x = 5u8;
    let y = 6u8;
    let a: [&u8; 2] = [&x, &y];
    let v: &[&u8] = &a[..];
    assert!(*v[1] == 5);
}

// --- the sub-slice length fold: a constant range must be read exactly ------

#[kani::proof]
fn const_range_view_exact_safe() {
    let a = [1u8, 2, 3, 4];
    let s = &a[1..3];
    assert!(s.len() == 2 && s[0] == 2 && s[1] == 3);
}

#[kani::proof]
fn const_range_view_exact_must_fail() {
    let a = [1u8, 2, 3, 4];
    let s = &a[1..3];
    assert!(s[0] == 1);
}

#[kani::proof]
fn const_range_from_view_exact_safe() {
    let a = [1u8, 2, 3, 4];
    let s = &a[2..];
    assert!(s.len() == 2 && s[0] == 3 && s[1] == 4);
}

#[kani::proof]
fn const_range_from_view_exact_must_fail() {
    let a = [1u8, 2, 3, 4];
    let s = &a[2..];
    assert!(s[0] == 1);
}

// --- views whose copy goes stale: these must fail closed -------------------

#[kani::proof]
fn double_ref_cells_stale_safe() {
    // `&&Cell<u8>` is `Freeze` AND its immediate pointee `&Cell<u8>` is
    // `Freeze` too, so only a predicate that recurses through the pointee sees
    // the interior mutability.
    let cells = [Cell::new(1u8), Cell::new(2u8)];
    let refs: [&Cell<u8>; 2] = [&cells[0], &cells[1]];
    let rrefs: [&&Cell<u8>; 2] = [&refs[0], &refs[1]];
    let v: &[&&Cell<u8>] = &rrefs[..];
    cells[1].set(7);
    assert!(v[1].get() == 7);
}

#[kani::proof]
fn double_ref_cells_stale_must_fail() {
    let cells = [Cell::new(1u8), Cell::new(2u8)];
    let refs: [&Cell<u8>; 2] = [&cells[0], &cells[1]];
    let rrefs: [&&Cell<u8>; 2] = [&refs[0], &refs[1]];
    let v: &[&&Cell<u8>] = &rrefs[..];
    cells[1].set(7);
    assert!(v[1].get() == 2);
}

#[kani::proof]
fn cell_elems_stale_safe() {
    // Interior mutability BY VALUE: the copy is stale for the older reason.
    let cells = [Cell::new(1u8), Cell::new(2u8)];
    let v: &[Cell<u8>] = &cells[..];
    cells[0].set(7);
    assert!(v[0].get() == 7);
}

#[kani::proof]
fn cell_elems_stale_must_fail() {
    let cells = [Cell::new(1u8), Cell::new(2u8)];
    let v: &[Cell<u8>] = &cells[..];
    cells[0].set(7);
    assert!(v[0].get() == 1);
}

#[kani::proof]
fn range_view_of_cell_refs_stale_safe() {
    let cells = [Cell::new(1u8), Cell::new(2u8), Cell::new(3u8)];
    let refs: [&Cell<u8>; 3] = [&cells[0], &cells[1], &cells[2]];
    let v: &[&Cell<u8>] = &refs[1..];
    v[0].set(7);
    assert!(cells[1].get() == 7);
}

#[kani::proof]
fn range_view_of_cell_refs_stale_must_fail() {
    let cells = [Cell::new(1u8), Cell::new(2u8), Cell::new(3u8)];
    let refs: [&Cell<u8>; 3] = [&cells[0], &cells[1], &cells[2]];
    let v: &[&Cell<u8>] = &refs[1..];
    v[0].set(7);
    assert!(cells[1].get() == 2);
}
