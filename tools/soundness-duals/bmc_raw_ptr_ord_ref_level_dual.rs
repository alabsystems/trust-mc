// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Oracle (per harness, BMC lane; Kani 0.67.0 semantics):
//   safe_cmp_through_generic_ref       -> VERIFICATION:- SUCCESSFUL
//   bug_cmp_claimed_greater            -> VERIFICATION:- FAILED (assertion)
//   safe_min_max_through_generic       -> VERIFICATION:- SUCCESSFUL
//   bug_max_claimed_smaller            -> VERIFICATION:- FAILED (assertion)
//   safe_clamp_through_generic         -> VERIFICATION:- SUCCESSFUL
//
// WHY THIS FILE EXISTS. `<*const T as Ord>::cmp(&self, &other)` compares the
// POINTERS, one reference level below its arguments. Inside an inlined generic
// helper the BMC lane took `&smaller` / `&bigger` — the addresses of the two
// pointer VARIABLES, fresh unrelated stack symbols — and ordered those, so
// kani/PointerComparison/ptr_comparison.rs::check_thin_ptr failed
// `smaller.cmp(&bigger) == Ordering::Less` certified Genuine on main 1a1cb3865.

use std::cmp::Ordering;

fn cmp_via_ref<T: ?Sized>(smaller: *const T, bigger: *const T) -> Ordering {
    smaller.cmp(&bigger)
}

fn max_via_generic<T: ?Sized>(a: *const T, b: *const T) -> *const T {
    a.max(b)
}

fn min_via_generic<T: ?Sized>(a: *const T, b: *const T) -> *const T {
    a.min(b)
}

fn clamp_via_generic<T: ?Sized>(v: *const T, lo: *const T, hi: *const T) -> *const T {
    v.clamp(lo, hi)
}

#[kani::proof]
fn safe_cmp_through_generic_ref() {
    let array = [0u8; 10];
    let first: *const u8 = &array[0];
    let second: *const u8 = &array[5];
    assert_eq!(cmp_via_ref(first, second), Ordering::Less);
    assert_eq!(cmp_via_ref(second, first), Ordering::Greater);
    assert_eq!(cmp_via_ref(first, first), Ordering::Equal);
}

#[kani::proof]
fn bug_cmp_claimed_greater() {
    let array = [0u8; 10];
    let first: *const u8 = &array[0];
    let second: *const u8 = &array[5];
    assert_eq!(cmp_via_ref(first, second), Ordering::Greater);
}

#[kani::proof]
fn safe_min_max_through_generic() {
    let array = [0u8; 10];
    let first: *const u8 = &array[0];
    let second: *const u8 = &array[5];
    assert_eq!(max_via_generic(first, second), second);
    assert_eq!(min_via_generic(second, first), first);
}

#[kani::proof]
fn bug_max_claimed_smaller() {
    let array = [0u8; 10];
    let first: *const u8 = &array[0];
    let second: *const u8 = &array[5];
    assert_eq!(max_via_generic(first, second), first);
}

#[kani::proof]
fn safe_clamp_through_generic() {
    let array = [0u8; 10];
    let lo: *const u8 = &array[0];
    let mid: *const u8 = &array[5];
    let hi: *const u8 = &array[9];
    assert_eq!(clamp_via_generic(mid, lo, hi), mid);
    assert_eq!(clamp_via_generic(hi, lo, mid), mid);
}
