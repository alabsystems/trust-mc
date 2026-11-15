// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// NEGATIVE PACK: a SHIFTED sub-slice handed to a whole-slice model, in the BMC
// lane.
//
// The BMC lane materializes a backing shifted by the sub-slice's start, so
// every read THROUGH the view is exact. A model that reads the SOURCE array by
// another path is not, and the CHC lane's `subslice_consumer_fail_closed` had
// no BMC counterpart: `let a = [1u8,2,3,4]; let s = &a[1..3];
// assert!(s.contains(&2) && s.contains(&3))` — true in real Rust, since s is
// [2,3] — was FAILED [AY:CTREX_CAT:Genuine] in bmc. Found by the third
// adversarial review (2026-09-14); red on origin/main too.
//
// Oracle (per harness):
//   *_must_fail   -> VERIFICATION:- FAILED; never SUCCESSFUL
//   *_safe        -> never a Genuine counterexample

#[kani::proof]
fn sub_contains_safe() {
    let a = [1u8, 2, 3, 4];
    let s = &a[1..3]; // [2, 3]
    assert!(s.contains(&2) && s.contains(&3));
}

#[kani::proof]
fn sub_contains_must_fail() {
    let a = [1u8, 2, 3, 4];
    let s = &a[1..3];
    assert!(s.contains(&1)); // truth: no
}

#[kani::proof]
fn sub_starts_with_safe() {
    let a = [1u8, 2, 3, 4];
    let s = &a[1..3];
    assert!(s.starts_with(&[2u8]));
}

#[kani::proof]
fn sub_starts_with_must_fail() {
    let a = [1u8, 2, 3, 4];
    let s = &a[1..3];
    assert!(s.starts_with(&[1u8])); // truth: no
}

#[kani::proof]
fn sub_copy_from_slice_must_fail() {
    let src = [1u8, 2, 3, 4];
    let mut dst = [0u8; 2];
    dst.copy_from_slice(&src[1..3]); // [2, 3]
    assert!(dst[0] == 1); // truth: 2
}

// --- over-correction guards: the routes that DO read the shifted backing ---

#[kani::proof]
fn sub_index_read_safe() {
    let a = [1u8, 2, 3, 4];
    let s = &a[1..3];
    assert!(s.len() == 2 && s[0] == 2 && s[1] == 3);
}

#[kani::proof]
fn sub_index_read_must_fail() {
    let a = [1u8, 2, 3, 4];
    let s = &a[1..3];
    assert!(s[0] == 1); // truth: 2
}

#[kani::proof]
fn sub_iter_sum_safe() {
    let a = [1u8, 2, 3, 4];
    let s = &a[1..3];
    let total: u8 = s.iter().fold(0u8, |acc, v| acc + *v);
    assert!(total == 5);
}

#[kani::proof]
fn zero_start_view_contains_safe() {
    // A view that starts at 0 shares the source array and must stay exact.
    let a = [1u8, 2, 3, 4];
    let s = &a[..2];
    assert!(s.contains(&1) && s.contains(&2));
}
