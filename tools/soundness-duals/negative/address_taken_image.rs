// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// NEGATIVE PACK: the BYTE IMAGE of an address-taken local, after a store into
// one of its sub-places.
//
// Taking `&mut s.x` materializes `s` into byte memory (#1246) and every
// raw-pointer read loads from that image; a store into a FIELD or an ELEMENT
// updated only the register, so the two lanes disagreed about what `s` holds.
// The branch guarded only the nested-place store path, keyed on one handler's
// base name. Found by the third adversarial review (2026-09-14).
//
// NOTE ON UB. Writing to `s.x` while a raw pointer derived from `&mut s.x` is
// live and then READING through that pointer is UB under Stacked Borrows, so
// the write-then-read-through-the-pointer direction is recorded here as a
// PRECISION row only (`*_safe` must not be certified Genuine; no proof rests
// on it). The load-bearing direction is the other one — write THROUGH the
// pointer, read the field — which is well defined and must be exact.
//
// Oracle (per harness):
//   *_must_fail   -> VERIFICATION:- FAILED; never SUCCESSFUL
//   *_safe        -> never a Genuine counterexample

struct S {
    x: u8,
    y: u8,
}

// --- well defined: write through the pointer, read the field --------------

#[kani::proof]
fn raw_store_seen_in_field_must_fail() {
    let mut s = S { x: 0, y: 0 };
    let p: *mut u8 = &mut s.x;
    unsafe { *p = 9 };
    assert!(s.x == 0); // truth: 9
}

#[kani::proof]
fn raw_store_seen_in_field_safe() {
    let mut s = S { x: 0, y: 0 };
    let p: *mut u8 = &mut s.x;
    unsafe { *p = 9 };
    assert!(s.x == 9 && s.y == 0);
}

#[kani::proof]
fn raw_store_seen_in_element_must_fail() {
    let mut a = [0u8, 0];
    let p: *mut u8 = &mut a[1];
    unsafe { *p = 9 };
    assert!(a[1] == 0); // truth: 9
}

#[kani::proof]
fn raw_store_seen_in_element_safe() {
    let mut a = [0u8, 0];
    let p: *mut u8 = &mut a[1];
    unsafe { *p = 9 };
    assert!(a[1] == 9 && a[0] == 0);
}

// --- precision rows: the parent write is UB under Stacked Borrows ----------

#[kani::proof]
fn field_store_seen_through_raw_safe() {
    let mut s = S { x: 0, y: 0 };
    let p: *mut u8 = &mut s.x;
    s.x = 9;
    assert!(unsafe { *p } == 9 && s.y == 0);
}

#[kani::proof]
fn elem_store_seen_through_raw_safe() {
    let mut a = [0u8, 0];
    let p: *mut u8 = &mut a[1];
    a[1] = 9;
    assert!(unsafe { *p } == 9 && a[0] == 0);
}

// --- control: a whole local, which already had a write-back ---------------

#[kani::proof]
fn plain_local_store_seen_through_raw_safe() {
    let mut v = 0u8;
    let p: *mut u8 = &mut v;
    v = 9;
    assert!(unsafe { *p } == 9);
}
