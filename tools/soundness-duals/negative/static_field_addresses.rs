// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// NEGATIVE PACK: the addresses of two FIELDS of one `static`.
//
// `negative/alloc_id_fields_offsets.rs` and `negative/static_address_identity.rs`
// cover two statics against each other, a static against a stack local, the same
// element twice and element ORDER. What neither covers is two fields of ONE
// static: `static S3: T = T { a: 1, b: 2 }; assert!(!ptr::eq(&S3.a, &S3.b))` was
// FAILED [AY:CTREX_CAT:Genuine] — a constant's address is keyed on its
// allocation, and the field offset did not separate the two borrows (fourth
// adversarial review of m3/soundness-fixes-2, 2026-09-14, defect D8).
//
// Ground truth for every harness here was compiled and run natively on the
// frozen nightly-2025-12-03 rustc.
//
// Oracle (per harness):
//   *_must_fail   -> VERIFICATION:- FAILED; never SUCCESSFUL
//   *_safe        -> never a Genuine counterexample

use std::ptr;

struct T {
    a: u8,
    b: u8,
}

static S3: T = T { a: 1, b: 2 };
static S4: [u8; 2] = [7, 8];

#[kani::proof]
fn static_field_addrs_differ_safe() {
    assert!(!ptr::eq(&S3.a, &S3.b));
}

#[kani::proof]
fn static_field_addrs_same_must_fail() {
    assert!(ptr::eq(&S3.a, &S3.b)); // truth: they differ
}

#[kani::proof]
fn static_elem_addrs_differ_safe() {
    assert!(!ptr::eq(&S4[0], &S4[1]));
}

#[kani::proof]
fn static_same_field_addr_eq_safe() {
    let p = &S3.a;
    let q = &S3.a;
    assert!(ptr::eq(p, q));
}

#[kani::proof]
fn static_field_values_safe() {
    assert!(S3.a == 1 && S3.b == 2);
}
