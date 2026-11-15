// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// NEGATIVE PACK (review bypass r17): Aggregates whose REFERENCE field differs per producer (field_sources keyed by aggregate local).
//
// Audit evidence: review of m3/chc-joined-option-eq at f1373b8d1 (2026-09-12),
// bypass pack r17. Every `_must_fail` assertion is violated on a path native Rust
// takes; every `_safe` assertion holds on every path. A `SUCCESSFUL` on a `_must_fail`
// harness in either lane is a false proof.
//
// Oracle (per harness):
//   struct_scalar_ref_field_a_must_fail    -> VERIFICATION:- FAILED (assertion)
//   struct_scalar_ref_field_b_must_fail    -> VERIFICATION:- FAILED (assertion)
//   struct_scalar_ref_field_safe           -> VERIFICATION:- SUCCESSFUL
//   tuple_ref_field_a_must_fail            -> VERIFICATION:- FAILED (assertion)
//   tuple_ref_field_b_must_fail            -> VERIFICATION:- FAILED (assertion)
//   tuple_ref_field_safe                   -> VERIFICATION:- SUCCESSFUL
//   option_ref_payload_join_a_must_fail    -> VERIFICATION:- FAILED (assertion)
//   option_ref_payload_join_b_must_fail    -> VERIFICATION:- FAILED (assertion)
//   option_ref_payload_join_safe           -> VERIFICATION:- SUCCESSFUL
//   struct_ref_field_mut_write_b_must_fail -> VERIFICATION:- FAILED (assertion)
//   struct_ref_field_mut_write_safe        -> VERIFICATION:- SUCCESSFUL

struct HS<'a> {
    r: &'a u8,
}
#[kani::proof]
fn struct_scalar_ref_field_a_must_fail() {
    let m = 1u8;
    let n = 2u8;
    let b: bool = kani::any();
    let h = if b { HS { r: &m } } else { HS { r: &n } };
    assert!(*h.r == 1);
}
#[kani::proof]
fn struct_scalar_ref_field_b_must_fail() {
    let m = 1u8;
    let n = 2u8;
    let b: bool = kani::any();
    let h = if b { HS { r: &m } } else { HS { r: &n } };
    assert!(*h.r == 2);
}
#[kani::proof]
fn struct_scalar_ref_field_safe() {
    let m = 1u8;
    let n = 2u8;
    let b: bool = kani::any();
    let h = if b { HS { r: &m } } else { HS { r: &n } };
    assert!((*h.r == 1) == b);
}
#[kani::proof]
fn tuple_ref_field_a_must_fail() {
    let m = 1u8;
    let n = 2u8;
    let b: bool = kani::any();
    let t: (&u8, u8) = if b { (&m, 0) } else { (&n, 0) };
    assert!(*t.0 == 1);
}
#[kani::proof]
fn tuple_ref_field_b_must_fail() {
    let m = 1u8;
    let n = 2u8;
    let b: bool = kani::any();
    let t: (&u8, u8) = if b { (&m, 0) } else { (&n, 0) };
    assert!(*t.0 == 2);
}
#[kani::proof]
fn tuple_ref_field_safe() {
    let m = 1u8;
    let n = 2u8;
    let b: bool = kani::any();
    let t: (&u8, u8) = if b { (&m, 0) } else { (&n, 0) };
    assert!((*t.0 == 1) == b);
}
#[kani::proof]
fn option_ref_payload_join_a_must_fail() {
    let m = 1u8;
    let n = 2u8;
    let b: bool = kani::any();
    let o: Option<&u8> = if b { Some(&m) } else { Some(&n) };
    if let Some(r) = o {
        assert!(*r == 1);
    }
}
#[kani::proof]
fn option_ref_payload_join_b_must_fail() {
    let m = 1u8;
    let n = 2u8;
    let b: bool = kani::any();
    let o: Option<&u8> = if b { Some(&m) } else { Some(&n) };
    if let Some(r) = o {
        assert!(*r == 2);
    }
}
#[kani::proof]
fn option_ref_payload_join_safe() {
    let m = 1u8;
    let n = 2u8;
    let b: bool = kani::any();
    let o: Option<&u8> = if b { Some(&m) } else { Some(&n) };
    if let Some(r) = o {
        assert!((*r == 1) == b);
    } else {
        assert!(false);
    }
}
#[kani::proof]
fn struct_ref_field_mut_write_b_must_fail() {
    let mut m = 1u8;
    let mut n = 2u8;
    let b: bool = kani::any();
    {
        let h = if b { (&mut m, 0u8) } else { (&mut n, 0u8) };
        *h.0 = 9;
    }
    assert!(n == 9);
}
#[kani::proof]
fn struct_ref_field_mut_write_safe() {
    let mut m = 1u8;
    let mut n = 2u8;
    let b: bool = kani::any();
    {
        let h = if b { (&mut m, 0u8) } else { (&mut n, 0u8) };
        *h.0 = 9;
    }
    assert!((m == 9) == b && (n == 9) != b);
}
