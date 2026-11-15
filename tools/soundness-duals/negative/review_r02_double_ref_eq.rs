// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// NEGATIVE PACK (review bypass r02): `==` one reference level up: <&Option<u8> as PartialEq>::eq and &&T parameters.
//
// Audit evidence: review of m3/chc-joined-option-eq at f1373b8d1 (2026-09-12),
// bypass pack r02. Every `_must_fail` assertion is violated on a path native Rust
// takes; every `_safe` assertion holds on every path. A `SUCCESSFUL` on a `_must_fail`
// harness in either lane is a false proof.
//
// Oracle (per harness):
//   double_ref_eq_must_fail        -> VERIFICATION:- FAILED (assertion)
//   double_ref_eq_safe             -> VERIFICATION:- SUCCESSFUL
//   ref_ref_param_must_fail        -> VERIFICATION:- FAILED (assertion)
//   ref_ref_param_safe             -> VERIFICATION:- SUCCESSFUL
//   generic_ref_to_ref_must_fail   -> VERIFICATION:- FAILED (assertion)
//   generic_ref_to_ref_safe        -> VERIFICATION:- SUCCESSFUL
//   double_ref_refjoin_a_must_fail -> VERIFICATION:- FAILED (assertion)
//   double_ref_refjoin_b_must_fail -> VERIFICATION:- FAILED (assertion)
//   double_ref_refjoin_safe        -> VERIFICATION:- SUCCESSFUL

fn hit2(r: &&Option<u8>) -> bool {
    **r == Some(4)
}
fn same<T: PartialEq>(x: &T, y: &T) -> bool {
    x == y
}

#[kani::proof]
fn double_ref_eq_must_fail() {
    let b: bool = kani::any();
    let o: Option<u8> = if b { Some(4) } else { Some(4) };
    let r = &o;
    assert!(!(r == &Some(4)));
}
#[kani::proof]
fn double_ref_eq_safe() {
    let b: bool = kani::any();
    let o: Option<u8> = if b { Some(4) } else { Some(4) };
    let r = &o;
    assert!(r == &Some(4));
}
#[kani::proof]
fn ref_ref_param_must_fail() {
    let b: bool = kani::any();
    let o: Option<u8> = if b { Some(4) } else { Some(4) };
    let r = &o;
    assert!(!hit2(&r));
}
#[kani::proof]
fn ref_ref_param_safe() {
    let b: bool = kani::any();
    let o: Option<u8> = if b { Some(4) } else { Some(4) };
    let r = &o;
    assert!(hit2(&r));
}
#[kani::proof]
fn generic_ref_to_ref_must_fail() {
    let b: bool = kani::any();
    let o: Option<u8> = if b { Some(4) } else { Some(4) };
    let c = Some(4u8);
    let r: &Option<u8> = &o;
    let s: &Option<u8> = &c;
    assert!(!same(&r, &s));
}
#[kani::proof]
fn generic_ref_to_ref_safe() {
    let b: bool = kani::any();
    let o: Option<u8> = if b { Some(4) } else { Some(4) };
    let c = Some(4u8);
    let r: &Option<u8> = &o;
    let s: &Option<u8> = &c;
    assert!(same(&r, &s));
}
#[kani::proof]
fn double_ref_refjoin_a_must_fail() {
    let m = Some(1u8);
    let n = Some(2u8);
    let b: bool = kani::any();
    let r: &Option<u8> = if b { &m } else { &n };
    assert!(r == &Some(1));
}
#[kani::proof]
fn double_ref_refjoin_b_must_fail() {
    let m = Some(1u8);
    let n = Some(2u8);
    let b: bool = kani::any();
    let r: &Option<u8> = if b { &m } else { &n };
    assert!(r == &Some(2));
}
#[kani::proof]
fn double_ref_refjoin_safe() {
    let m = Some(1u8);
    let n = Some(2u8);
    let b: bool = kani::any();
    let r: &Option<u8> = if b { &m } else { &n };
    assert!((r == &Some(1)) == b);
}
