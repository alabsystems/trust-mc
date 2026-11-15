// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// NEGATIVE PACK (review bypass r01): Joined references to promoted constants: const_ref_values / const_ref_discriminants are keyed by the ref local.
//
// Audit evidence: review of m3/chc-joined-option-eq at f1373b8d1 (2026-09-12),
// bypass pack r01. Every `_must_fail` assertion is violated on a path native Rust
// takes; every `_safe` assertion holds on every path. A `SUCCESSFUL` on a `_must_fail`
// harness in either lane is a false proof.
//
// Oracle (per harness):
//   const_scalar_ref_a_must_fail    -> VERIFICATION:- FAILED (assertion)
//   const_scalar_ref_b_must_fail    -> VERIFICATION:- FAILED (assertion)
//   const_scalar_ref_safe           -> VERIFICATION:- SUCCESSFUL
//   const_option_ref_a_must_fail    -> VERIFICATION:- FAILED (assertion)
//   const_option_ref_b_must_fail    -> VERIFICATION:- FAILED (assertion)
//   const_option_ref_safe           -> VERIFICATION:- SUCCESSFUL
//   const_unit_enum_ref_a_must_fail -> VERIFICATION:- FAILED (assertion)
//   const_unit_enum_ref_b_must_fail -> VERIFICATION:- FAILED (assertion)
//   const_unit_enum_ref_safe        -> VERIFICATION:- SUCCESSFUL

#[derive(PartialEq, Clone, Copy)]
enum Color { R, G, Bl }

#[kani::proof]
fn const_scalar_ref_a_must_fail() {
    let b: bool = kani::any();
    let r: &u8 = if b { &1 } else { &2 };
    assert!(*r == 1);
}
#[kani::proof]
fn const_scalar_ref_b_must_fail() {
    let b: bool = kani::any();
    let r: &u8 = if b { &1 } else { &2 };
    assert!(*r == 2);
}
#[kani::proof]
fn const_scalar_ref_safe() {
    let b: bool = kani::any();
    let r: &u8 = if b { &1 } else { &2 };
    assert!((*r == 1) == b);
}
#[kani::proof]
fn const_option_ref_a_must_fail() {
    let b: bool = kani::any();
    let r: &Option<u8> = if b { &Some(1) } else { &Some(2) };
    assert!(*r == Some(1));
}
#[kani::proof]
fn const_option_ref_b_must_fail() {
    let b: bool = kani::any();
    let r: &Option<u8> = if b { &Some(1) } else { &Some(2) };
    assert!(*r == Some(2));
}
#[kani::proof]
fn const_option_ref_safe() {
    let b: bool = kani::any();
    let r: &Option<u8> = if b { &Some(1) } else { &Some(2) };
    assert!((*r == Some(1)) == b);
}
#[kani::proof]
fn const_unit_enum_ref_a_must_fail() {
    let b: bool = kani::any();
    let r: &Color = if b { &Color::R } else { &Color::G };
    assert!(*r == Color::R);
}
#[kani::proof]
fn const_unit_enum_ref_b_must_fail() {
    let b: bool = kani::any();
    let r: &Color = if b { &Color::R } else { &Color::G };
    assert!(*r == Color::G);
}
#[kani::proof]
fn const_unit_enum_ref_safe() {
    let b: bool = kani::any();
    let r: &Color = if b { &Color::R } else { &Color::G };
    assert!((*r == Color::R) == b && *r != Color::Bl);
}
