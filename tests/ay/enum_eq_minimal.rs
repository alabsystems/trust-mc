// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-expect: PROOF

//! Minimal test: enum construction + assert_eq, with and without function calls.

#[derive(PartialEq)]
enum TwoVar {
    Unit,
    Data(bool),
}

#[derive(PartialEq)]
enum ThreeVar {
    Unit,
    Also,
    Data(bool),
}

impl ThreeVar {
    fn create_unit() -> ThreeVar {
        ThreeVar::Unit
    }
    fn create_also() -> ThreeVar {
        ThreeVar::Also
    }
}

#[kani::proof]
fn check_two_var_unit_eq() {
    let x = TwoVar::Unit;
    let y = TwoVar::Unit;
    assert_eq!(x, y);
}

#[kani::proof]
fn check_three_var_unit_eq() {
    let x = ThreeVar::Unit;
    let y = ThreeVar::Unit;
    assert_eq!(x, y);
}

#[kani::proof]
fn check_three_var_also_eq() {
    let x = ThreeVar::Also;
    let y = ThreeVar::Also;
    assert_eq!(x, y);
}

#[kani::proof]
fn check_two_var_data_eq() {
    let x = TwoVar::Data(true);
    let y = TwoVar::Data(true);
    assert_eq!(x, y);
}

// Function call + literal (uses promoted constant) — isolates promoted constant path
#[kani::proof]
fn check_fn_call_unit_eq() {
    let x = ThreeVar::create_unit();
    assert_eq!(x, ThreeVar::Unit);
}

#[kani::proof]
fn check_fn_call_also_eq() {
    let x = ThreeVar::create_also();
    assert_eq!(x, ThreeVar::Also);
}

// Both sides from function calls — no promoted constant
#[kani::proof]
fn check_fn_call_both_sides() {
    let x = ThreeVar::create_unit();
    let y = ThreeVar::create_unit();
    assert_eq!(x, y);
}

// Function call + variable (avoids promoted constant for RHS)
#[kani::proof]
fn check_fn_call_vs_var() {
    let x = ThreeVar::create_unit();
    let y = ThreeVar::Unit;
    assert_eq!(x, y);
}

// No function call, but use raw == with assert! (avoids assert_eq! macro MIR)
#[kani::proof]
fn check_fn_call_raw_eq() {
    let x = ThreeVar::create_unit();
    let y = ThreeVar::Unit;
    assert!(x == y);
}

// Direct construction, but use matches! (known to work)
#[kani::proof]
fn check_fn_call_matches() {
    let x = ThreeVar::create_unit();
    assert!(matches!(x, ThreeVar::Unit));
}

// ZST field variant tests (Part of #3994)
#[derive(PartialEq)]
struct ZeroSized;

#[derive(PartialEq)]
enum WithZST {
    A,
    B(bool),
    C(ZeroSized),
}

// Direct construction: both sides are local variables
#[kani::proof]
fn check_zst_field_vars() {
    let x = WithZST::C(ZeroSized);
    let y = WithZST::C(ZeroSized);
    assert_eq!(x, y);
}

// Direct construction + promoted constant
#[kani::proof]
fn check_zst_field_promoted() {
    let x = WithZST::C(ZeroSized);
    assert_eq!(x, WithZST::C(ZeroSized));
}

// Unit variant in same enum (control: should pass)
#[kani::proof]
fn check_zst_enum_unit() {
    let x = WithZST::A;
    assert_eq!(x, WithZST::A);
}

// 5-variant enum with ZST: unit fields
#[derive(PartialEq)]
enum FiveVar {
    NoFields,
    DataFul(bool),
    UnitFields((), ()),
    ZSTField(ZeroSized),
    ZSTStruct { field: ZeroSized, unit: () },
}

#[kani::proof]
fn check_five_var_no_fields() {
    let x = FiveVar::NoFields;
    assert_eq!(x, FiveVar::NoFields);
}

#[kani::proof]
fn check_five_var_unit_fields() {
    let x = FiveVar::UnitFields((), ());
    assert_eq!(x, FiveVar::UnitFields((), ()));
}

// Diagnostic: raw == (bypasses assert_eq! macro MIR)
#[kani::proof]
fn check_five_var_raw_eq_unit_fields() {
    let x = FiveVar::UnitFields((), ());
    let y = FiveVar::UnitFields((), ());
    assert!(x == y);
}

// Diagnostic: matches! (bypasses PartialEq entirely)
#[kani::proof]
fn check_five_var_matches_unit_fields() {
    let x = FiveVar::UnitFields((), ());
    assert!(matches!(x, FiveVar::UnitFields(_, _)));
}

// Diagnostic: 3-variant enum with UnitFields (same structure, fewer variants)
#[derive(PartialEq)]
enum ThreeVarUF {
    NoFields,
    DataFul(bool),
    UnitFields((), ()),
}

#[kani::proof]
fn check_three_var_uf_unit_fields() {
    let x = ThreeVarUF::UnitFields((), ());
    let y = ThreeVarUF::UnitFields((), ());
    assert!(x == y);
}

// Diagnostic: 4-variant enum
#[derive(PartialEq)]
enum FourVar {
    NoFields,
    DataFul(bool),
    UnitFields((), ()),
    ZSTField(ZeroSized),
}

#[kani::proof]
fn check_four_var_unit_fields() {
    let x = FourVar::UnitFields((), ());
    let y = FourVar::UnitFields((), ());
    assert!(x == y);
}

// Diagnostic: DataFul comparison (payload bool, not ZST)
#[kani::proof]
fn check_five_var_dataful() {
    let x = FiveVar::DataFul(true);
    let y = FiveVar::DataFul(true);
    assert!(x == y);
}

// Diagnostic: match on DataFul (SwitchInt only, no PartialEq)
#[kani::proof]
fn check_five_var_dataful_match() {
    let x = FiveVar::DataFul(true);
    match x {
        FiveVar::DataFul(v) => assert!(v),
        _ => panic!("wrong variant"),
    }
}

// Diagnostic: 5-variant enum with different constructor (Also variant)
// Test if adding variant between NoFields and DataFul changes result
#[derive(PartialEq)]
enum FiveVarAlt {
    NoFields,
    Also,
    DataFul(bool),
    UnitFields((), ()),
    ZSTField(ZeroSized),
}

#[kani::proof]
fn check_five_var_alt_dataful() {
    let x = FiveVarAlt::DataFul(true);
    let y = FiveVarAlt::DataFul(true);
    assert!(x == y);
}
