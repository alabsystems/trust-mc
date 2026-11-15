// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// A higher-order enum combinator's result under the DERIVED `PartialEq`, on
// both routes in both lanes.
//
// The defect this pins (`limits-page/chc-joined-option-eq-false-proof`, fixed on
// main by the m3/chc-joined-option-eq campaign, 2026-09-11..13): under
// `--ay-chc` the inlined `<Option<T> as PartialEq>::eq` came back with its
// SwitchInt discriminant folded to a constant and no fallback recorded, so the
// error rule became the constant `false`. Both directions were wrong at once,
// on BOTH routes:
//
//   `Some(2i32).map(|z| z + 1) == None`     SUCCESSFUL   — a false proof
//   `Some(2i32).map(|z| z + 1) == Some(3)`  FAILED, and the counterexample
//                                           certified `[AY:CTREX_CAT:Genuine]`
//
// on the same `v`, while `v.unwrap() == 3` and `matches!(v, Some(3))` both
// verified — an internally inconsistent model. BMC was correct throughout.
//
// These harnesses are the parity-1 third review's reductions, kept because they
// cover shapes `tools/soundness-duals/negative/eq_joined_option_*.rs` does not:
// `Option::and_then`, `Result::map`, a SYMBOLIC payload, f32/f64 payloads
// (where the combinator meets the min/max relation), and the `unwrap()` /
// `matches!` controls that exposed the inconsistency. Ground truth was checked
// natively on the frozen nightly (review3b/gt4.rs, 0 mismatches).
#![allow(unused)]

fn plus_one(x: i32) -> Option<i32> {
    Some(x + 1)
}

fn id_opt(x: Option<i32>) -> Option<i32> {
    x
}

// ---- the combinator results that really hold -------------------------------

#[kani::proof]
fn eqj_map_eq_some_holds() {
    let v = Some(2i32).map(|z| z + 1);
    assert!(v == Some(3));
}

#[kani::proof]
fn eqj_map_eq_var_holds() {
    let v = Some(2i32).map(|z| z + 1);
    let w = Some(3i32);
    assert!(v == w);
}

#[kani::proof]
fn eqj_map_identity_eq_holds() {
    let v = Some(1.0f64).map(|z| z);
    assert!(v == Some(1.0));
}

#[kani::proof]
fn eqj_and_then_eq_holds() {
    let v = Some(2i32).and_then(|z| Some(z + 1));
    assert!(v == Some(3));
}

#[kani::proof]
fn eqj_result_map_eq_holds() {
    let v: Result<i32, ()> = Ok(2i32).map(|z| z + 1);
    assert!(v == Ok(3));
}

#[kani::proof]
fn eqj_map_symbolic_eq_holds() {
    let x: i32 = kani::any();
    kani::assume(x == 2);
    let v = Some(x).map(|z| z + 1);
    assert!(v == Some(3));
}

// The combinator over the FLOAT min/max relation — the shape the review's packs
// M and O found this through (`m64_optionmap_value_holds`,
// `d2_optionmap_min64_value_holds`). `(-2.0).max(1.0)` is 1.0 at both widths.
#[kani::proof]
fn eqj_map_f64_max_eq_holds() {
    let v = Some(-2.0f64).map(|z| z.max(1.0));
    assert!(v == Some(1.0));
}

#[kani::proof]
fn eqj_map_f32_max_eq_holds() {
    let v = Some(-2.0f32).map(|z| z.max(1.0));
    assert!(v == Some(1.0f32));
}

// ---- the controls that were CORRECT while the ones above were wrong --------
// They are what showed the model was internally inconsistent rather than merely
// imprecise, so they stay.

#[kani::proof]
fn eqj_map_unwrap_holds() {
    let v = Some(2i32).map(|z| z + 1);
    assert!(v.unwrap() == 3);
}

#[kani::proof]
fn eqj_map_matches_holds() {
    let v = Some(2i32).map(|z| z + 1);
    assert!(matches!(v, Some(3)));
}

#[kani::proof]
fn eqj_map_is_some_holds() {
    let v = Some(2i32).map(|z| z + 1);
    assert!(v.is_some());
}

#[kani::proof]
fn eqj_no_call_eq_holds() {
    let v = Some(2i32);
    assert!(v == Some(2));
}

#[kani::proof]
fn eqj_constructed_eq_holds() {
    let x = 2i32;
    let v = Some(x + 1);
    assert!(v == Some(3));
}

#[kani::proof]
fn eqj_fn_returns_option_eq_holds() {
    let v = plus_one(2);
    assert!(v == Some(3));
}

#[kani::proof]
fn eqj_fn_id_option_eq_holds() {
    let v = id_opt(Some(3));
    assert!(v == Some(3));
}

#[kani::proof]
fn eqj_tuple_eq_after_map_holds() {
    let v = Some(2i32).map(|z| z + 1);
    let t = (v.unwrap(), 0i32);
    assert!(t == (3, 0));
}

// ---- the refutations: false on every path ----------------------------------
// `eqj_map_eq_none_refuted` is the one that was SUCCESSFUL — a missed bug with
// no float and no dyn dispatch anywhere in it.

#[kani::proof]
fn eqj_map_eq_none_refuted() {
    let v = Some(2i32).map(|z| z + 1);
    assert!(v == None);
}

#[kani::proof]
fn eqj_map_eq_wrong_payload_refuted() {
    let v = Some(2i32).map(|z| z + 1);
    assert!(v == Some(4));
}

#[kani::proof]
fn eqj_and_then_eq_none_refuted() {
    let v = Some(2i32).and_then(|z| Some(z + 1));
    assert!(v == None);
}

#[kani::proof]
fn eqj_result_map_eq_wrong_refuted() {
    let v: Result<i32, ()> = Ok(2i32).map(|z| z + 1);
    assert!(v == Ok(4));
}

#[kani::proof]
fn eqj_map_f64_max_eq_wrong_refuted() {
    let v = Some(-2.0f64).map(|z| z.max(1.0));
    assert!(v == Some(-2.0));
}
