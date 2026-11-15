// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// NEGATIVE PACK: safe twins of eq_joined_option_false_proof.rs, and the joined
// reference whose two referents differ.
//
// Audit evidence: limits-page/chc-joined-option-eq-false-proof. The must-fail
// file proved `!(a == b)` under --ay-chc because the inlined
// `<Option<T> as PartialEq>::eq` bound a reference's ADDRESS as its referent
// and decoded the tag from pointer bits. The same decode made every TRUE
// `a == b` below fail as [AY:CTREX_CAT:Genuine]. A fix that only stops the
// false proof (a havoc, a refusal) turns these twins into demoted failures;
// a fix that reads the referent turns them green. The differing-referent pair
// pins that the read follows the borrow the path took, not the last borrow the
// encoder translated.
//
// Oracle (per harness):
//   map_result_eq_safe                   -> VERIFICATION:- SUCCESSFUL
//   question_mark_result_eq_safe         -> VERIFICATION:- SUCCESSFUL
//   branch_join_eq_safe                  -> VERIFICATION:- SUCCESSFUL
//   symbolic_branch_join_eq_safe         -> VERIFICATION:- SUCCESSFUL
//   joined_reference_eq_safe             -> VERIFICATION:- SUCCESSFUL
//   joined_reference_differ_eq_safe      -> VERIFICATION:- SUCCESSFUL
//   joined_reference_differ_eq_must_fail -> VERIFICATION:- FAILED (assertion)
//
// Every `_safe` assertion holds on every path, so native Rust never panics on
// them; `joined_reference_differ_eq_must_fail` assumes the path that took `&m`
// and asserts `n`'s value, so it panics on every path it keeps.

fn f(x: Option<u8>) -> Option<u8> {
    let v = x?;
    Some(v + 1)
}

#[kani::proof]
fn map_result_eq_safe() {
    let o: Option<u8> = Some(3);
    assert!(o.map(|x| x + 1) == Some(4));
}

#[kani::proof]
fn question_mark_result_eq_safe() {
    assert!(f(Some(3)) == Some(4));
}

#[kani::proof]
fn branch_join_eq_safe() {
    let b: bool = kani::any();
    let o: Option<u8> = if b { Some(4) } else { Some(4) };
    assert!(o == Some(4));
}

#[kani::proof]
fn symbolic_branch_join_eq_safe() {
    let b: bool = kani::any();
    let v: u8 = kani::any();
    let o: Option<u8> = if b { Some(v) } else { None };
    assert!((o == Some(v)) == b);
}

#[kani::proof]
fn joined_reference_eq_safe() {
    let m = Some(4u8);
    let n = Some(4u8);
    let b: bool = kani::any();
    let r: &Option<u8> = if b { &m } else { &n };
    assert!(*r == Some(4));
}

#[kani::proof]
fn joined_reference_differ_eq_safe() {
    let m = Some(1u8);
    let n = Some(2u8);
    let b: bool = kani::any();
    let r: &Option<u8> = if b { &m } else { &n };
    assert!((*r == Some(1)) == b);
}

#[kani::proof]
fn joined_reference_differ_eq_must_fail() {
    let m = Some(1u8);
    let n = Some(2u8);
    let b: bool = kani::any();
    kani::assume(b);
    let r: &Option<u8> = if b { &m } else { &n };
    assert!(*r == Some(2));
}
