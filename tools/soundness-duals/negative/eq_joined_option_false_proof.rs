// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// NEGATIVE PACK: `==` on an Option that more than one branch assigned.
//
// Audit evidence: limits-page/chc-joined-option-eq-false-proof (triage
// 2026-09-11, ISSUE-limits-page.md section 3). Under --ay-chc the inlined
// `<Option<T> as PartialEq>::eq` came back with its SwitchInt discriminant
// folded to a constant (virtual-inline walker: "inline discriminant: literal
// ctor fast-path (#4290)" in statement_exec_helpers.rs, then
// `const_fold_switch_target` in switchint.rs: "SwitchInt discriminant folded to
// a constant — single-arm walk") and no fallback recorded. The error rule became
// the constant false, so `!(a == b)` was PROVED while `a == b` held on every
// path. BMC fails every one of them. Measured 2026-09-11 with a bundle compiler
// built at origin/main and ay 0.26.0 (94bf24d0f): every *_must_fail harness
// below except the control was SUCCESSFUL under --ay-chc and FAILED
// [AY:CTREX_CAT:Genuine] under BMC.
//
// Oracle (per harness):
//   map_result_eq_must_fail            -> VERIFICATION:- FAILED (assertion)
//   question_mark_result_eq_must_fail  -> VERIFICATION:- FAILED (assertion)
//   branch_join_eq_must_fail           -> VERIFICATION:- FAILED (assertion)
//   symbolic_branch_join_eq_must_fail  -> VERIFICATION:- FAILED (assertion)
//   joined_reference_eq_must_fail      -> VERIFICATION:- FAILED (assertion)
//   copied_result_eq_control_must_fail -> VERIFICATION:- FAILED (assertion)
//
// Every assertion is false on every path, so native Rust panics on each. The
// control reaches `==` through a single-producer copy (`let c = m;`) and was
// already FAILED in both lanes; it keeps the fix honest. The joined-reference
// harness does not depend on f1f2079d1 clearing a borrow's points-at edge, so
// restoring that edge must not turn this file green on its own.

fn f(x: Option<u8>) -> Option<u8> {
    let v = x?;
    Some(v + 1)
}

#[kani::proof]
fn map_result_eq_must_fail() {
    let o: Option<u8> = Some(3);
    assert!(!(o.map(|x| x + 1) == Some(4)));
}

#[kani::proof]
fn question_mark_result_eq_must_fail() {
    assert!(!(f(Some(3)) == Some(4)));
}

#[kani::proof]
fn branch_join_eq_must_fail() {
    let b: bool = kani::any();
    let o: Option<u8> = if b { Some(4) } else { Some(4) };
    assert!(!(o == Some(4)));
}

#[kani::proof]
fn symbolic_branch_join_eq_must_fail() {
    let b: bool = kani::any();
    let v: u8 = kani::any();
    let o: Option<u8> = if b { Some(v) } else { None };
    kani::assume(b);
    assert!(!(o == Some(v)));
}

#[kani::proof]
fn joined_reference_eq_must_fail() {
    let m = Some(4u8);
    let n = Some(4u8);
    let b: bool = kani::any();
    let r: &Option<u8> = if b { &m } else { &n };
    assert!(!(*r == Some(4)));
}

#[kani::proof]
fn copied_result_eq_control_must_fail() {
    let o: Option<u8> = Some(3);
    let m = o.map(|x| x + 1);
    let c = m;
    assert!(!(c == Some(4)));
}
