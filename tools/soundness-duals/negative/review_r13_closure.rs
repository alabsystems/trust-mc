// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// NEGATIVE PACK (review bypass r13): Closure parameters and captures bound through call_args.rs / resolve_closure_capture_expr.
//
// Audit evidence: review of m3/chc-joined-option-eq at f1373b8d1 (2026-09-12),
// bypass pack r13. Every `_must_fail` assertion is violated on a path native Rust
// takes; every `_safe` assertion holds on every path. A `SUCCESSFUL` on a `_must_fail`
// harness in either lane is a false proof.
//
// Oracle (per harness):
//   closure_ref_param_refjoin_a_must_fail -> VERIFICATION:- FAILED (assertion)
//   closure_ref_param_refjoin_b_must_fail -> VERIFICATION:- FAILED (assertion)
//   closure_ref_param_refjoin_safe        -> VERIFICATION:- SUCCESSFUL
//   closure_capture_refjoin_a_must_fail   -> VERIFICATION:- FAILED (assertion)
//   closure_capture_refjoin_b_must_fail   -> VERIFICATION:- FAILED (assertion)
//   closure_capture_refjoin_safe          -> VERIFICATION:- SUCCESSFUL
//   closure_capture_option_join_must_fail -> VERIFICATION:- FAILED (assertion)
//   closure_capture_option_join_safe      -> VERIFICATION:- SUCCESSFUL
//   map_closure_capture_join_must_fail    -> VERIFICATION:- FAILED (assertion)
//   map_closure_capture_join_safe         -> VERIFICATION:- SUCCESSFUL

#[kani::proof]
fn closure_ref_param_refjoin_a_must_fail() {
    let m = 1u8;
    let n = 2u8;
    let b: bool = kani::any();
    let r: &u8 = if b { &m } else { &n };
    let f = |x: &u8| *x == 1;
    assert!(f(r));
}
#[kani::proof]
fn closure_ref_param_refjoin_b_must_fail() {
    let m = 1u8;
    let n = 2u8;
    let b: bool = kani::any();
    let r: &u8 = if b { &m } else { &n };
    let f = |x: &u8| *x == 2;
    assert!(f(r));
}
#[kani::proof]
fn closure_ref_param_refjoin_safe() {
    let m = 1u8;
    let n = 2u8;
    let b: bool = kani::any();
    let r: &u8 = if b { &m } else { &n };
    let f = |x: &u8| *x == 1;
    assert!(f(r) == b);
}
#[kani::proof]
fn closure_capture_refjoin_a_must_fail() {
    let m = 1u8;
    let n = 2u8;
    let b: bool = kani::any();
    let r: &u8 = if b { &m } else { &n };
    let f = || *r == 1;
    assert!(f());
}
#[kani::proof]
fn closure_capture_refjoin_b_must_fail() {
    let m = 1u8;
    let n = 2u8;
    let b: bool = kani::any();
    let r: &u8 = if b { &m } else { &n };
    let f = || *r == 2;
    assert!(f());
}
#[kani::proof]
fn closure_capture_refjoin_safe() {
    let m = 1u8;
    let n = 2u8;
    let b: bool = kani::any();
    let r: &u8 = if b { &m } else { &n };
    let f = || *r == 1;
    assert!(f() == b);
}
#[kani::proof]
fn closure_capture_option_join_must_fail() {
    let b: bool = kani::any();
    let o: Option<u8> = if b { Some(4) } else { Some(4) };
    let f = || o == Some(4);
    assert!(!f());
}
#[kani::proof]
fn closure_capture_option_join_safe() {
    let b: bool = kani::any();
    let o: Option<u8> = if b { Some(4) } else { Some(4) };
    let f = || o == Some(4);
    assert!(f());
}
#[kani::proof]
fn map_closure_capture_join_must_fail() {
    let b: bool = kani::any();
    let o: Option<u8> = if b { Some(4) } else { Some(4) };
    let t = Some(1u8).map(|_| o == Some(4)).unwrap();
    assert!(!t);
}
#[kani::proof]
fn map_closure_capture_join_safe() {
    let b: bool = kani::any();
    let o: Option<u8> = if b { Some(4) } else { Some(4) };
    let t = Some(1u8).map(|_| o == Some(4)).unwrap();
    assert!(t);
}
