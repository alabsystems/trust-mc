// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// NEGATIVE PACK (review bypass r09): Values and references joined by a loop back-edge.
//
// Audit evidence: review of m3/chc-joined-option-eq at f1373b8d1 (2026-09-12),
// bypass pack r09. Every `_must_fail` assertion is violated on a path native Rust
// takes; every `_safe` assertion holds on every path. A `SUCCESSFUL` on a `_must_fail`
// harness in either lane is a false proof.
//
// Oracle (per harness):
//   loop_join_eq_must_fail         -> VERIFICATION:- FAILED (assertion)
//   loop_join_eq_safe              -> VERIFICATION:- SUCCESSFUL
//   loop_join_ref_differ_must_fail -> VERIFICATION:- FAILED (assertion)
//   loop_join_ref_differ_safe      -> VERIFICATION:- SUCCESSFUL
//   loop_symbolic_join_must_fail   -> VERIFICATION:- FAILED (assertion)
//   loop_symbolic_join_safe        -> VERIFICATION:- SUCCESSFUL

#[kani::proof]
fn loop_join_eq_must_fail() {
    let mut o: Option<u8> = None;
    let mut i = 0u8;
    while i < 2 {
        o = Some(4);
        i += 1;
    }
    assert!(!(o == Some(4)));
}
#[kani::proof]
fn loop_join_eq_safe() {
    let mut o: Option<u8> = None;
    let mut i = 0u8;
    while i < 2 {
        o = Some(4);
        i += 1;
    }
    assert!(o == Some(4));
}
#[kani::proof]
fn loop_join_ref_differ_must_fail() {
    let m = Some(1u8);
    let n = Some(2u8);
    let mut r: &Option<u8> = &m;
    let mut i = 0u8;
    while i < 3 {
        if i == 1 {
            r = &n;
        }
        i += 1;
    }
    assert!(*r == Some(1));
}
#[kani::proof]
fn loop_join_ref_differ_safe() {
    let m = Some(1u8);
    let n = Some(2u8);
    let mut r: &Option<u8> = &m;
    let mut i = 0u8;
    while i < 3 {
        if i == 1 {
            r = &n;
        }
        i += 1;
    }
    assert!(*r == Some(2));
}
#[kani::proof]
fn loop_symbolic_join_must_fail() {
    let k: u8 = kani::any();
    kani::assume(k < 4);
    let mut o: Option<u8> = None;
    let mut i = 0u8;
    while i < k {
        o = Some(i);
        i += 1;
    }
    assert!(o == None);
}
#[kani::proof]
fn loop_symbolic_join_safe() {
    let k: u8 = kani::any();
    kani::assume(k < 4);
    let mut o: Option<u8> = None;
    let mut i = 0u8;
    while i < k {
        o = Some(i);
        i += 1;
    }
    assert!((o == None) == (k == 0));
}
