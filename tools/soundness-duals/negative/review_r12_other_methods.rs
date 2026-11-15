// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// NEGATIVE PACK (review bypass r12): Other &self entry points on a joined Option: clone, Ord::cmp, partial_cmp, max, ne, reversed ==.
//
// Audit evidence: review of m3/chc-joined-option-eq at f1373b8d1 (2026-09-12),
// bypass pack r12. Every `_must_fail` assertion is violated on a path native Rust
// takes; every `_safe` assertion holds on every path. A `SUCCESSFUL` on a `_must_fail`
// harness in either lane is a false proof.
//
// Oracle (per harness):
//   clone_join_must_fail       -> VERIFICATION:- FAILED (assertion)
//   clone_join_safe            -> VERIFICATION:- SUCCESSFUL
//   cmp_join_must_fail         -> VERIFICATION:- FAILED (assertion)
//   cmp_join_safe              -> VERIFICATION:- SUCCESSFUL
//   partial_cmp_join_must_fail -> VERIFICATION:- FAILED (assertion)
//   partial_cmp_join_safe      -> VERIFICATION:- SUCCESSFUL
//   max_join_must_fail         -> VERIFICATION:- FAILED (assertion)
//   max_join_safe              -> VERIFICATION:- SUCCESSFUL
//   ne_method_join_must_fail   -> VERIFICATION:- FAILED (assertion)
//   ne_method_join_safe        -> VERIFICATION:- SUCCESSFUL
//   reversed_eq_join_must_fail -> VERIFICATION:- FAILED (assertion)
//   reversed_eq_join_safe      -> VERIFICATION:- SUCCESSFUL

use std::cmp::Ordering;
#[kani::proof]
fn clone_join_must_fail() {
    let b: bool = kani::any();
    let o: Option<u8> = if b { Some(4) } else { Some(4) };
    assert!(!(o.clone() == Some(4)));
}
#[kani::proof]
fn clone_join_safe() {
    let b: bool = kani::any();
    let o: Option<u8> = if b { Some(4) } else { Some(4) };
    assert!(o.clone() == Some(4));
}
#[kani::proof]
fn cmp_join_must_fail() {
    let b: bool = kani::any();
    let o: Option<u8> = if b { Some(4) } else { Some(4) };
    assert!(o.cmp(&Some(4)) != Ordering::Equal);
}
#[kani::proof]
fn cmp_join_safe() {
    let b: bool = kani::any();
    let o: Option<u8> = if b { Some(4) } else { Some(4) };
    assert!(o.cmp(&Some(4)) == Ordering::Equal);
}
#[kani::proof]
fn partial_cmp_join_must_fail() {
    let b: bool = kani::any();
    let o: Option<u8> = if b { Some(4) } else { Some(4) };
    assert!(o.partial_cmp(&Some(4)) != Some(Ordering::Equal));
}
#[kani::proof]
fn partial_cmp_join_safe() {
    let b: bool = kani::any();
    let o: Option<u8> = if b { Some(4) } else { Some(4) };
    assert!(o.partial_cmp(&Some(4)) == Some(Ordering::Equal));
}
#[kani::proof]
fn max_join_must_fail() {
    let b: bool = kani::any();
    let o: Option<u8> = if b { Some(4) } else { Some(4) };
    assert!(o.max(Some(3)) != Some(4));
}
#[kani::proof]
fn max_join_safe() {
    let b: bool = kani::any();
    let o: Option<u8> = if b { Some(4) } else { Some(4) };
    assert!(o.max(Some(3)) == Some(4));
}
#[kani::proof]
fn ne_method_join_must_fail() {
    let b: bool = kani::any();
    let o: Option<u8> = if b { Some(4) } else { Some(4) };
    assert!(o.ne(&Some(4)));
}
#[kani::proof]
fn ne_method_join_safe() {
    let b: bool = kani::any();
    let o: Option<u8> = if b { Some(4) } else { Some(4) };
    assert!(!o.ne(&Some(4)));
}
#[kani::proof]
fn reversed_eq_join_must_fail() {
    let b: bool = kani::any();
    let o: Option<u8> = if b { Some(4) } else { Some(4) };
    assert!(!(Some(4) == o));
}
#[kani::proof]
fn reversed_eq_join_safe() {
    let b: bool = kani::any();
    let o: Option<u8> = if b { Some(4) } else { Some(4) };
    assert!(Some(4) == o);
}
