// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// NEGATIVE PACK (review bypass r05): Joined references reaching slice::contains / Range::contains, and a joined Option needle.
//
// Audit evidence: review of m3/chc-joined-option-eq at f1373b8d1 (2026-09-12),
// bypass pack r05. Every `_must_fail` assertion is violated on a path native Rust
// takes; every `_safe` assertion holds on every path. A `SUCCESSFUL` on a `_must_fail`
// harness in either lane is a false proof.
//
// Oracle (per harness):
//   slice_contains_refjoin_a_must_fail   -> VERIFICATION:- FAILED (assertion)
//   slice_contains_refjoin_b_must_fail   -> VERIFICATION:- FAILED (assertion)
//   slice_contains_refjoin_safe          -> VERIFICATION:- SUCCESSFUL
//   range_contains_refjoin_a_must_fail   -> VERIFICATION:- FAILED (assertion)
//   range_contains_refjoin_b_must_fail   -> VERIFICATION:- FAILED (assertion)
//   range_contains_refjoin_safe          -> VERIFICATION:- SUCCESSFUL
//   slice_contains_option_join_must_fail -> VERIFICATION:- FAILED (assertion)
//   slice_contains_option_join_safe      -> VERIFICATION:- SUCCESSFUL

#[kani::proof]
fn slice_contains_refjoin_a_must_fail() {
    let m = 1u8;
    let n = 2u8;
    let b: bool = kani::any();
    let r: &u8 = if b { &m } else { &n };
    let a = [1u8, 3];
    assert!(a.contains(r));
}
#[kani::proof]
fn slice_contains_refjoin_b_must_fail() {
    let m = 1u8;
    let n = 2u8;
    let b: bool = kani::any();
    let r: &u8 = if b { &m } else { &n };
    let a = [2u8, 3];
    assert!(a.contains(r));
}
#[kani::proof]
fn slice_contains_refjoin_safe() {
    let m = 1u8;
    let n = 2u8;
    let b: bool = kani::any();
    let r: &u8 = if b { &m } else { &n };
    let a = [1u8, 3];
    assert!(a.contains(r) == b);
}
#[kani::proof]
fn range_contains_refjoin_a_must_fail() {
    let m = 1u8;
    let n = 5u8;
    let b: bool = kani::any();
    let r: &u8 = if b { &m } else { &n };
    assert!((0u8..3).contains(r));
}
#[kani::proof]
fn range_contains_refjoin_b_must_fail() {
    let m = 1u8;
    let n = 5u8;
    let b: bool = kani::any();
    let r: &u8 = if b { &m } else { &n };
    assert!((4u8..8).contains(r));
}
#[kani::proof]
fn range_contains_refjoin_safe() {
    let m = 1u8;
    let n = 5u8;
    let b: bool = kani::any();
    let r: &u8 = if b { &m } else { &n };
    assert!((0u8..3).contains(r) == b);
}
#[kani::proof]
fn slice_contains_option_join_must_fail() {
    let b: bool = kani::any();
    let o: Option<u8> = if b { Some(4) } else { Some(4) };
    let a = [Some(4u8), None];
    assert!(!a.contains(&o));
}
#[kani::proof]
fn slice_contains_option_join_safe() {
    let b: bool = kani::any();
    let o: Option<u8> = if b { Some(4) } else { Some(4) };
    let a = [Some(4u8), None];
    assert!(a.contains(&o));
}
