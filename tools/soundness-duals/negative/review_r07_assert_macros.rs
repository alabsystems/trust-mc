// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// NEGATIVE PACK (review bypass r07): assert_eq! / assert_ne! (a tuple of references matched apart) on joined values.
//
// Audit evidence: review of m3/chc-joined-option-eq at f1373b8d1 (2026-09-12),
// bypass pack r07. Every `_must_fail` assertion is violated on a path native Rust
// takes; every `_safe` assertion holds on every path. A `SUCCESSFUL` on a `_must_fail`
// harness in either lane is a false proof.
//
// Oracle (per harness):
//   assert_ne_join_must_fail        -> VERIFICATION:- FAILED (assertion)
//   assert_eq_join_safe             -> VERIFICATION:- SUCCESSFUL
//   assert_eq_refjoin_a_must_fail   -> VERIFICATION:- FAILED (assertion)
//   assert_eq_refjoin_b_must_fail   -> VERIFICATION:- FAILED (assertion)
//   assert_eq_refjoin_safe          -> VERIFICATION:- SUCCESSFUL
//   assert_ne_result_join_must_fail -> VERIFICATION:- FAILED (assertion)
//   assert_eq_result_join_safe      -> VERIFICATION:- SUCCESSFUL

#[kani::proof]
fn assert_ne_join_must_fail() {
    let b: bool = kani::any();
    let o: Option<u8> = if b { Some(4) } else { Some(4) };
    assert_ne!(o, Some(4));
}
#[kani::proof]
fn assert_eq_join_safe() {
    let b: bool = kani::any();
    let o: Option<u8> = if b { Some(4) } else { Some(4) };
    assert_eq!(o, Some(4));
}
#[kani::proof]
fn assert_eq_refjoin_a_must_fail() {
    let m = Some(1u8);
    let n = Some(2u8);
    let b: bool = kani::any();
    let r: &Option<u8> = if b { &m } else { &n };
    assert_eq!(*r, Some(1));
}
#[kani::proof]
fn assert_eq_refjoin_b_must_fail() {
    let m = Some(1u8);
    let n = Some(2u8);
    let b: bool = kani::any();
    let r: &Option<u8> = if b { &m } else { &n };
    assert_eq!(*r, Some(2));
}
#[kani::proof]
fn assert_eq_refjoin_safe() {
    let m = Some(1u8);
    let n = Some(2u8);
    let b: bool = kani::any();
    let r: &Option<u8> = if b { &m } else { &n };
    assert_eq!(*r == Some(1), b);
}
#[kani::proof]
fn assert_ne_result_join_must_fail() {
    let b: bool = kani::any();
    let o: Result<u8, u8> = if b { Ok(4) } else { Ok(4) };
    assert_ne!(o, Ok(4));
}
#[kani::proof]
fn assert_eq_result_join_safe() {
    let b: bool = kani::any();
    let o: Result<u8, u8> = if b { Ok(4) } else { Ok(4) };
    assert_eq!(o, Ok(4));
}
