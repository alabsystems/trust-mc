// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// NEGATIVE PACK (review bypass r16): Joined arrays of Options handed to callees by &[T; N] and by &[T].
//
// Audit evidence: review of m3/chc-joined-option-eq at f1373b8d1 (2026-09-12),
// bypass pack r16. Every `_must_fail` assertion is violated on a path native Rust
// takes; every `_safe` assertion holds on every path. A `SUCCESSFUL` on a `_must_fail`
// harness in either lane is a false proof.
//
// Oracle (per harness):
//   array_join_callee_must_fail     -> VERIFICATION:- FAILED (assertion)
//   array_join_callee_safe          -> VERIFICATION:- SUCCESSFUL
//   slice_join_callee_must_fail     -> VERIFICATION:- FAILED (assertion)
//   slice_join_callee_safe          -> VERIFICATION:- SUCCESSFUL
//   array_differ_callee_a_must_fail -> VERIFICATION:- FAILED (assertion)
//   array_differ_callee_b_must_fail -> VERIFICATION:- FAILED (assertion)
//   array_differ_callee_safe        -> VERIFICATION:- SUCCESSFUL

fn first_is4(a: &[Option<u8>; 2]) -> bool {
    a[0] == Some(4)
}
fn first_is4s(a: &[Option<u8>]) -> bool {
    a[0] == Some(4)
}
#[kani::proof]
fn array_join_callee_must_fail() {
    let b: bool = kani::any();
    let a: [Option<u8>; 2] = if b { [Some(4), None] } else { [Some(4), None] };
    assert!(!first_is4(&a));
}
#[kani::proof]
fn array_join_callee_safe() {
    let b: bool = kani::any();
    let a: [Option<u8>; 2] = if b { [Some(4), None] } else { [Some(4), None] };
    assert!(first_is4(&a));
}
#[kani::proof]
fn slice_join_callee_must_fail() {
    let b: bool = kani::any();
    let a: [Option<u8>; 2] = if b { [Some(4), None] } else { [Some(4), None] };
    assert!(!first_is4s(&a));
}
#[kani::proof]
fn slice_join_callee_safe() {
    let b: bool = kani::any();
    let a: [Option<u8>; 2] = if b { [Some(4), None] } else { [Some(4), None] };
    assert!(first_is4s(&a));
}
#[kani::proof]
fn array_differ_callee_a_must_fail() {
    let b: bool = kani::any();
    let a: [Option<u8>; 2] = if b { [Some(4), None] } else { [None, None] };
    assert!(first_is4(&a));
}
#[kani::proof]
fn array_differ_callee_b_must_fail() {
    let b: bool = kani::any();
    let a: [Option<u8>; 2] = if b { [Some(4), None] } else { [None, None] };
    assert!(!first_is4(&a));
}
#[kani::proof]
fn array_differ_callee_safe() {
    let b: bool = kani::any();
    let a: [Option<u8>; 2] = if b { [Some(4), None] } else { [None, None] };
    assert!(first_is4(&a) == b);
}
