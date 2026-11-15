// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// NEGATIVE PACK (review bypass r22): Option == over aggregate payloads, WITHOUT any join (the walker folds both tags and then compares payloads).
//
// Audit evidence: review of m3/chc-joined-option-eq at f1373b8d1 (2026-09-12),
// bypass pack r22. Every `_must_fail` assertion is violated on a path native Rust
// takes; every `_safe` assertion holds on every path. A `SUCCESSFUL` on a `_must_fail`
// harness in either lane is a false proof.
//
// Oracle (per harness):
//   opt_array_ne_must_fail      -> VERIFICATION:- FAILED (assertion)
//   opt_array_eq_safe           -> VERIFICATION:- SUCCESSFUL
//   opt_array1_ne_must_fail     -> VERIFICATION:- FAILED (assertion)
//   opt_array1_eq_safe          -> VERIFICATION:- SUCCESSFUL
//   opt_struct_ne_must_fail     -> VERIFICATION:- FAILED (assertion)
//   opt_struct_eq_safe          -> VERIFICATION:- SUCCESSFUL
//   opt_pair_symbolic_must_fail -> VERIFICATION:- FAILED (assertion)
//   opt_pair_symbolic_safe      -> VERIFICATION:- SUCCESSFUL
//   result_pair_ne_must_fail    -> VERIFICATION:- FAILED (assertion)
//   result_pair_eq_safe         -> VERIFICATION:- SUCCESSFUL
//   opt_array_differ_must_fail  -> VERIFICATION:- FAILED (assertion)
//   opt_array_differ_safe       -> VERIFICATION:- SUCCESSFUL

#[derive(PartialEq, Clone, Copy)]
struct P2 {
    a: u8,
    b: u8,
}
#[kani::proof]
fn opt_array_ne_must_fail() {
    let o: Option<[u8; 2]> = Some([1, 2]);
    assert!(o != Some([1, 2]));
}
#[kani::proof]
fn opt_array_eq_safe() {
    let o: Option<[u8; 2]> = Some([1, 2]);
    assert!(o == Some([1, 2]));
}
#[kani::proof]
fn opt_array1_ne_must_fail() {
    let o: Option<[u8; 1]> = Some([7]);
    assert!(!(o == Some([7])));
}
#[kani::proof]
fn opt_array1_eq_safe() {
    let o: Option<[u8; 1]> = Some([7]);
    assert!(o == Some([7]));
}
#[kani::proof]
fn opt_struct_ne_must_fail() {
    let o: Option<P2> = Some(P2 { a: 1, b: 2 });
    assert!(!(o == Some(P2 { a: 1, b: 2 })));
}
#[kani::proof]
fn opt_struct_eq_safe() {
    let o: Option<P2> = Some(P2 { a: 1, b: 2 });
    assert!(o == Some(P2 { a: 1, b: 2 }));
}
#[kani::proof]
fn opt_pair_symbolic_must_fail() {
    let x: u8 = kani::any();
    let o: Option<(u8, u8)> = Some((x, 2));
    assert!(!(o == Some((x, 2))));
}
#[kani::proof]
fn opt_pair_symbolic_safe() {
    let x: u8 = kani::any();
    let o: Option<(u8, u8)> = Some((x, 2));
    assert!(o == Some((x, 2)));
}
#[kani::proof]
fn result_pair_ne_must_fail() {
    let o: Result<(u8, u8), u8> = Ok((1, 2));
    assert!(!(o == Ok((1, 2))));
}
#[kani::proof]
fn result_pair_eq_safe() {
    let o: Result<(u8, u8), u8> = Ok((1, 2));
    assert!(o == Ok((1, 2)));
}
#[kani::proof]
fn opt_array_differ_must_fail() {
    let o: Option<[u8; 2]> = Some([1, 2]);
    assert!(o == Some([1, 3]));
}
#[kani::proof]
fn opt_array_differ_safe() {
    let o: Option<[u8; 2]> = Some([1, 2]);
    assert!(o != Some([1, 3]));
}
