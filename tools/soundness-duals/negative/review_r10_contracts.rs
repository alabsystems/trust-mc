// kani-flags: -Z function-contracts -Z stubbing
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// NEGATIVE PACK (review bypass r10): Joined Option values seen by contract closures and verified stubs.
//
// Audit evidence: review of m3/chc-joined-option-eq at f1373b8d1 (2026-09-12),
// bypass pack r10. Every `_must_fail` assertion is violated on a path native Rust
// takes; every `_safe` assertion holds on every path. A `SUCCESSFUL` on a `_must_fail`
// harness in either lane is a false proof.
//
// Oracle (per harness):
//   pick_bad_contract_must_fail               -> VERIFICATION:- FAILED (postcondition)
//   pick_good_contract_safe                   -> VERIFICATION:- SUCCESSFUL
//   always4_negated_contract_must_fail        -> VERIFICATION:- FAILED (postcondition)
//   unwrap4_contract_safe                     -> VERIFICATION:- SUCCESSFUL
//   stub_verified_joined_must_fail            -> VERIFICATION:- FAILED (assertion)
//   stub_verified_joined_safe                 -> VERIFICATION:- SUCCESSFUL
//   stub_verified_requires_violated_must_fail -> VERIFICATION:- FAILED (assertion)

#[kani::ensures(|result: &Option<u8>| *result == Some(4))]
fn pick_bad(b: bool) -> Option<u8> {
    if b { Some(4) } else { Some(5) }
}
#[kani::ensures(|result: &Option<u8>| *result == Some(4))]
fn pick_good(b: bool) -> Option<u8> {
    if b { Some(4) } else { Some(4) }
}
#[kani::ensures(|result: &Option<u8>| !(*result == Some(4)))]
fn always4_negated(b: bool) -> Option<u8> {
    if b { Some(4) } else { Some(4) }
}
#[kani::requires(*x == Some(4))]
#[kani::ensures(|r: &u8| *r == 4)]
fn unwrap4(x: &Option<u8>) -> u8 {
    x.unwrap()
}

#[kani::proof_for_contract(pick_bad)]
fn pick_bad_contract_must_fail() {
    let b: bool = kani::any();
    let _ = pick_bad(b);
}
#[kani::proof_for_contract(pick_good)]
fn pick_good_contract_safe() {
    let b: bool = kani::any();
    let _ = pick_good(b);
}
#[kani::proof_for_contract(always4_negated)]
fn always4_negated_contract_must_fail() {
    let b: bool = kani::any();
    let _ = always4_negated(b);
}
#[kani::proof_for_contract(unwrap4)]
fn unwrap4_contract_safe() {
    let o: Option<u8> = kani::any();
    let _ = unwrap4(&o);
}
#[kani::proof]
#[kani::stub_verified(unwrap4)]
fn stub_verified_joined_must_fail() {
    let b: bool = kani::any();
    let o: Option<u8> = if b { Some(4) } else { Some(4) };
    assert!(unwrap4(&o) != 4);
}
#[kani::proof]
#[kani::stub_verified(unwrap4)]
fn stub_verified_joined_safe() {
    let b: bool = kani::any();
    let o: Option<u8> = if b { Some(4) } else { Some(4) };
    assert!(unwrap4(&o) == 4);
}
#[kani::proof]
#[kani::stub_verified(unwrap4)]
fn stub_verified_requires_violated_must_fail() {
    let b: bool = kani::any();
    let o: Option<u8> = if b { Some(5) } else { Some(5) };
    let _ = unwrap4(&o);
}
