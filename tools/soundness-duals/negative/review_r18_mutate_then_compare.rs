// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// NEGATIVE PACK (review bypass r18): A joined Option mutated through &mut (store, callee, swap, as_mut) and THEN compared by reference.
//
// Audit evidence: review of m3/chc-joined-option-eq at f1373b8d1 (2026-09-12),
// bypass pack r18. Every `_must_fail` assertion is violated on a path native Rust
// takes; every `_safe` assertion holds on every path. A `SUCCESSFUL` on a `_must_fail`
// harness in either lane is a false proof.
//
// Oracle (per harness):
//   deref_store_then_eq_must_fail   -> VERIFICATION:- FAILED (assertion)
//   deref_store_then_eq_safe        -> VERIFICATION:- SUCCESSFUL
//   callee_store_then_eq_must_fail  -> VERIFICATION:- FAILED (assertion)
//   callee_store_then_eq_safe       -> VERIFICATION:- SUCCESSFUL
//   swap_then_eq_must_fail          -> VERIFICATION:- FAILED (assertion)
//   swap_then_eq_safe               -> VERIFICATION:- SUCCESSFUL
//   payload_write_then_eq_must_fail -> VERIFICATION:- FAILED (assertion)
//   payload_write_then_eq_safe      -> VERIFICATION:- SUCCESSFUL
//   replace_then_eq_must_fail       -> VERIFICATION:- FAILED (assertion)
//   replace_then_eq_safe            -> VERIFICATION:- SUCCESSFUL

fn clear(x: &mut Option<u8>) {
    *x = None;
}
#[kani::proof]
fn deref_store_then_eq_must_fail() {
    let b: bool = kani::any();
    let mut o: Option<u8> = if b { Some(4) } else { Some(4) };
    let p = &mut o;
    *p = None;
    assert!(!(o == None));
}
#[kani::proof]
fn deref_store_then_eq_safe() {
    let b: bool = kani::any();
    let mut o: Option<u8> = if b { Some(4) } else { Some(4) };
    let p = &mut o;
    *p = None;
    assert!(o == None);
}
#[kani::proof]
fn callee_store_then_eq_must_fail() {
    let b: bool = kani::any();
    let mut o: Option<u8> = if b { Some(4) } else { Some(4) };
    clear(&mut o);
    assert!(!(o == None));
}
#[kani::proof]
fn callee_store_then_eq_safe() {
    let b: bool = kani::any();
    let mut o: Option<u8> = if b { Some(4) } else { Some(4) };
    clear(&mut o);
    assert!(o == None);
}
#[kani::proof]
fn swap_then_eq_must_fail() {
    let b: bool = kani::any();
    let mut o: Option<u8> = if b { Some(4) } else { Some(4) };
    let mut q: Option<u8> = None;
    core::mem::swap(&mut o, &mut q);
    assert!(!(o == None));
}
#[kani::proof]
fn swap_then_eq_safe() {
    let b: bool = kani::any();
    let mut o: Option<u8> = if b { Some(4) } else { Some(4) };
    let mut q: Option<u8> = None;
    core::mem::swap(&mut o, &mut q);
    assert!(o == None && q == Some(4));
}
#[kani::proof]
fn payload_write_then_eq_must_fail() {
    let b: bool = kani::any();
    let mut o: Option<u8> = if b { Some(4) } else { Some(4) };
    if let Some(x) = &mut o {
        *x = 5;
    }
    assert!(!(o == Some(5)));
}
#[kani::proof]
fn payload_write_then_eq_safe() {
    let b: bool = kani::any();
    let mut o: Option<u8> = if b { Some(4) } else { Some(4) };
    if let Some(x) = &mut o {
        *x = 5;
    }
    assert!(o == Some(5));
}
#[kani::proof]
fn replace_then_eq_must_fail() {
    let b: bool = kani::any();
    let mut o: Option<u8> = if b { Some(4) } else { Some(4) };
    let _old = core::mem::replace(&mut o, Some(7));
    assert!(!(o == Some(7)));
}
#[kani::proof]
fn replace_then_eq_safe() {
    let b: bool = kani::any();
    let mut o: Option<u8> = if b { Some(4) } else { Some(4) };
    let old = core::mem::replace(&mut o, Some(7));
    assert!(o == Some(7) && old == Some(4));
}
