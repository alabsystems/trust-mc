// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// NEGATIVE PACK (review bypass r19): More reference levels around a joined Option: by-value generic T=&Option, &&& comparisons,
// a trait implemented for &Option<u8>, and Vec indexing.
//
// Audit evidence: review of m3/chc-joined-option-eq at f1373b8d1 (2026-09-12),
// bypass pack r19. Every `_must_fail` assertion is violated on a path native Rust
// takes; every `_safe` assertion holds on every path. A `SUCCESSFUL` on a `_must_fail`
// harness in either lane is a false proof.
//
// Oracle (per harness):
//   generic_by_value_ref_must_fail        -> VERIFICATION:- FAILED (assertion)
//   generic_by_value_ref_safe             -> VERIFICATION:- SUCCESSFUL
//   generic_ref_value_differ_a_must_fail  -> VERIFICATION:- FAILED (assertion)
//   generic_ref_value_differ_b_must_fail  -> VERIFICATION:- FAILED (assertion)
//   generic_ref_value_differ_safe         -> VERIFICATION:- SUCCESSFUL
//   triple_ref_eq_must_fail               -> VERIFICATION:- FAILED (assertion)
//   triple_ref_eq_safe                    -> VERIFICATION:- SUCCESSFUL
//   trait_on_ref_must_fail                -> VERIFICATION:- FAILED (assertion)
//   trait_on_ref_safe                     -> VERIFICATION:- SUCCESSFUL
//   unjoined_generic_ref_to_ref_must_fail -> VERIFICATION:- FAILED (assertion)
//   unjoined_generic_ref_to_ref_safe      -> VERIFICATION:- SUCCESSFUL

fn same_val<T: PartialEq>(x: T, y: T) -> bool {
    x == y
}
fn same_ref<T: PartialEq>(x: &T, y: &T) -> bool {
    x == y
}
trait Hit {
    fn hit(&self) -> bool;
}
impl Hit for &Option<u8> {
    fn hit(&self) -> bool {
        **self == Some(4)
    }
}
#[kani::proof]
fn generic_by_value_ref_must_fail() {
    let b: bool = kani::any();
    let o: Option<u8> = if b { Some(4) } else { Some(4) };
    let c = Some(4u8);
    assert!(!same_val(&o, &c));
}
#[kani::proof]
fn generic_by_value_ref_safe() {
    let b: bool = kani::any();
    let o: Option<u8> = if b { Some(4) } else { Some(4) };
    let c = Some(4u8);
    assert!(same_val(&o, &c));
}
#[kani::proof]
fn generic_ref_value_differ_a_must_fail() {
    let b: bool = kani::any();
    let o: Option<u8> = if b { Some(1) } else { Some(2) };
    let c = Some(1u8);
    let r: &Option<u8> = &o;
    let s: &Option<u8> = &c;
    assert!(same_ref(&r, &s));
}
#[kani::proof]
fn generic_ref_value_differ_b_must_fail() {
    let b: bool = kani::any();
    let o: Option<u8> = if b { Some(1) } else { Some(2) };
    let c = Some(1u8);
    let r: &Option<u8> = &o;
    let s: &Option<u8> = &c;
    assert!(!same_ref(&r, &s));
}
#[kani::proof]
fn generic_ref_value_differ_safe() {
    let b: bool = kani::any();
    let o: Option<u8> = if b { Some(1) } else { Some(2) };
    let c = Some(1u8);
    let r: &Option<u8> = &o;
    let s: &Option<u8> = &c;
    assert!(same_ref(&r, &s) == b);
}
#[kani::proof]
fn triple_ref_eq_must_fail() {
    let b: bool = kani::any();
    let o: Option<u8> = if b { Some(4) } else { Some(4) };
    let c = Some(4u8);
    assert!(!(&&o == &&c));
}
#[kani::proof]
fn triple_ref_eq_safe() {
    let b: bool = kani::any();
    let o: Option<u8> = if b { Some(4) } else { Some(4) };
    let c = Some(4u8);
    assert!(&&o == &&c);
}
#[kani::proof]
fn trait_on_ref_must_fail() {
    let b: bool = kani::any();
    let o: Option<u8> = if b { Some(4) } else { Some(4) };
    let r = &o;
    assert!(!r.hit());
}
#[kani::proof]
fn trait_on_ref_safe() {
    let b: bool = kani::any();
    let o: Option<u8> = if b { Some(4) } else { Some(4) };
    let r = &o;
    assert!(r.hit());
}
#[kani::proof]
fn unjoined_generic_ref_to_ref_must_fail() {
    let o: Option<u8> = Some(4);
    let c = Some(4u8);
    let r: &Option<u8> = &o;
    let s: &Option<u8> = &c;
    assert!(!same_ref(&r, &s));
}
#[kani::proof]
fn unjoined_generic_ref_to_ref_safe() {
    let o: Option<u8> = Some(4);
    let c = Some(4u8);
    let r: &Option<u8> = &o;
    let s: &Option<u8> = &c;
    assert!(same_ref(&r, &s));
}
