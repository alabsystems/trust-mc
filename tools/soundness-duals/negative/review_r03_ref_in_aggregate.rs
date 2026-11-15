// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// NEGATIVE PACK (review bypass r03): An aggregate that HOLDS a reference to a joined Option.
//
// Audit evidence: review of m3/chc-joined-option-eq at f1373b8d1 (2026-09-12),
// bypass pack r03. Every `_must_fail` assertion is violated on a path native Rust
// takes; every `_safe` assertion holds on every path. A `SUCCESSFUL` on a `_must_fail`
// harness in either lane is a false proof.
//
// Oracle (per harness):
//   struct_holding_ref_must_fail       -> VERIFICATION:- FAILED (assertion)
//   struct_holding_ref_safe            -> VERIFICATION:- SUCCESSFUL
//   tuple_of_ref_eq_must_fail          -> VERIFICATION:- FAILED (assertion)
//   tuple_of_ref_eq_safe               -> VERIFICATION:- SUCCESSFUL
//   struct_holding_refjoin_a_must_fail -> VERIFICATION:- FAILED (assertion)
//   struct_holding_refjoin_b_must_fail -> VERIFICATION:- FAILED (assertion)
//   struct_holding_refjoin_safe        -> VERIFICATION:- SUCCESSFUL

struct H<'a> {
    r: &'a Option<u8>,
}
impl<'a> H<'a> {
    fn hit(&self) -> bool {
        *self.r == Some(4)
    }
}

#[kani::proof]
fn struct_holding_ref_must_fail() {
    let b: bool = kani::any();
    let o: Option<u8> = if b { Some(4) } else { Some(4) };
    let h = H { r: &o };
    assert!(!h.hit());
}
#[kani::proof]
fn struct_holding_ref_safe() {
    let b: bool = kani::any();
    let o: Option<u8> = if b { Some(4) } else { Some(4) };
    let h = H { r: &o };
    assert!(h.hit());
}
#[kani::proof]
fn tuple_of_ref_eq_must_fail() {
    let b: bool = kani::any();
    let o: Option<u8> = if b { Some(4) } else { Some(4) };
    let c = Some(4u8);
    assert!(!((&o, 1u8) == (&c, 1u8)));
}
#[kani::proof]
fn tuple_of_ref_eq_safe() {
    let b: bool = kani::any();
    let o: Option<u8> = if b { Some(4) } else { Some(4) };
    let c = Some(4u8);
    assert!((&o, 1u8) == (&c, 1u8));
}
#[kani::proof]
fn struct_holding_refjoin_a_must_fail() {
    let m = Some(1u8);
    let n = Some(2u8);
    let b: bool = kani::any();
    let h = if b { H { r: &m } } else { H { r: &n } };
    assert!(*h.r == Some(1));
}
#[kani::proof]
fn struct_holding_refjoin_b_must_fail() {
    let m = Some(1u8);
    let n = Some(2u8);
    let b: bool = kani::any();
    let h = if b { H { r: &m } } else { H { r: &n } };
    assert!(*h.r == Some(2));
}
#[kani::proof]
fn struct_holding_refjoin_safe() {
    let m = Some(1u8);
    let n = Some(2u8);
    let b: bool = kani::any();
    let h = if b { H { r: &m } } else { H { r: &n } };
    assert!((*h.r == Some(1)) == b);
}
