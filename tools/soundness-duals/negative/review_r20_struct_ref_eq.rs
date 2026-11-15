// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// NEGATIVE PACK (r20): structural equality on an AGGREGATE that holds a reference.
//
// Companion to the ref-level-eq repair. A `&T` field of a sized `T` encodes as a
// bare address (sort_inference.rs:53), so datatype equality on the aggregate
// compares ADDRESSES while Rust's derived `PartialEq` compares `*a.0 == *b.0`.
// Two distinct locals never share an address, so the comparison folds to FALSE
// and PROVES the negation — a missed bug, measured on the tuple shape in
// `review_r03_ref_in_aggregate.rs::tuple_of_ref_eq_must_fail`.
//
// The tuple shape is now refused (fail closed). This pack MEASURES the two
// cases that refusal deliberately does not cover, rather than assuming them:
//   * a `struct` with a derived `PartialEq` holding `&Option<u8>`
//   * a `&str` field, which is NOT address-encoded (it carries a slice sort)
//     and whose structural comparison must therefore keep working
//
// Oracle (per harness):
//   struct_derive_ref_eq_must_fail   -> VERIFICATION:- FAILED (assertion)
//   struct_derive_ref_eq_safe        -> VERIFICATION:- SUCCESSFUL
//   nested_tuple_ref_eq_must_fail    -> VERIFICATION:- FAILED (assertion)
//   nested_tuple_ref_eq_safe         -> VERIFICATION:- SUCCESSFUL
//   tuple_of_str_eq_must_fail        -> VERIFICATION:- FAILED (assertion)
//   tuple_of_str_eq_safe             -> VERIFICATION:- SUCCESSFUL
//   array_of_ref_eq_must_fail        -> VERIFICATION:- FAILED (assertion)
//   array_of_ref_eq_safe             -> VERIFICATION:- SUCCESSFUL
//   option_of_ref_eq_must_fail       -> VERIFICATION:- FAILED (assertion)
//   option_of_ref_eq_safe            -> VERIFICATION:- SUCCESSFUL

#[derive(PartialEq)]
struct P<'a> {
    r: &'a Option<u8>,
    k: u8,
}

#[kani::proof]
fn struct_derive_ref_eq_must_fail() {
    let b: bool = kani::any();
    let o: Option<u8> = if b { Some(4) } else { Some(4) };
    let c = Some(4u8);
    assert!(!(P { r: &o, k: 1 } == P { r: &c, k: 1 }));
}
#[kani::proof]
fn struct_derive_ref_eq_safe() {
    let b: bool = kani::any();
    let o: Option<u8> = if b { Some(4) } else { Some(4) };
    let c = Some(4u8);
    assert!(P { r: &o, k: 1 } == P { r: &c, k: 1 });
}
#[kani::proof]
fn nested_tuple_ref_eq_must_fail() {
    let b: bool = kani::any();
    let o: Option<u8> = if b { Some(4) } else { Some(4) };
    let c = Some(4u8);
    assert!(!(((&o, 1u8), 2u8) == ((&c, 1u8), 2u8)));
}
#[kani::proof]
fn nested_tuple_ref_eq_safe() {
    let b: bool = kani::any();
    let o: Option<u8> = if b { Some(4) } else { Some(4) };
    let c = Some(4u8);
    assert!(((&o, 1u8), 2u8) == ((&c, 1u8), 2u8));
}
#[kani::proof]
fn tuple_of_str_eq_must_fail() {
    let b: bool = kani::any();
    let s: &str = if b { "ab" } else { "ab" };
    assert!(!((s, 1u8) == ("ab", 1u8)));
}
#[kani::proof]
fn tuple_of_str_eq_safe() {
    let b: bool = kani::any();
    let s: &str = if b { "ab" } else { "ab" };
    assert!((s, 1u8) == ("ab", 1u8));
}

#[kani::proof]
fn array_of_ref_eq_must_fail() {
    let b: bool = kani::any();
    let o: Option<u8> = if b { Some(4) } else { Some(4) };
    let c = Some(4u8);
    assert!(!([&o] == [&c]));
}
#[kani::proof]
fn array_of_ref_eq_safe() {
    let b: bool = kani::any();
    let o: Option<u8> = if b { Some(4) } else { Some(4) };
    let c = Some(4u8);
    assert!([&o] == [&c]);
}
#[kani::proof]
fn option_of_ref_eq_must_fail() {
    let b: bool = kani::any();
    let o: Option<u8> = if b { Some(4) } else { Some(4) };
    let c = Some(4u8);
    assert!(!(Some(&o) == Some(&c)));
}
#[kani::proof]
fn option_of_ref_eq_safe() {
    let b: bool = kani::any();
    let o: Option<u8> = if b { Some(4) } else { Some(4) };
    let c = Some(4u8);
    assert!(Some(&o) == Some(&c));
}
