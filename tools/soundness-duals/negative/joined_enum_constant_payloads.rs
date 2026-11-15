// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// NEGATIVE PACK: a JOINED value compared with a CONSTANT whose encoding holds a
// fieldless enum, and comparisons of values that hold references.
//
// Audit evidence: probes written while repairing m3/chc-joined-option-eq (2026-09-12).
// Constant decoders read a fieldless enum (`Ordering`: one byte behind a BV32 sort)
// over the sort's width and did not sign-extend it: `Some(Ordering::Less)` decoded as
// `Some(0xFF)`, `Ok(Ordering::Greater)` as `Ok(0x100)`, and `(Ordering::Greater, 1)` and
// `S { a: Ordering::Greater, b: 2 }` read neighbouring or missing bytes. A joined value
// then compared unequal to the constant it equals, and `!(o == C)` was proved: under
// --ay-chc for the Option, Result and tuple rows, in the BMC lane for the struct rows.
// `(&o, 1u8) != (&c, 1u8)` and `v.get(0) == Some(&1)` compared addresses under
// --ay-chc. Every `_must_fail` assertion is violated on every path native Rust takes;
// every `_safe` assertion holds on every path. A `SUCCESSFUL` on a `_must_fail`
// harness in either lane is a false proof.
//
// Oracle (per harness):
//   opt_repr_i8_neg_join_must_fail        -> VERIFICATION:- FAILED (assertion)
//   opt_repr_i8_neg_join_safe             -> VERIFICATION:- SUCCESSFUL
//   opt_ordering_ne_join_must_fail        -> VERIFICATION:- FAILED (assertion)
//   opt_ordering_ne_join_safe             -> VERIFICATION:- SUCCESSFUL
//   res_ok_ordering_join_must_fail        -> VERIFICATION:- FAILED (assertion)
//   res_ok_ordering_join_safe             -> VERIFICATION:- SUCCESSFUL
//   res_err_ordering_join_must_fail       -> VERIFICATION:- FAILED (assertion)
//   res_err_ordering_join_safe            -> VERIFICATION:- SUCCESSFUL
//   tuple_ordering_join_must_fail         -> VERIFICATION:- FAILED (assertion)
//   tuple_ordering_join_safe              -> VERIFICATION:- SUCCESSFUL
//   tuple_u8_ordering_join_must_fail      -> VERIFICATION:- FAILED (assertion)
//   tuple_u8_ordering_join_safe           -> VERIFICATION:- SUCCESSFUL
//   struct_ordering_field_join_must_fail  -> VERIFICATION:- FAILED (assertion)
//   struct_ordering_field_join_safe       -> VERIFICATION:- SUCCESSFUL
//   struct_less_field_join_must_fail      -> VERIFICATION:- FAILED (assertion)
//   struct_less_field_join_safe           -> VERIFICATION:- SUCCESSFUL
//   struct_unit_enum_field_join_must_fail -> VERIFICATION:- FAILED (assertion)
//   struct_unit_enum_field_join_safe      -> VERIFICATION:- SUCCESSFUL
//   default_repr_neg_enum_join_must_fail  -> VERIFICATION:- FAILED (assertion)
//   default_repr_neg_enum_join_safe       -> VERIFICATION:- SUCCESSFUL
//   tuple_ref_ne_join_must_fail           -> VERIFICATION:- FAILED (assertion)
//   tuple_ref_ne_join_safe                -> VERIFICATION:- SUCCESSFUL
//   vec_get_some_ref_must_fail            -> VERIFICATION:- FAILED (assertion)
//   vec_get_some_ref_safe                 -> VERIFICATION:- SUCCESSFUL

use std::cmp::Ordering;

#[allow(dead_code)]
#[derive(PartialEq, Clone, Copy)]
#[repr(i8)]
enum F {
    X = -3,
    Y = 7,
}

#[allow(dead_code)]
#[derive(PartialEq, Clone, Copy)]
enum E {
    A,
    B,
}

#[allow(dead_code)]
#[derive(PartialEq, Clone, Copy)]
enum G {
    N = -1,
    P = 1,
}

#[derive(PartialEq, Clone, Copy)]
struct S {
    a: Ordering,
    b: u8,
}

#[derive(PartialEq, Clone, Copy)]
struct S2 {
    a: E,
    b: u8,
}

/// Either argument, chosen nondeterministically: a local with two producers.
fn pick<T: Copy>(x: T, y: T) -> T {
    if kani::any() { x } else { y }
}

#[kani::proof]
fn opt_repr_i8_neg_join_must_fail() {
    let o: Option<F> = pick(Some(F::X), Some(F::X));
    assert!(!(o == Some(F::X)));
}
#[kani::proof]
fn opt_repr_i8_neg_join_safe() {
    let o: Option<F> = pick(Some(F::X), Some(F::X));
    assert!(o == Some(F::X));
}

#[kani::proof]
fn opt_ordering_ne_join_must_fail() {
    let o: Option<Ordering> = pick(Some(Ordering::Less), Some(Ordering::Less));
    assert!(o != Some(Ordering::Less));
}
#[kani::proof]
fn opt_ordering_ne_join_safe() {
    let o: Option<Ordering> = pick(Some(Ordering::Less), Some(Ordering::Less));
    assert!(!(o != Some(Ordering::Less)));
}

#[kani::proof]
fn res_ok_ordering_join_must_fail() {
    let o: Result<Ordering, u8> = pick(Ok(Ordering::Greater), Ok(Ordering::Greater));
    assert!(!(o == Ok(Ordering::Greater)));
}
#[kani::proof]
fn res_ok_ordering_join_safe() {
    let o: Result<Ordering, u8> = pick(Ok(Ordering::Greater), Ok(Ordering::Greater));
    assert!(o == Ok(Ordering::Greater));
}

#[kani::proof]
fn res_err_ordering_join_must_fail() {
    let o: Result<u8, Ordering> = pick(Err(Ordering::Less), Err(Ordering::Less));
    assert!(!(o == Err(Ordering::Less)));
}
#[kani::proof]
fn res_err_ordering_join_safe() {
    let o: Result<u8, Ordering> = pick(Err(Ordering::Less), Err(Ordering::Less));
    assert!(o == Err(Ordering::Less));
}

#[kani::proof]
fn tuple_ordering_join_must_fail() {
    let o = pick((Ordering::Greater, 1u8), (Ordering::Greater, 1u8));
    assert!(!(o == (Ordering::Greater, 1u8)));
}
#[kani::proof]
fn tuple_ordering_join_safe() {
    let o = pick((Ordering::Greater, 1u8), (Ordering::Greater, 1u8));
    assert!(o == (Ordering::Greater, 1u8));
}

#[kani::proof]
fn tuple_u8_ordering_join_must_fail() {
    let o = pick((1u8, Ordering::Greater), (1u8, Ordering::Greater));
    assert!(!(o == (1u8, Ordering::Greater)));
}
#[kani::proof]
fn tuple_u8_ordering_join_safe() {
    let o = pick((1u8, Ordering::Greater), (1u8, Ordering::Greater));
    assert!(o == (1u8, Ordering::Greater));
}

#[kani::proof]
fn struct_ordering_field_join_must_fail() {
    let o = pick(S { a: Ordering::Greater, b: 2 }, S { a: Ordering::Greater, b: 2 });
    assert!(!(o == S { a: Ordering::Greater, b: 2 }));
}
#[kani::proof]
fn struct_ordering_field_join_safe() {
    let o = pick(S { a: Ordering::Greater, b: 2 }, S { a: Ordering::Greater, b: 2 });
    assert!(o == S { a: Ordering::Greater, b: 2 });
}

#[kani::proof]
fn struct_less_field_join_must_fail() {
    let o = pick(S { a: Ordering::Less, b: 0 }, S { a: Ordering::Less, b: 0 });
    assert!(!(o == S { a: Ordering::Less, b: 0 }));
}
#[kani::proof]
fn struct_less_field_join_safe() {
    let o = pick(S { a: Ordering::Less, b: 0 }, S { a: Ordering::Less, b: 0 });
    assert!(o == S { a: Ordering::Less, b: 0 });
}

#[kani::proof]
fn struct_unit_enum_field_join_must_fail() {
    let o = pick(S2 { a: E::B, b: 2 }, S2 { a: E::B, b: 2 });
    assert!(!(o == S2 { a: E::B, b: 2 }));
}
#[kani::proof]
fn struct_unit_enum_field_join_safe() {
    let o = pick(S2 { a: E::B, b: 2 }, S2 { a: E::B, b: 2 });
    assert!(o == S2 { a: E::B, b: 2 });
}

#[kani::proof]
fn default_repr_neg_enum_join_must_fail() {
    let o: Option<G> = pick(Some(G::N), Some(G::N));
    assert!(!(o == Some(G::N)));
}
#[kani::proof]
fn default_repr_neg_enum_join_safe() {
    let o: Option<G> = pick(Some(G::N), Some(G::N));
    assert!(o == Some(G::N));
}

#[kani::proof]
fn tuple_ref_ne_join_must_fail() {
    let o: Option<u8> = pick(Some(4), Some(4));
    let c = Some(4u8);
    assert!((&o, 1u8) != (&c, 1u8));
}
#[kani::proof]
fn tuple_ref_ne_join_safe() {
    let o: Option<u8> = pick(Some(4), Some(4));
    let c = Some(4u8);
    assert!(!((&o, 1u8) != (&c, 1u8)));
}

#[kani::proof]
fn vec_get_some_ref_must_fail() {
    let v = vec![1u8, 2];
    assert!(!(v.get(0) == Some(&1)));
}
#[kani::proof]
fn vec_get_some_ref_safe() {
    let v = vec![1u8, 2];
    assert!(v.get(0) == Some(&1));
}
