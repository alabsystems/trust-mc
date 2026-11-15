// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// NEGATIVE PACK: reads of a `Box::new` payload through every access path.
//
// Found while fixing alloc_id_offset_dual_safe.rs::safe_distinct_fields_differ
// (2026-09-12). The BMC `BoxNew` stub allocated the object and returned its
// address but never stored the boxed value, so every read through the box saw
// unconstrained memory and the counterexample was certified Genuine. Measured
// on bundle 31793ccc3 (BMC): every *_safe harness below except the array, enum
// and raw-field shapes FAILED with [AY:CTREX_CAT:Genuine]; the CHC lane proved
// them all.
//
// The *_through_ref / *_box_mut / direct_field harnesses write the payload back
// through the box, a raw-deref alias or `&mut` and read it again. Once the
// payload lived in memory, a store through `&mut s.b` still updated only the
// alias name: `mut_scalar_through_ref_must_fail` verified SUCCESSFUL and
// `compound_through_ref_safe` FAILED Genuine (BMC) until the store was mirrored
// into byte memory (codegen_assign_ref_deref.rs).
//
// Oracle (per harness):
//   *_safe           -> VERIFICATION:- SUCCESSFUL (array/enum/raw shapes and
//                       mut_field_through_ref_safe: never a Genuine counterexample)
//   *_must_fail      -> VERIFICATION:- FAILED (assertion)

#[repr(C)]
struct S {
    a: u8,
    b: u8,
}

struct Wide {
    x: u16,
    y: u32,
}

enum E {
    A(u8),
    B(u16),
}

#[kani::proof]
fn scalar_roundtrip_safe() {
    let b = Box::new(7u8);
    assert!(*b == 7);
}

#[kani::proof]
fn scalar_wrong_must_fail() {
    let b = Box::new(7u8);
    assert!(*b == 8);
}

#[kani::proof]
fn field_ref_safe() {
    let s = Box::new(S { a: 1, b: 2 });
    let pa = &s.a;
    let pb = &s.b;
    assert!(*pa == 1 && *pb == 2);
}

#[kani::proof]
fn field_ref_wrong_must_fail() {
    let s = Box::new(S { a: 1, b: 2 });
    let pb = &s.b;
    assert!(*pb == 1);
}

#[kani::proof]
fn field_direct_safe() {
    let s = Box::new(S { a: 1, b: 2 });
    assert!(s.a == 1 && s.b == 2);
}

#[kani::proof]
fn field_direct_wrong_must_fail() {
    let s = Box::new(S { a: 1, b: 2 });
    assert!(s.b == 1);
}

#[kani::proof]
fn wide_field_ref_safe() {
    let w = Box::new(Wide { x: 0x1234, y: 0xdead_beef });
    let py = &w.y;
    assert!(*py == 0xdead_beef && w.x == 0x1234);
}

#[kani::proof]
fn wide_field_ref_wrong_must_fail() {
    let w = Box::new(Wide { x: 0x1234, y: 0xdead_beef });
    let py = &w.y;
    assert!(*py == 0x1234);
}

#[kani::proof]
fn symbolic_field_ref_safe() {
    let v: u8 = kani::any();
    let s = Box::new(S { a: v, b: v.wrapping_add(1) });
    let pa = &s.a;
    let pb = &s.b;
    assert!(*pa != *pb);
}

#[kani::proof]
fn tuple_ref_safe() {
    let t = Box::new((3u8, 4u16));
    let p1 = &t.1;
    assert!(*p1 == 4 && t.0 == 3);
}

#[kani::proof]
fn array_ref_safe() {
    let a = Box::new([5u8, 6u8]);
    let p = &a[1];
    assert!(*p == 6 && a[0] == 5);
}

#[kani::proof]
fn array_ref_wrong_must_fail() {
    let a = Box::new([5u8, 6u8]);
    let p = &a[1];
    assert!(*p == 5);
}

#[kani::proof]
fn enum_match_safe() {
    let e = Box::new(E::B(9));
    match *e {
        E::B(v) => assert!(v == 9),
        E::A(_) => assert!(false),
    }
}

#[kani::proof]
fn enum_match_wrong_must_fail() {
    let e = Box::new(E::B(9));
    match *e {
        E::B(v) => assert!(v == 8),
        E::A(_) => {}
    }
}

#[kani::proof]
fn raw_field_read_safe() {
    let s = Box::new(S { a: 1, b: 2 });
    let p: *const S = &*s;
    unsafe { assert!((*p).b == 2) }
}

#[kani::proof]
fn mut_through_ref_safe() {
    let mut s = Box::new(S { a: 1, b: 2 });
    let pb = &mut s.b;
    *pb = 9;
    assert!(s.b == 9 && s.a == 1);
}

#[kani::proof]
fn scalar_box_mut_safe() {
    let mut b = Box::new(7u32);
    *b = 11;
    assert!(*b == 11);
}

#[kani::proof]
fn scalar_box_mut_must_fail() {
    let mut b = Box::new(7u32);
    *b = 11;
    assert!(*b == 7);
}

#[kani::proof]
fn direct_field_store_safe() {
    let mut s = Box::new(S { a: 1, b: 2 });
    s.b = 9;
    assert!(s.b == 9 && s.a == 1);
}

#[kani::proof]
fn direct_field_store_must_fail() {
    let mut s = Box::new(S { a: 1, b: 2 });
    s.b = 9;
    assert!(s.b == 2);
}

#[kani::proof]
fn mut_scalar_through_ref_must_fail() {
    let mut s = Box::new(S { a: 1, b: 2 });
    let pb = &mut s.b;
    *pb = 9;
    // FALSE: the store through `pb` wrote 9.
    assert!(s.b == 2);
}

#[kani::proof]
fn compound_through_ref_safe() {
    let mut s = Box::new(S { a: 1, b: 2 });
    let pb = &mut s.b;
    *pb += 3;
    assert!(s.b == 5);
}

#[kani::proof]
fn mut_field_through_ref_safe() {
    let mut w = Box::new(Wide { x: 1, y: 2 });
    let r = &mut *w;
    r.y = 9;
    assert!(w.y == 9 && w.x == 1);
}

#[kani::proof]
fn mut_field_through_ref_must_fail() {
    let mut w = Box::new(Wide { x: 1, y: 2 });
    let r = &mut *w;
    r.y = 9;
    assert!(w.y == 2);
}
