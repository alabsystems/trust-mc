// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// NEGATIVE PACK: a store through a `&mut` taken of an ELEMENT of an aggregate,
// with one or more FIELD projections after the dereference.
//
// The store place is `[Deref, Field]` with NO Index — the index lives in the
// REFERENT, not in the place — so neither lane's element-store rule could see
// it. BMC bound the element's own register and never wrote the array back; CHC
// passed the ref_target's post-index fields to the element handler and dropped
// the LHS's own. `let mut a = [P{x:0,z:0}; 2]; { let p = &mut a[1]; p.x = 9; }
// assert!(a[1].x == 0);` was VERIFICATION:- SUCCESSFUL with
// [AY:PROOF_QUALIFIERS:clean] in BOTH lanes, and its safe twin was FAILED
// [AY:CTREX_CAT:Genuine] in both. Measured on m3/soundness-fixes-2 at
// 3b73824bb and on origin/main; found by the third adversarial review
// (2026-09-14).
//
// Ground truth for every harness here was compiled and run natively on the
// frozen nightly-2025-12-03 rustc.
//
// Oracle (per harness):
//   *_must_fail   -> VERIFICATION:- FAILED; never SUCCESSFUL
//   *_safe        -> never a Genuine counterexample

#[derive(Clone, Copy)]
struct P {
    x: u8,
    z: u8,
}

struct Holder {
    buf: [P; 2],
}

struct WithArray {
    b: [u8; 2],
}

#[kani::proof]
fn const_index_ref_field_must_fail() {
    let mut a = [P { x: 0, z: 0 }, P { x: 0, z: 0 }];
    {
        let p = &mut a[1];
        p.x = 9;
    }
    assert!(a[1].x == 0); // truth: 9
}

#[kani::proof]
fn const_index_ref_field_safe() {
    let mut a = [P { x: 0, z: 0 }, P { x: 0, z: 0 }];
    {
        let p = &mut a[1];
        p.x = 9;
    }
    assert!(a[1].x == 9 && a[1].z == 0 && a[0].x == 0);
}

#[kani::proof]
fn explicit_deref_ref_field_must_fail() {
    let mut a = [P { x: 0, z: 0 }, P { x: 0, z: 0 }];
    {
        let p = &mut a[1];
        (*p).x = 9;
    }
    assert!(a[1].x == 0); // truth: 9
}

#[kani::proof]
fn sym_index_ref_field_must_fail() {
    let mut a = [P { x: 0, z: 0 }, P { x: 0, z: 0 }];
    let i: usize = kani::any();
    kani::assume(i < 2);
    {
        let p = &mut a[i];
        p.x = 9;
    }
    assert!(a[i].x == 0); // truth: 9
}

#[kani::proof]
fn sym_index_ref_field_safe() {
    let mut a = [P { x: 0, z: 0 }, P { x: 0, z: 0 }];
    let i: usize = kani::any();
    kani::assume(i < 2);
    {
        let p = &mut a[i];
        p.x = 9;
    }
    assert!(a[i].x == 9);
}

#[kani::proof]
fn two_fields_through_one_ref_must_fail() {
    let mut a = [P { x: 0, z: 0 }, P { x: 0, z: 0 }];
    {
        let p = &mut a[1];
        p.x = 9;
        p.z = 8;
    }
    assert!(a[1].x == 0 && a[1].z == 0); // truth: 9 and 8
}

#[kani::proof]
fn two_fields_through_one_ref_safe() {
    // The safe twin the pack's header promises and did not have. Its
    // `_must_fail` sibling above is satisfied if EITHER store lands, so a lane
    // that encodes only one of the two still reads green; this one is violated
    // unless BOTH land. In CHC the second store replaced the first's constraint
    // and this was FAILED [AY:CTREX_CAT:Genuine] (fourth adversarial review of
    // m3/soundness-fixes-2, 2026-09-14, defect M4/D5).
    let mut a = [P { x: 0, z: 0 }, P { x: 0, z: 0 }];
    {
        let p = &mut a[1];
        p.x = 9;
        p.z = 8;
    }
    assert!(a[1].x == 9 && a[1].z == 8);
}

#[kani::proof]
fn two_fields_first_store_lost_must_fail() {
    // Red if only the SECOND of the two stores lands.
    let mut a = [P { x: 0, z: 0 }, P { x: 0, z: 0 }];
    {
        let p = &mut a[1];
        p.x = 9;
        p.z = 8;
    }
    assert!(a[1].x == 0); // truth: 9
}

#[kani::proof]
fn two_fields_second_store_lost_must_fail() {
    // Red if only the FIRST of the two stores lands.
    let mut a = [P { x: 0, z: 0 }, P { x: 0, z: 0 }];
    {
        let p = &mut a[1];
        p.x = 9;
        p.z = 8;
    }
    assert!(a[1].z == 0); // truth: 8
}

#[kani::proof]
fn read_back_through_the_ref_safe() {
    // The write must at least be visible through the reference itself.
    let mut a = [P { x: 0, z: 0 }, P { x: 0, z: 0 }];
    let p = &mut a[1];
    p.x = 9;
    assert!(p.x == 9);
}

#[kani::proof]
fn fn_arg_ref_field_must_fail() {
    // The most idiomatic shape there is: a `&mut` to an element passed to a fn.
    fn bump(p: &mut P) {
        p.x = 9;
    }
    let mut a = [P { x: 0, z: 0 }, P { x: 0, z: 0 }];
    bump(&mut a[1]);
    assert!(a[1].x == 0); // truth: 9
}

#[kani::proof]
fn struct_field_array_ref_field_must_fail() {
    // Two levels: an element of an array that is itself a FIELD.
    let mut g = Holder { buf: [P { x: 0, z: 0 }, P { x: 0, z: 0 }] };
    {
        let p = &mut g.buf[1];
        p.x = 9;
    }
    assert!(g.buf[1].x == 0); // truth: 9
}

#[kani::proof]
fn struct_field_array_ref_field_safe() {
    let mut g = Holder { buf: [P { x: 0, z: 0 }, P { x: 0, z: 0 }] };
    {
        let p = &mut g.buf[1];
        p.x = 9;
    }
    assert!(g.buf[1].x == 9 && g.buf[0].x == 0);
}

#[kani::proof]
fn ref_field_array_elem_must_fail() {
    // An ARRAY-typed field written through a `&mut` to the element.
    let mut a = [WithArray { b: [0, 0] }, WithArray { b: [0, 0] }];
    {
        let p = &mut a[1];
        p.b[0] = 9;
    }
    assert!(a[1].b[0] == 0); // truth: 9
}

// --- controls: shapes that were already exact and must stay PROVED ---------

#[kani::proof]
fn whole_element_through_ref_safe() {
    let mut a = [P { x: 0, z: 0 }, P { x: 0, z: 0 }];
    {
        let p = &mut a[1];
        *p = P { x: 9, z: 8 };
    }
    assert!(a[1].x == 9 && a[1].z == 8 && a[0].x == 0);
}

#[kani::proof]
fn local_struct_through_ref_safe() {
    let mut s = P { x: 0, z: 0 };
    {
        let p = &mut s;
        p.x = 9;
    }
    assert!(s.x == 9 && s.z == 0);
}

#[kani::proof]
fn local_struct_through_ref_must_fail() {
    let mut s = P { x: 0, z: 0 };
    {
        let p = &mut s;
        p.x = 9;
    }
    assert!(s.x == 0); // truth: 9
}

// --- R2: two field stores through ONE element reference, array one deep ----
//
// The bare-local row (`two_fields_through_one_ref_*`) was closed by the D1/D5
// repair; the same shape with the array a FIELD of a struct then certified a
// counterexample on a safe program. The stores were placed exactly — the
// UNTOUCHED element was the counterexample. `[P { .. }; 2]` (a `Repeat`) was
// encoded as a FRESH UNCONSTRAINED array with the repeated element recorded
// only in a side table keyed by the array's own local, so the moment the array
// was MOVED into `Holder` every read through the container saw an arbitrary
// array:
//
//   let mut h = Holder { a: [P { x: 0, z: 0 }; 2], tag: 0 };
//   { let p = &mut h.a[0]; p.x = 9; p.z = 8; }
//   assert!(h.a[0].x == 9 && h.a[0].z == 8 && h.a[1].x == 0 && h.tag == 0);
//
// was FAILED [AY:CTREX_CAT:Genuine] in BMC on a program with no bug (fifth
// adversarial review of m3/soundness-fixes-2, 2026-09-14, defect R2 — a
// regression of the D1 commit, which removed the fallback that used to demote
// this shape). The repeat array's elements are now CONSTRAINED in the encoding
// itself, so the value is exact wherever it flows.

#[derive(Clone, Copy)]
struct RepeatHolder {
    a: [P; 2],
    tag: u8,
}

#[kani::proof]
fn two_stores_nested_container_safe() {
    let mut h = RepeatHolder { a: [P { x: 0, z: 0 }; 2], tag: 0 };
    {
        let p = &mut h.a[0];
        p.x = 9;
        p.z = 8;
    }
    assert!(h.a[0].x == 9 && h.a[0].z == 8 && h.a[1].x == 0 && h.tag == 0);
}

#[kani::proof]
fn two_stores_nested_container_must_fail() {
    let mut h = RepeatHolder { a: [P { x: 0, z: 0 }; 2], tag: 0 };
    {
        let p = &mut h.a[0];
        p.x = 9;
        p.z = 8;
    }
    assert!(h.a[0].x == 0 || h.a[0].z == 0); // truth: 9 and 8
}

// The untouched element of a REPEAT array moved into a container, with no
// store at all: the element that carried the false counterexample above.
#[kani::proof]
fn repeat_array_in_container_untouched_safe() {
    let h = RepeatHolder { a: [P { x: 0, z: 0 }; 2], tag: 0 };
    assert!(h.a[0].x == 0 && h.a[1].x == 0 && h.a[1].z == 0);
}

#[kani::proof]
fn repeat_array_in_container_untouched_must_fail() {
    let h = RepeatHolder { a: [P { x: 7, z: 0 }; 2], tag: 0 };
    assert!(h.a[1].x == 0); // truth: 7
}
