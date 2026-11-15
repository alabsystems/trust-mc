// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// NEGATIVE PACK: a `&mut` or `*mut` taken of an array element's FIELD, and the
// same one projection deeper.
//
// The shape `negative/elem_ref_field_stores.rs` does NOT carry: every harness
// there takes `&mut a[i]` (the WHOLE element). Taking `&mut a[i].x` names the
// FIELD, so the derived pointee is `..._cidx_1_field_0`, whose parent
// `..._cidx_1` is an element slot with no register of its own. The BMC
// write-back walk returned `None` there with no recorded reason and the store
// was DROPPED:
//
//   let mut a = [P { x: 0, z: 0 }; 2]; { let p = &mut a[1].x; *p = 9; }
//   assert!(a[1].x == 0);
//
// was `VERIFICATION:- SUCCESSFUL` with `[AY:PROOF_QUALIFIERS:clean]` and its
// safe twin was `FAILED [AY:CTREX_CAT:Genuine]`. That was a REGRESSION of
// commit 7fe93048b (which routed the shape through the walk after removing the
// array-coercion havoc that used to demote it); the `.nested` and the raw
// pointer variants were red before it too. Fourth adversarial review of
// m3/soundness-fixes-2, 2026-09-14, defects B/D1 and M1/D2.
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

#[derive(Clone, Copy)]
struct Inner {
    x: u8,
    y: u8,
}

#[derive(Clone, Copy)]
struct S {
    inner: Inner,
    y: u8,
}

#[kani::proof]
fn elem_field_ref_store_must_fail() {
    let mut a = [P { x: 0, z: 0 }, P { x: 0, z: 0 }];
    {
        let p = &mut a[1].x;
        *p = 9;
    }
    assert!(a[1].x == 0); // truth: 9
}

#[kani::proof]
fn elem_field_ref_store_safe() {
    let mut a = [P { x: 0, z: 0 }, P { x: 0, z: 0 }];
    {
        let p = &mut a[1].x;
        *p = 9;
    }
    assert!(a[1].x == 9 && a[0].x == 0 && a[1].z == 0);
}

#[kani::proof]
fn sym_elem_field_ref_store_must_fail() {
    let mut a = [P { x: 0, z: 0 }, P { x: 0, z: 0 }];
    let i: usize = kani::any();
    kani::assume(i < 2);
    {
        let p = &mut a[i].x;
        *p = 9;
    }
    assert!(a[i].x == 0); // truth: 9
}

#[kani::proof]
fn sym_elem_field_ref_store_safe() {
    let mut a = [P { x: 0, z: 0 }, P { x: 0, z: 0 }];
    let i: usize = kani::any();
    kani::assume(i < 2);
    {
        let p = &mut a[i].x;
        *p = 9;
    }
    assert!(a[i].x == 9);
}

#[kani::proof]
fn raw_of_elem_field_write_must_fail() {
    let mut a = [P { x: 0, z: 0 }, P { x: 0, z: 0 }];
    let p: *mut u8 = &mut a[1].x;
    unsafe {
        *p = 9;
    }
    assert!(a[1].x == 0); // truth: 9
}

#[kani::proof]
fn raw_of_elem_field_write_safe() {
    let mut a = [P { x: 0, z: 0 }, P { x: 0, z: 0 }];
    let p: *mut u8 = &mut a[1].x;
    unsafe {
        *p = 9;
    }
    assert!(a[1].x == 9 && a[0].x == 0 && a[1].z == 0);
}

#[kani::proof]
fn nested_elem_field_ref_must_fail() {
    let mut a = [
        S { inner: Inner { x: 0, y: 0 }, y: 0 },
        S { inner: Inner { x: 0, y: 0 }, y: 0 },
    ];
    {
        let p = &mut a[1].inner;
        p.x = 9;
    }
    assert!(a[1].inner.x == 0); // truth: 9
}

#[kani::proof]
fn nested_elem_field_ref_safe() {
    let mut a = [
        S { inner: Inner { x: 0, y: 0 }, y: 0 },
        S { inner: Inner { x: 0, y: 0 }, y: 0 },
    ];
    {
        let p = &mut a[1].inner;
        p.x = 9;
    }
    assert!(a[1].inner.x == 9 && a[1].inner.y == 0 && a[0].inner.x == 0);
}

#[kani::proof]
fn raw_of_nested_field_write_must_fail() {
    let mut a = [
        S { inner: Inner { x: 0, y: 0 }, y: 0 },
        S { inner: Inner { x: 0, y: 0 }, y: 0 },
    ];
    let p: *mut S = &mut a[0];
    unsafe {
        (*p).y = 9;
    }
    assert!(a[0].y == 0); // truth: 9
}

#[kani::proof]
fn raw_of_nested_field_write_safe() {
    let mut a = [
        S { inner: Inner { x: 0, y: 0 }, y: 0 },
        S { inner: Inner { x: 0, y: 0 }, y: 0 },
    ];
    let p: *mut S = &mut a[0];
    unsafe {
        (*p).y = 9;
    }
    assert!(a[0].y == 9 && a[1].y == 0 && a[0].inner.x == 0);
}

// --- controls: the shapes that were already exact must stay exact -----------

#[kani::proof]
fn local_struct_field_ref_safe() {
    let mut s = P { x: 0, z: 0 };
    {
        let p = &mut s.x;
        *p = 9;
    }
    assert!(s.x == 9 && s.z == 0);
}

#[kani::proof]
fn local_struct_field_ref_must_fail() {
    let mut s = P { x: 0, z: 0 };
    {
        let p = &mut s.x;
        *p = 9;
    }
    assert!(s.x == 0); // truth: 9
}

// --- R1: a RAW pointer of an element's field at a SYMBOLIC index -----------
//
// The one cell of the matrix this pack did not carry: const+ref, sym+ref and
// const+RAW were all here, RAW+SYMBOLIC was not, and it was the cell that
// proved clean. `&raw mut a[i].x` names the pointee `a_idx_by_L_field_0`,
// which `write_back_to_stack_pointee` routed to the indexed-array branch —
// the one branch of that function that never moved the SLOT's own register.
// `codegen_place` resolves the full projected name BEFORE it walks the array,
// so the read answered with the value the borrow was taken at while the array
// itself was updated exactly:
//
//   let i: usize = kani::any(); kani::assume(i < 2);
//   let mut a = [P { x: 0, z: 0 }; 2];
//   unsafe { let p: *mut u8 = &raw mut a[i].x; *p = 9; }
//   assert!(a[i].x == 0);
//
// was SUCCESSFUL [AY:PROOF_QUALIFIERS:clean] in BMC and its safe twin FAILED
// [AY:CTREX_CAT:Genuine] (fifth adversarial review of m3/soundness-fixes-2,
// 2026-09-14, defect R1 — a regression of the D1 commit).

#[kani::proof]
fn raw_of_sym_elem_field_write_must_fail() {
    let mut a = [P { x: 0, z: 0 }, P { x: 0, z: 0 }];
    let i: usize = kani::any();
    kani::assume(i < 2);
    unsafe {
        let p: *mut u8 = &raw mut a[i].x;
        *p = 9;
    }
    assert!(a[i].x == 0); // truth: 9
}

#[kani::proof]
fn raw_of_sym_elem_field_write_safe() {
    let mut a = [P { x: 0, z: 0 }, P { x: 0, z: 0 }];
    let i: usize = kani::any();
    kani::assume(i < 2);
    unsafe {
        let p: *mut u8 = &raw mut a[i].x;
        *p = 9;
    }
    assert!(a[i].x == 9 && a[i].z == 0);
}

// The same cell with the array built by REPEAT rather than by list: the repeat
// array's elements are constrained in the encoding, not only in the side table.
#[kani::proof]
fn raw_of_sym_repeat_elem_field_must_fail() {
    let mut a = [P { x: 0, z: 0 }; 2];
    let i: usize = kani::any();
    kani::assume(i < 2);
    unsafe {
        let p: *mut u8 = &raw mut a[i].x;
        *p = 9;
    }
    assert!(a[i].x == 0); // truth: 9
}

#[kani::proof]
fn raw_of_sym_repeat_elem_field_safe() {
    let mut a = [P { x: 0, z: 0 }; 2];
    let i: usize = kani::any();
    kani::assume(i < 2);
    unsafe {
        let p: *mut u8 = &raw mut a[i].x;
        *p = 9;
    }
    assert!(a[i].x == 9 && a[i].z == 0);
}

// --- R3: `&mut <container>.a[i].x` — the array one container deep ----------
//
// The CHC ref_target handler collected the ref_target's fields as ONE flat
// chain and applied them all to the CONTAINER, so `&mut h.a[1].x` selected
// `h.a` and then took the ARRAY's field 0 — which `datatype_field_select`
// answers with the array itself (the repr-SIMD passthrough) — and the store
// wrote the whole ELEMENT with the field's value. `assert!(h.a[1].x == 0)` was
// SUCCESSFUL [AY:PROOF_QUALIFIERS:clean] and the safe twin FAILED
// [AY:CTREX_CAT:Genuine], for a struct field, a tuple field and a 2-D array
// alike (fifth adversarial review, defects R3/R4). The fields after the index
// now travel to the ELEMENT, or the store fails closed.

#[derive(Clone, Copy)]
struct Holder {
    a: [P; 2],
    tag: u8,
}

#[kani::proof]
fn struct_field_array_elem_field_must_fail() {
    let mut h = Holder { a: [P { x: 0, z: 0 }, P { x: 0, z: 0 }], tag: 0 };
    {
        let p = &mut h.a[1].x;
        *p = 9;
    }
    assert!(h.a[1].x == 0); // truth: 9
}

#[kani::proof]
fn struct_field_array_elem_field_safe() {
    let mut h = Holder { a: [P { x: 0, z: 0 }, P { x: 0, z: 0 }], tag: 0 };
    {
        let p = &mut h.a[1].x;
        *p = 9;
    }
    assert!(h.a[1].x == 9 && h.a[0].x == 0 && h.tag == 0);
}

#[kani::proof]
fn tuple_field_array_elem_field_must_fail() {
    let mut t: (u8, [P; 2]) = (0, [P { x: 0, z: 0 }, P { x: 0, z: 0 }]);
    {
        let p = &mut t.1[0].z;
        *p = 9;
    }
    assert!(t.1[0].z == 0); // truth: 9
}

#[kani::proof]
fn tuple_field_array_elem_field_safe() {
    let mut t: (u8, [P; 2]) = (0, [P { x: 0, z: 0 }, P { x: 0, z: 0 }]);
    {
        let p = &mut t.1[0].z;
        *p = 9;
    }
    assert!(t.1[0].z == 9 && t.0 == 0 && t.1[1].z == 0);
}

#[kani::proof]
fn grid_elem_field_must_fail() {
    let mut g = [
        [P { x: 0, z: 0 }, P { x: 0, z: 0 }],
        [P { x: 0, z: 0 }, P { x: 0, z: 0 }],
    ];
    {
        let p = &mut g[1][0].x;
        *p = 9;
    }
    assert!(g[1][0].x == 0); // truth: 9
}

#[kani::proof]
fn grid_elem_field_safe() {
    let mut g = [
        [P { x: 0, z: 0 }, P { x: 0, z: 0 }],
        [P { x: 0, z: 0 }, P { x: 0, z: 0 }],
    ];
    {
        let p = &mut g[1][0].x;
        *p = 9;
    }
    assert!(g[1][0].x == 9 && g[0][0].x == 0 && g[1][1].x == 0);
}
