// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL -- a nested path on a flattened owner whose flattened slot
//! the index walk does not name faithfully: read, written directly (no
//! reference), or written with an element index.
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, Kani 0.67.0; see the
//! manifest entry). Every bug_ row FAILS on the check named here, every safe_
//! row verifies:
//!   bug_tuple1_readonly               -> FAILED ('assertion failed: o.a.0.y == a')
//!   safe_tuple1_readonly              -> SUCCESSFUL
//!   bug_tuple1_copy_read              -> FAILED ('assertion failed: p.a.0.y == a')
//!   bug_tuple1_direct_write           -> FAILED ('assertion failed: o.a.0.y == 0')
//!   safe_tuple1_direct_write          -> SUCCESSFUL
//!   bug_md_read                       -> FAILED ('assertion failed: o.m.b == x')
//!   safe_md_read                      -> SUCCESSFUL
//!   bug_capped_readonly               -> FAILED ('assertion failed: o.k1.k2.k3.k4.y == a')
//!   safe_capped_readonly              -> SUCCESSFUL
//!   bug_capped_direct_aliases_z       -> FAILED ('assertion failed: o.z == v')
//!   safe_capped_direct_z_untouched    -> SUCCESSFUL
//!   bug_root1_direct_c                -> FAILED ('assertion failed: t.0.c == 0')
//!   safe_root1_direct_c               -> SUCCESSFUL
//!   bug_array_field_elem              -> FAILED ('assertion failed: o.inner.arr[1] == 0')
//!   safe_array_field_elem             -> SUCCESSFUL
//!   bug_array_field_elem_ref_to_inner -> FAILED ('assertion failed: o.inner.arr[1] == 0')
//!   safe_array_field_elem_ref_to_inner -> SUCCESSFUL
//!   bug_array_field_elem_direct       -> FAILED ('assertion failed: o.inner.arr[1] == 0')
//!   safe_array_field_elem_direct      -> SUCCESSFUL
//!   bug_ref_to_array_after_sibling    -> FAILED ('assertion failed: s.b[0] == 0')
//!   safe_ref_to_array_after_sibling   -> SUCCESSFUL
//!   bug_array_elem_nested             -> FAILED ('assertion failed: o.inner.arr[i] == 0')
//!   safe_array_elem_nested            -> SUCCESSFUL
//!   bug_array_elem_ref_to_field       -> FAILED ('assertion failed: o.inner.arr[1] == 0')
//!   safe_array_elem_ref_to_field      -> SUCCESSFUL
//!
//! MECHANISM (pre-existing on main e709ca52f59f). A flattened local keeps one
//! state variable per leaf of its sort (`collect_leaf_sorts`), and read case C
//! of `translate_flattened_place`, the direct nested write and the Field+Index
//! stores found a path's slot with `compute_nested_flat_slot`: the MIR field
//! indices walked over the SORT tree. That is the layout only while the two
//! trees have one shape, and `translate_ty` breaks it three ways:
//! - it collapses an interior `(T,)` and the transparent wrappers it models by
//!   name (ManuallyDrop, Cell, a single-field array wrapper, ...) to their
//!   content's sort, so the index after the step is taken one level too high
//!   (`o.a.0.y` named `o.a.0.x.r1`'s slot; `o.m.b` through a ManuallyDrop
//!   likewise);
//! - flattening stops at depth 4 and keeps a datatype in one slot, while the
//!   walk counts every sibling's leaves from depth 0
//!   (`o.k1.k2.k3.k4.y` named `o.z`'s slot);
//! - the direct write did not peel a ROOT `(T,)` the read peels (`t.0.c` on
//!   `t: (P,)` named `inner.b`'s slot), and two Field+Index store paths used
//!   a raw field index as the slot (`let r = &mut s.b; r[0] = v` after a
//!   two-array sibling wrote `s.t.y`) or ignored the reference's own path
//!   (`let r = &mut o.inner; r.arr[1] = v` and `let r = &mut o;
//!   r.inner.arr[1] = v` wrote `o.pre`).
//! On main every bug_ row but the controls below was SUCCESSFUL clean (or the
//! safe twin FAILED Genuine), see the manifest.
//!
//! FIX (compiler 8bc075c5541e): `flat_nested_path_refusal`
//! (`expr/codegen_expr_flat_struct_path.rs`) walks the MIR types and the sorts
//! together and refuses an interior `(T,)` step, a step whose field sort is
//! not `translate_ty` of its MIR type, and a walk past the depth cap
//! (`nested_flat_walk_is_depth_faithful`). Read case C returns no value for a
//! refused path (fail closed, `flattened_nested_path_unfaithful`); the direct
//! nested write peels the root `(T,)` steps the read peels and havocs every
//! slot of the owner on a refused path (`flat_nested_store_unfaithful`); the
//! Field+Index stores compose the ref_target's path with the store's, place
//! the array's slot the same way, or fail closed
//! (`flat_field_index_store_unresolved`). Exact where the walk is faithful:
//! the array rows on a plain struct are FAILED Genuine / SUCCESSFUL clean; a
//! path through the single-field array wrapper AQ fails closed.
//!
//! The two AQ bug_ rows (`bug_array_elem_nested`,
//! `bug_array_elem_ref_to_field`) then reached FAILED only through a demoted
//! proof: emit-time constant propagation re-bound the havocked slots to their
//! constant inputs. Since 2026-09-25 (`const_prop_havoc_dual.rs`) both FAIL
//! from a solver counterexample on the pinned check.
//!
//! Lane scope: CHC only.
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options --harness-timeout=30s flat_nested_path_dual.rs

use std::mem::ManuallyDrop;

// ---- an interior single-element tuple
pub struct R2 {
    r0: u8,
    r1: u8,
}
pub struct QT {
    x: R2,
    y: u8,
}
pub struct PT {
    a: (QT,),
    c: u8,
}

#[kani::proof]
fn bug_tuple1_readonly() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    kani::assume(a != b);
    let o = PT { a: (QT { x: R2 { r0: 0, r1: a }, y: b },), c: 0 };
    assert!(o.a.0.y == a);
}

#[kani::proof]
fn safe_tuple1_readonly() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let o = PT { a: (QT { x: R2 { r0: 0, r1: a }, y: b },), c: 0 };
    assert!(o.a.0.y == b);
}

#[kani::proof]
fn bug_tuple1_copy_read() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    kani::assume(a != b);
    let o = PT { a: (QT { x: R2 { r0: 0, r1: a }, y: b },), c: 0 };
    let p = o;
    assert!(p.a.0.y == a);
}

#[kani::proof]
fn bug_tuple1_direct_write() {
    let mut o = PT { a: (QT { x: R2 { r0: 0, r1: 0 }, y: 0 },), c: 0 };
    let v: u8 = kani::any();
    kani::assume(v != 0);
    o.a.0.y = v;
    assert!(o.a.0.y == 0);
}

#[kani::proof]
fn safe_tuple1_direct_write() {
    let mut o = PT { a: (QT { x: R2 { r0: 0, r1: 0 }, y: 0 },), c: 0 };
    let v: u8 = kani::any();
    o.a.0.y = v;
    assert!(o.a.0.y == v);
}

// ---- a transparent wrapper modeled by name
pub struct Q2 {
    a: R2,
    b: u8,
}
pub struct PM {
    m: ManuallyDrop<Q2>,
    c: u8,
}

#[kani::proof]
fn bug_md_read() {
    let x: u8 = kani::any();
    let y: u8 = kani::any();
    kani::assume(x != y);
    let o = PM { m: ManuallyDrop::new(Q2 { a: R2 { r0: 0, r1: x }, b: y }), c: 0 };
    assert!(o.m.b == x);
}

#[kani::proof]
fn safe_md_read() {
    let x: u8 = kani::any();
    let y: u8 = kani::any();
    let o = PM { m: ManuallyDrop::new(Q2 { a: R2 { r0: 0, r1: x }, b: y }), c: 0 };
    assert!(o.m.b == y);
}

// ---- past the depth cap
pub struct K4 {
    x: u8,
    y: u8,
}
pub struct K3 {
    k4: K4,
}
pub struct K2 {
    k3: K3,
}
pub struct K1 {
    k2: K2,
}
pub struct K0 {
    k1: K1,
    z: u8,
}
fn mk_k0() -> K0 {
    K0 { k1: K1 { k2: K2 { k3: K3 { k4: K4 { x: 0, y: 0 } } } }, z: 0 }
}

#[kani::proof]
fn bug_capped_readonly() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    kani::assume(a != b);
    let o = K0 { k1: K1 { k2: K2 { k3: K3 { k4: K4 { x: 0, y: b } } } }, z: a };
    assert!(o.k1.k2.k3.k4.y == a);
}

#[kani::proof]
fn safe_capped_readonly() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let o = K0 { k1: K1 { k2: K2 { k3: K3 { k4: K4 { x: 0, y: b } } } }, z: a };
    assert!(o.k1.k2.k3.k4.y == b);
}

#[kani::proof]
fn bug_capped_direct_aliases_z() {
    let mut o = mk_k0();
    let v: u8 = kani::any();
    kani::assume(v != 0);
    o.k1.k2.k3.k4.y = v;
    assert!(o.z == v);
}

#[kani::proof]
fn safe_capped_direct_z_untouched() {
    let mut o = mk_k0();
    let v: u8 = kani::any();
    o.k1.k2.k3.k4.y = v;
    assert!(o.z == 0);
}

// ---- a root single-element tuple written directly
pub struct Q {
    a: u8,
    b: u8,
}
pub struct P {
    inner: Q,
    c: u8,
}

#[kani::proof]
fn bug_root1_direct_c() {
    let mut t = (P { inner: Q { a: 0, b: 0 }, c: 0 },);
    let v: u8 = kani::any();
    kani::assume(v != 0);
    t.0.c = v;
    assert!(t.0.c == 0);
}

#[kani::proof]
fn safe_root1_direct_c() {
    let mut t = (P { inner: Q { a: 0, b: 0 }, c: 0 },);
    let v: u8 = kani::any();
    t.0.c = v;
    assert!(t.0.c == v && t.0.inner.b == 0);
}

// ---- an array field inside a nested struct, written with an element index
pub struct Q3 {
    k: u8,
    arr: [u8; 2],
}
pub struct P3 {
    pre: [u8; 2],
    inner: Q3,
    c: u8,
}
fn mk_p3() -> P3 {
    P3 { pre: [0; 2], inner: Q3 { k: 0, arr: [0; 2] }, c: 0 }
}

#[kani::proof]
fn bug_array_field_elem() {
    let mut o = mk_p3();
    let v: u8 = kani::any();
    kani::assume(v != 0);
    let r = &mut o;
    r.inner.arr[1] = v;
    assert!(o.inner.arr[1] == 0);
}

#[kani::proof]
fn safe_array_field_elem() {
    let mut o = mk_p3();
    let v: u8 = kani::any();
    let r = &mut o;
    r.inner.arr[1] = v;
    assert!(o.inner.arr[1] == v && o.pre[1] == 0 && o.inner.k == 0 && o.c == 0);
}

#[kani::proof]
fn bug_array_field_elem_ref_to_inner() {
    let mut o = mk_p3();
    let v: u8 = kani::any();
    kani::assume(v != 0);
    let r = &mut o.inner;
    r.arr[1] = v;
    assert!(o.inner.arr[1] == 0);
}

#[kani::proof]
fn safe_array_field_elem_ref_to_inner() {
    let mut o = mk_p3();
    let v: u8 = kani::any();
    let r = &mut o.inner;
    r.arr[1] = v;
    assert!(o.inner.arr[1] == v && o.pre[1] == 0 && o.inner.k == 0);
}

#[kani::proof]
fn bug_array_field_elem_direct() {
    let mut o = mk_p3();
    let v: u8 = kani::any();
    kani::assume(v != 0);
    o.inner.arr[1] = v;
    assert!(o.inner.arr[1] == 0);
}

#[kani::proof]
fn safe_array_field_elem_direct() {
    let mut o = mk_p3();
    let v: u8 = kani::any();
    o.inner.arr[1] = v;
    assert!(o.inner.arr[1] == v && o.pre[1] == 0 && o.inner.k == 0);
}

// A reference to an array field that follows a two-array sibling: its raw
// field index (1) is the sibling's second array, not its slot (2).
pub struct T2 {
    x: [u8; 2],
    y: [u8; 2],
}
pub struct S2 {
    t: T2,
    b: [u8; 2],
}
fn mk_s2() -> S2 {
    S2 { t: T2 { x: [0; 2], y: [0; 2] }, b: [0; 2] }
}

#[kani::proof]
fn bug_ref_to_array_after_sibling() {
    let mut s = mk_s2();
    let v: u8 = kani::any();
    kani::assume(v != 0);
    let r = &mut s.b;
    r[0] = v;
    assert!(s.b[0] == 0);
}

#[kani::proof]
fn safe_ref_to_array_after_sibling() {
    let mut s = mk_s2();
    let v: u8 = kani::any();
    let r = &mut s.b;
    r[0] = v;
    assert!(s.b[0] == v && s.t.y[0] == 0 && s.t.x[0] == 0);
}

// Through a single-field array wrapper (its sort is the array's).
pub struct A2 {
    x: [u8; 2],
    y: [u8; 2],
}
pub struct AQ {
    arr: [u8; 2],
}
pub struct PA {
    pre: A2,
    inner: AQ,
    c: u8,
}
fn mk_pa() -> PA {
    PA { pre: A2 { x: [0; 2], y: [0; 2] }, inner: AQ { arr: [0; 2] }, c: 0 }
}

#[kani::proof]
fn bug_array_elem_nested() {
    let mut o = mk_pa();
    let i: usize = kani::any();
    kani::assume(i < 2);
    let v: u8 = kani::any();
    kani::assume(v != 0);
    let r = &mut o;
    r.inner.arr[i] = v;
    assert!(o.inner.arr[i] == 0);
}

#[kani::proof]
fn safe_array_elem_nested() {
    let mut o = mk_pa();
    let i: usize = kani::any();
    kani::assume(i < 2);
    let v: u8 = kani::any();
    let r = &mut o;
    r.inner.arr[i] = v;
    assert!(o.inner.arr[i] == v && o.pre.y[i] == 0 && o.pre.x[i] == 0);
}

#[kani::proof]
fn bug_array_elem_ref_to_field() {
    let mut o = mk_pa();
    let v: u8 = kani::any();
    kani::assume(v != 0);
    let r = &mut o.inner;
    r.arr[1] = v;
    assert!(o.inner.arr[1] == 0);
}

#[kani::proof]
fn safe_array_elem_ref_to_field() {
    let mut o = mk_pa();
    let v: u8 = kani::any();
    let r = &mut o.inner;
    r.arr[1] = v;
    assert!(o.inner.arr[1] == v && o.pre.y[1] == 0);
}
