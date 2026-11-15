// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL -- a whole read of a struct or tuple FIELD of a heap object
//! after a store of one of its leaves: `d.x.0 = 255; let t = d.x;` on a
//! `Box<N2 { x: (u8, u8), .. }>`.
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, measured 2026-09-27):
//!   bug_pair_leaf_whole_read            -> FAILED ('assertion failed: t.0 < 255')
//!   safe_pair_leaf_whole_read           -> SUCCESSFUL
//!   bug_tuple3_leaf_whole_read          -> FAILED ('assertion failed: (t.0).0 < 255')
//!   safe_tuple3_leaf_whole_read         -> SUCCESSFUL
//!   bug_struct_leaf_whole_read          -> FAILED ('assertion failed: i.p < 255')
//!   safe_struct_leaf_whole_read         -> SUCCESSFUL
//!   bug_nested_struct_leaf_whole_read   -> FAILED ('assertion failed: w.i.p < 255')
//!   safe_nested_struct_leaf_whole_read  -> SUCCESSFUL
//!   bug_raw_pair_leaf_whole_read        -> FAILED ('assertion failed: t.0 < 255')
//!   safe_raw_pair_leaf_whole_read       -> SUCCESSFUL
//!   bug_ref_pair_leaf_whole_read        -> FAILED ('assertion failed: t.0 < 255')
//!   safe_ref_pair_leaf_whole_read       -> SUCCESSFUL
//!   bug_whole_payload_read_after_leaf   -> FAILED ('assertion failed: v.x.0 < 255')
//!   safe_whole_payload_read_after_leaf  -> SUCCESSFUL
//!
//! MECHANISM (pre-existing on main; found by the review follow-up of
//! fix/chc-lost-writes, 2026-09-27). A leaf store (`d.x.0 = 255`) writes the
//! leaf's type-indexed array (`mem_u8`) at the leaf's address. The whole read
//! of the field (`let t = d.x`) went through the Deref+Field lane
//! (`try_deref_field_offset_load`), which loaded the field from ITS OWN type's
//! array (`mem_tuple_u8_u8`, `mem_I`), written only by the `Box::new`
//! initializer: the read returned the constructor's value. On main the safe
//! rows were certified Genuine failures and the bug rows ended in a solver
//! timeout (Unknown), which only the const-prop guard
//! `has_scalarized_obj_size_bounds` produced; through a raw pointer the bug
//! row verified SUCCESSFUL clean. The lane now rebuilds a struct or tuple
//! field from its scalar leaves (`load_aggregate_field_from_leaves`), the way
//! the walked impl's field map reads a field of `self`.
//!
//! The `ref` rows fail closed on main and on the fix (a store through `r`
//! whose stack target is unresolved), and the whole-payload rows fail closed
//! on the region read after a sub-sort store: their safe twins are known-red
//! false failures, never certificates.
//!
//! Lane scope: CHC only.
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options --harness-timeout=30s aggregate_field_leaf_view_dual.rs

#[derive(Clone, Copy)]
pub struct I {
    p: u8,
    q: u8,
}
#[derive(Clone, Copy)]
pub struct W {
    i: I,
    r: u8,
}
pub struct D3 {
    x: ((u8, u8), u8),
    z: u8,
}
pub struct N2 {
    x: (u8, u8),
    z: u8,
}
pub struct N3 {
    i: I,
    z: u8,
}
pub struct S2 {
    w: W,
    z: u8,
}

#[kani::proof]
fn bug_pair_leaf_whole_read() {
    let a: u8 = kani::any();
    kani::assume(a < 10);
    let mut d = Box::new(N2 { x: (a, 1), z: 4 });
    d.x.0 = 255;
    let t = d.x;
    assert!(t.0 < 255);
}

#[kani::proof]
fn safe_pair_leaf_whole_read() {
    let a: u8 = kani::any();
    kani::assume(a < 10);
    let mut d = Box::new(N2 { x: (a, 1), z: 4 });
    d.x.0 = 200;
    let t = d.x;
    assert!(t.0 == 200);
}

#[kani::proof]
fn bug_tuple3_leaf_whole_read() {
    let a: u8 = kani::any();
    kani::assume(a < 10);
    let mut d = Box::new(D3 { x: ((a, 1), 2), z: 4 });
    d.x.0.0 = 255;
    let t = d.x;
    assert!((t.0).0 < 255);
}

#[kani::proof]
fn safe_tuple3_leaf_whole_read() {
    let a: u8 = kani::any();
    kani::assume(a < 10);
    let mut d = Box::new(D3 { x: ((a, 1), 2), z: 4 });
    d.x.0.0 = 200;
    let t = d.x;
    assert!((t.0).0 == 200);
}

#[kani::proof]
fn bug_struct_leaf_whole_read() {
    let a: u8 = kani::any();
    kani::assume(a < 10);
    let mut d = Box::new(N3 { i: I { p: a, q: 1 }, z: 4 });
    d.i.p = 255;
    let i = d.i;
    assert!(i.p < 255);
}

#[kani::proof]
fn safe_struct_leaf_whole_read() {
    let a: u8 = kani::any();
    kani::assume(a < 10);
    let mut d = Box::new(N3 { i: I { p: a, q: 1 }, z: 4 });
    d.i.p = 200;
    let i = d.i;
    assert!(i.p == 200);
}

#[kani::proof]
fn bug_nested_struct_leaf_whole_read() {
    let a: u8 = kani::any();
    kani::assume(a < 10);
    let mut d = Box::new(S2 { w: W { i: I { p: a, q: 1 }, r: 2 }, z: 4 });
    d.w.i.p = 255;
    let w = d.w;
    assert!(w.i.p < 255);
}

#[kani::proof]
fn safe_nested_struct_leaf_whole_read() {
    let a: u8 = kani::any();
    kani::assume(a < 10);
    let mut d = Box::new(S2 { w: W { i: I { p: a, q: 1 }, r: 2 }, z: 4 });
    d.w.i.p = 200;
    let w = d.w;
    assert!(w.i.p == 200);
}

#[kani::proof]
fn bug_raw_pair_leaf_whole_read() {
    let a: u8 = kani::any();
    kani::assume(a < 10);
    let mut d = Box::new(N2 { x: (a, 1), z: 4 });
    let p: *mut N2 = &mut *d;
    unsafe { (*p).x.0 = 255; }
    let t = unsafe { (*p).x };
    assert!(t.0 < 255);
}

#[kani::proof]
fn safe_raw_pair_leaf_whole_read() {
    let a: u8 = kani::any();
    kani::assume(a < 10);
    let mut d = Box::new(N2 { x: (a, 1), z: 4 });
    let p: *mut N2 = &mut *d;
    unsafe { (*p).x.0 = 200; }
    let t = unsafe { (*p).x };
    assert!(t.0 == 200);
}

#[kani::proof]
fn bug_ref_pair_leaf_whole_read() {
    let a: u8 = kani::any();
    kani::assume(a < 10);
    let mut d = Box::new(N2 { x: (a, 1), z: 4 });
    let r: &mut N2 = &mut d;
    r.x.0 = 255;
    let t = r.x;
    assert!(t.0 < 255);
}

#[kani::proof]
fn safe_ref_pair_leaf_whole_read() {
    let a: u8 = kani::any();
    kani::assume(a < 10);
    let mut d = Box::new(N2 { x: (a, 1), z: 4 });
    let r: &mut N2 = &mut d;
    r.x.0 = 200;
    let t = r.x;
    assert!(t.0 == 200);
}

#[kani::proof]
fn bug_whole_payload_read_after_leaf() {
    let a: u8 = kani::any();
    kani::assume(a < 10);
    let mut d = Box::new(N2 { x: (a, 1), z: 4 });
    d.x.0 = 255;
    let v = *d;
    assert!(v.x.0 < 255);
}

#[kani::proof]
fn safe_whole_payload_read_after_leaf() {
    let a: u8 = kani::any();
    kani::assume(a < 10);
    let mut d = Box::new(N2 { x: (a, 1), z: 4 });
    d.x.0 = 200;
    let v = *d;
    assert!(v.x.0 == 200);
}
