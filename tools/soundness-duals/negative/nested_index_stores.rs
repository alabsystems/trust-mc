// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// NEGATIVE PACK: the two directions of `store_nests_under_element_index`, the
// CHC rule that decides which element-index stores no handler can encode.
//
// Written while fixing defect 3 of the adversarial review of
// m3/soundness-fixes-2 (2026-09-13). `(*r)[i][j] = v` and `(*r)[i].x = v` were
// resolved with the FIRST index only and everything after it dropped, so the
// store landed nowhere while the harness still claimed a proof
// (negative/ref_index_ops.rs pins that half through a `&mut` reference).
//
// The fail-closed rule must be exactly as wide as the gap. `a[i].x = v` on a
// LOCAL is rebuilt exactly by the array-element handler, and `s.buf[i] = v`
// (index last) is exact too; demoting either would be a proof regression. So
// this pack pins:
//
//   * `*_exact_safe`   a store shape the handlers DO encode: still PROVED.
//   * `*_must_fail`    a store that must reach the referent, or fail closed.
//
// Oracle (per harness):
//   *_must_fail   -> VERIFICATION:- FAILED (assertion); never SUCCESSFUL
//   *_safe        -> never a Genuine counterexample

#[derive(Clone, Copy)]
struct P {
    x: u8,
    y: u8,
}

struct Buf {
    buf: [u8; 3],
    tag: u8,
}

// --- shapes the handlers encode exactly: these must stay PROVED ------------

#[kani::proof]
fn local_index_then_field_exact_safe() {
    // `a[i].x = v` on a local: no dereference, fields after the index.
    let mut a = [P { x: 1, y: 2 }, P { x: 3, y: 4 }];
    let i: usize = kani::any();
    kani::assume(i < 2);
    a[i].x = 9;
    assert!(a[i].x == 9 && a[i].y == if i == 0 { 2 } else { 4 });
}

#[kani::proof]
fn local_index_then_field_must_fail() {
    let mut a = [P { x: 1, y: 2 }, P { x: 3, y: 4 }];
    a[1].x = 9;
    assert!(a[1].x == 3);
}

#[kani::proof]
fn field_then_index_exact_safe() {
    // `s.buf[i] = v`: the index is last.
    let mut s = Buf { buf: [1u8, 2, 3], tag: 7 };
    let i: usize = kani::any();
    kani::assume(i < 3);
    s.buf[i] = 9;
    assert!(s.buf[i] == 9 && s.tag == 7);
}

#[kani::proof]
fn field_then_index_must_fail() {
    let mut s = Buf { buf: [1u8, 2, 3], tag: 7 };
    s.buf[2] = 9;
    assert!(s.buf[2] == 3);
}

#[kani::proof]
fn deref_index_exact_safe() {
    // `(*r)[i] = v`: one index under the dereference, nothing after it.
    let mut a = [1u8, 2, 3];
    {
        let r: &mut [u8; 3] = &mut a;
        let i: usize = kani::any();
        kani::assume(i < 3);
        r[i] = 9;
        assert!(r[i] == 9);
    }
    assert!(a[0] == 9 || a[1] == 9 || a[2] == 9);
}

#[kani::proof]
fn deref_index_must_fail() {
    let mut a = [1u8, 2, 3];
    {
        let r: &mut [u8; 3] = &mut a;
        r[1] = 9;
    }
    assert!(a[1] == 2);
}

// --- shapes no handler encodes: these must fail closed ---------------------

#[kani::proof]
fn local_nested_index_safe() {
    // `g[i][j] = v` on a local, both indices constant.
    let mut g = [[0u8; 2]; 2];
    g[1][0] = 9;
    assert!(g[1][0] == 9 && g[0][0] == 0 && g[1][1] == 0);
}

#[kani::proof]
fn local_nested_index_must_fail() {
    let mut g = [[0u8; 2]; 2];
    g[1][0] = 9;
    assert!(g[1][0] == 0);
}

#[kani::proof]
fn local_nested_index_symbolic_safe() {
    let mut g = [[0u8; 2]; 2];
    let i: usize = kani::any();
    kani::assume(i < 2);
    g[i][1] = 9;
    assert!(g[i][1] == 9);
}

#[kani::proof]
fn local_nested_index_symbolic_must_fail() {
    let mut g = [[0u8; 2]; 2];
    let i: usize = kani::any();
    kani::assume(i < 2);
    g[i][1] = 9;
    assert!(g[i][1] == 0);
}

#[kani::proof]
fn deref_nested_index_safe() {
    let mut g = [[0u8; 2]; 2];
    {
        let r: &mut [[u8; 2]; 2] = &mut g;
        r[1][0] = 9;
    }
    assert!(g[1][0] == 9 && g[1][1] == 0);
}

#[kani::proof]
fn deref_nested_index_must_fail() {
    let mut g = [[0u8; 2]; 2];
    {
        let r: &mut [[u8; 2]; 2] = &mut g;
        r[1][0] = 9;
    }
    assert!(g[1][0] == 0);
}

#[kani::proof]
fn deref_index_then_field_safe() {
    let mut a = [P { x: 1, y: 2 }, P { x: 3, y: 4 }];
    {
        let r: &mut [P; 2] = &mut a;
        r[1].x = 9;
    }
    assert!(a[1].x == 9 && a[1].y == 4 && a[0].x == 1);
}

#[kani::proof]
fn deref_index_then_field_must_fail() {
    let mut a = [P { x: 1, y: 2 }, P { x: 3, y: 4 }];
    {
        let r: &mut [P; 2] = &mut a;
        r[1].x = 9;
    }
    assert!(a[1].x == 3);
}

// --- an element FIELD read on an array of TUPLES (defect found by this pack) --

#[kani::proof]
fn local_index_then_tuple_field_safe() {
    // The struct twin above is exact; the TUPLE element is not. The array
    // aggregate constrains `a[i]` to the whole-tuple register of a local that
    // `try_codegen_flattened_tuple_aggregate` only ever bound FIELD BY FIELD,
    // so the element value is unconstrained and a safe read is certified wrong.
    // Measured FAILED [AY:CTREX_CAT:Genuine] on main 31793ccc3 (main-bundle) as
    // well as on this branch; `let a = [(1u8, 2u8), (3, 4)];
    // assert!(a[1].0 == 3)` needs no slice or reference at all.
    let a = [(1u8, 2u8), (3u8, 4u8)];
    assert!(a[1].0 == 3 && a[1].1 == 4 && a[0].0 == 1);
}

#[kani::proof]
fn local_index_then_tuple_field_must_fail() {
    let a = [(1u8, 2u8), (3u8, 4u8)];
    assert!(a[1].0 == 1);
}
