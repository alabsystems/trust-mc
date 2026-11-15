// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (tracker) -- an array-element store through a reference that
//! no handler places is LOST, and only the fail-closed demotion keeps the
//! false proof from being reported.
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, Kani 0.67.0, measured
//! 2026-09-25; see the manifest entry):
//!   bug_box_elem_store_verdict       -> FAILED ('assertion failed: b[3] == 4')
//!   bug_box_elem_store_check         -> FAILED ('assertion failed: b[3] == 4')
//!   safe_box_elem_store              -> SUCCESSFUL
//!   bug_static_elem_store_verdict    -> FAILED ('assertion failed: unsafe { G1[3] } == 4')
//!   bug_static_elem_store_check      -> FAILED ('assertion failed: unsafe { G2[3] } == 4')
//!   safe_static_elem_store           -> SUCCESSFUL
//!   bug_box_elem_sym_index_check     -> FAILED ('assertion failed: b[0] == 1')
//!   safe_box_elem_loop               -> SUCCESSFUL
//!   bug_static_elem_sym_index_check  -> FAILED ('assertion failed: unsafe { G5[2] } == 3')
//!   safe_static_elem_twice           -> SUCCESSFUL
//!   bug_static_pair_elem_verdict     -> FAILED ('assertion failed: unsafe { G7[1].0 } == 3')
//!   bug_box_elem_ref_check           -> FAILED ('assertion failed: *e == 4')
//!   safe_box_elem_ref                -> SUCCESSFUL
//!   bug_box_elem_ref_sym_check       -> FAILED ('assertion failed: *e != 8')
//!   bug_box_elem_raw_ptr_check       -> FAILED ('assertion failed: unsafe { *p } == 2')
//!   bug_box_elem_ref_helper_check    -> FAILED ('assertion failed: rd1(&b[1]) == 2')
//!   safe_box_elem_ref_helper         -> SUCCESSFUL
//!   bug_static_raw_elem_read_check   -> FAILED ('assertion failed: unsafe { *addr_of!(G8).cast::<u8>().add(3) } == 4')
//!   safe_static_raw_elem_read        -> SUCCESSFUL
//!   bug_static_whole_store_raw_read  -> FAILED ('assertion failed: unsafe { *addr_of!(G10).cast::<u8>().add(3) } == 4')
//!   safe_static_whole_store_raw_read -> SUCCESSFUL
//!   bug_box_u32_elem_ref_check       -> FAILED ('assertion failed: *e == 2')
//!   safe_box_u32_elem_ref            -> SUCCESSFUL
//!   bug_box_elem_ref_helper_inline_check -> FAILED ('assertion failed: rd1_inl(&b[1]) == 2')
//!   safe_box_elem_ref_helper_inline  -> SUCCESSFUL
//!   bug_box_elem_ref_nondet_check    -> FAILED ('assertion failed: *e == 0')
//!   bug_box_elem_ref_loop_verdict    -> FAILED ('assertion failed: *e == 0')
//!   bug_box_elem_raw_add_verdict     -> FAILED ('assertion failed: unsafe { *p.add(3) } == 4')
//!   safe_box_elem_raw_add            -> SUCCESSFUL
//!
//! MECHANISM. `b[3] = 8` on a `Box<[u8; 4]>` and `G[3] = 99` on a
//! `static mut G: [u8; 4]` lower to `(*_n)[_m] = v`. No store handler places a
//! Deref+Index projection there, so it reaches the unsupported-projection
//! arm of `encode_projection_assignment`, whose `projection_sound_fallback`
//! havocs the REFERENCE local `_n`, not the memory it points to. The write is
//! lost, the read returns the initializer, and the assertion over the stale
//! value is proved from a false error obligation. The fallback records
//! `proj_no_field_projections`, a FailClose reason, so every such proof is
//! demoted and the harness reads FAILED; the pinned check reads SUCCESS.
//! Pre-existing on main; found by the fix/chc-constprop-havoc review.
//!
//! FIXED (exact) on fix/chc-lost-writes (2026-09-26). An element store through
//! a pointer with no register referent is written where the element read
//! looks (`stmt/codegen_stmt_store/deref_elem_store.rs`: the region and the
//! array's type-indexed array at `base + i * size`), and an element store
//! through a static array updates the static's array state variable at the
//! index (`codegen_stmt_store_ref.rs`, the static lane). An element whose
//! memory sort is not its value sort (a struct, a tuple) is not written: the
//! array's memory, or the static, is havocked and a FailClose reason
//! recorded (`deref_elem_store_unplaced`, `static_elem_store_unplaced`).
//! The rows after `safe_static_elem_store` were added with the fix, each
//! checked against the corpus-rev Kani 4c0fce8c3.
//!
//! READERS OF THE OTHER VIEWS (review of fix/chc-lost-writes, 2026-09-27).
//! The first version of the fix wrote the element into the ARRAY's
//! type-indexed array only, and the static lane into the state variable only.
//! A read through the element's address (`&b[3]`, `&b[1] as *const u8`, a
//! helper taking `&u8`) selects the ELEMENT's type-indexed array, and a raw
//! read of a static (`*addr_of!(G).cast::<u8>().add(3)`) selects its memory
//! image; both still held the initializer, so those bug rows verified
//! SUCCESSFUL clean and their safe twins were certified Genuine, where the
//! baseline had failed closed. The element now also goes to the element's
//! type-indexed array, and the static lane writes the static's memory image
//! (`store_static_array_element_image`). The rows from `bug_box_elem_ref_check`
//! on pin those readers. The last two rows are PRE-EXISTING on main and on
//! the integration baseline: a WHOLE-array static store updated the state
//! variable only, so the raw read of the memory image was stale (a missed
//! bug and a false certificate); it now writes the image element by element
//! (`store_static_array_image`).
//!
//! The rows from `bug_box_u32_elem_ref_check` on (review follow-up 2,
//! 2026-09-27) promote the rest of the element readers the review named (a
//! `u32` element, an inlinable helper, a nondeterministic value, stores in a
//! loop, `b.as_ptr().add(3)`). The last pair is demoted on every bundle by
//! `offset_provenance_unresolved`, so the bug row pins no check and the safe
//! row is a known-red false failure.
//!
//! Two rows per shape. The `_verdict` rows expect FAILED with no pinned
//! check: they match today through the demotion and turn into a gating
//! missed-bug the moment anything drops it. The `_check` rows pin Kani's
//! check and are known-red missed-bug until the store havocs (or places) the
//! pointee. The safe rows are NOT_GENUINE: the demoted proof is a false
//! failure, never a certificate.
//!
//! Lane scope: CHC only.
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options --harness-timeout=30s lost_deref_elem_store_dual.rs

#![allow(static_mut_refs)]

use std::ptr::addr_of;

static mut G1: [u8; 4] = [1, 2, 3, 4];
static mut G2: [u8; 4] = [1, 2, 3, 4];
static mut G3: [u8; 4] = [1, 2, 3, 4];
static mut G5: [u32; 3] = [1, 2, 3];
static mut G6: [u32; 3] = [1, 2, 3];
static mut G7: [(u8, u8); 2] = [(1, 2), (3, 4)];
static mut G8: [u8; 4] = [1, 2, 3, 4];
static mut G9: [u8; 4] = [1, 2, 3, 4];
static mut G10: [u8; 4] = [1, 2, 3, 4];
static mut G11: [u8; 4] = [1, 2, 3, 4];

fn rd1_inl(e: &u8) -> u8 {
    *e
}

#[inline(never)]
fn rd1(e: &u8) -> u8 {
    *e
}

#[kani::proof]
fn bug_box_elem_store_verdict() {
    let mut b = Box::new([1u8, 2, 3, 4]);
    b[3] = 8;
    assert!(b[3] == 4);
}

#[kani::proof]
fn bug_box_elem_store_check() {
    let mut b = Box::new([1u8, 2, 3, 4]);
    b[3] = 8;
    assert!(b[3] == 4);
}

#[kani::proof]
fn safe_box_elem_store() {
    let mut b = Box::new([1u8, 2, 3, 4]);
    b[3] = 8;
    assert!(b[3] == 8);
}

#[kani::proof]
fn bug_static_elem_store_verdict() {
    unsafe {
        G1[3] = 99;
    }
    assert!(unsafe { G1[3] } == 4);
}

#[kani::proof]
fn bug_static_elem_store_check() {
    unsafe {
        G2[3] = 99;
    }
    assert!(unsafe { G2[3] } == 4);
}

#[kani::proof]
fn safe_static_elem_store() {
    unsafe {
        G3[3] = 99;
    }
    assert!(unsafe { G3[3] } == 99);
}

// A symbolic index through the Box's pointer: element 0 may be the one written.
#[kani::proof]
fn bug_box_elem_sym_index_check() {
    let mut b = Box::new([1u32, 2, 3]);
    let i: usize = kani::any();
    kani::assume(i < 3);
    b[i] = 7;
    assert!(b[0] == 1);
}

// A store per loop iteration, read back after the loop.
#[kani::proof]
fn safe_box_elem_loop() {
    let mut b = Box::new([0u8; 4]);
    for i in 0..4 {
        b[i] = 1;
    }
    assert!(b[3] == 1);
}

#[kani::proof]
fn bug_static_elem_sym_index_check() {
    let i: usize = kani::any();
    kani::assume(i < 3);
    unsafe {
        G5[i] = 7;
    }
    assert!(unsafe { G5[2] } == 3);
}

// Two stores to one element in one block, the second reading the first.
#[kani::proof]
fn safe_static_elem_twice() {
    unsafe {
        G6[0] = 7;
        G6[0] = G6[0] + 1;
    }
    assert!(unsafe { G6[0] } == 8);
}

// A tuple element: not placed exactly, so the static is havocked (fail closed).
#[kani::proof]
fn bug_static_pair_elem_verdict() {
    unsafe {
        G7[1] = (9, 9);
    }
    assert!(unsafe { G7[1].0 } == 3);
}

// Readers through the element's address after an element store through a Box.
#[kani::proof]
fn bug_box_elem_ref_check() {
    let mut b = Box::new([1u8, 2, 3, 4]);
    b[3] = 8;
    let e = &b[3];
    assert!(*e == 4);
}

#[kani::proof]
fn safe_box_elem_ref() {
    let mut b = Box::new([1u8, 2, 3, 4]);
    b[3] = 8;
    let e = &b[3];
    assert!(*e == 8);
}

#[kani::proof]
fn bug_box_elem_ref_sym_check() {
    let mut b = Box::new([1u8, 2, 3, 4]);
    let i: usize = kani::any();
    kani::assume(i < 4);
    b[i] = 8;
    let e = &b[i];
    assert!(*e != 8);
}

#[kani::proof]
fn bug_box_elem_raw_ptr_check() {
    let mut b = Box::new([1u8, 2, 3, 4]);
    b[1] = 9;
    let p: *const u8 = &b[1];
    assert!(unsafe { *p } == 2);
}

#[kani::proof]
fn bug_box_elem_ref_helper_check() {
    let mut b = Box::new([1u8, 2, 3, 4]);
    b[1] = 9;
    assert!(rd1(&b[1]) == 2);
}

#[kani::proof]
fn safe_box_elem_ref_helper() {
    let mut b = Box::new([1u8, 2, 3, 4]);
    b[1] = 9;
    assert!(rd1(&b[1]) == 9);
}

// The static's memory image after an element store through the static.
#[kani::proof]
fn bug_static_raw_elem_read_check() {
    unsafe {
        G8[3] = 99;
    }
    assert!(unsafe { *addr_of!(G8).cast::<u8>().add(3) } == 4);
}

#[kani::proof]
fn safe_static_raw_elem_read() {
    unsafe {
        G9[3] = 99;
    }
    assert!(unsafe { *addr_of!(G9).cast::<u8>().add(3) } == 99);
}

// PRE-EXISTING on the baseline: a whole-array static store left the memory
// image stale.
#[kani::proof]
fn bug_static_whole_store_raw_read() {
    unsafe {
        G10 = [1, 2, 3, 99];
    }
    assert!(unsafe { *addr_of!(G10).cast::<u8>().add(3) } == 4);
}

#[kani::proof]
fn safe_static_whole_store_raw_read() {
    unsafe {
        G11 = [1, 2, 3, 99];
    }
    assert!(unsafe { *addr_of!(G11).cast::<u8>().add(3) } == 99);
}

// Further readers through the element's address (review of
// fix/chc-lost-writes, 2026-09-27, lostwrite-review/src/a1, a4, a7).
#[kani::proof]
fn bug_box_u32_elem_ref_check() {
    let mut b = Box::new([1u32, 2, 3]);
    b[1] = 7;
    let e = &b[1];
    assert!(*e == 2);
}

#[kani::proof]
fn safe_box_u32_elem_ref() {
    let mut b = Box::new([1u32, 2, 3]);
    b[1] = 7;
    let e = &b[1];
    assert!(*e == 7);
}

#[kani::proof]
fn bug_box_elem_ref_helper_inline_check() {
    let mut b = Box::new([1u8, 2, 3, 4]);
    b[1] = 9;
    assert!(rd1_inl(&b[1]) == 2);
}

#[kani::proof]
fn safe_box_elem_ref_helper_inline() {
    let mut b = Box::new([1u8, 2, 3, 4]);
    b[1] = 9;
    assert!(rd1_inl(&b[1]) == 9);
}

#[kani::proof]
fn bug_box_elem_ref_nondet_check() {
    let mut b = Box::new([0u32; 3]);
    let x: u32 = kani::any();
    b[2] = x;
    let e = &b[2];
    assert!(*e == 0);
}

#[kani::proof]
fn bug_box_elem_ref_loop_verdict() {
    let mut b = Box::new([0u8; 3]);
    let mut i = 0;
    while i < 3 {
        b[i] = 1;
        i += 1;
    }
    let e = &b[2];
    assert!(*e == 0);
}

#[kani::proof]
fn bug_box_elem_raw_add_verdict() {
    let mut b = Box::new([1u8, 2, 3, 4]);
    b[3] = 8;
    let p = b.as_ptr();
    assert!(unsafe { *p.add(3) } == 4);
}

#[kani::proof]
fn safe_box_elem_raw_add() {
    let mut b = Box::new([1u8, 2, 3, 4]);
    b[3] = 8;
    let p = b.as_ptr();
    assert!(unsafe { *p.add(3) } == 8);
}
