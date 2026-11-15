// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! PRECISION + SOUNDNESS DUAL -- a store through a `&mut` that points THROUGH
//! a Box's heap pointer (`Box::as_mut`, `DerefMut::deref_mut`, `BorrowMut`,
//! a generic `AsMut`, and `as_mut` inside a closure).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, Kani 0.67.0; see the
//! manifest entry). Every row without a `bug_` prefix verifies; every bug_ row
//! FAILS on the check named here:
//!   u01_box_as_mut_scalar            -> SUCCESSFUL
//!   u02_box_as_mut_field             -> SUCCESSFUL
//!   v03_borrow_mut_box               -> SUCCESSFUL
//!   v07_box_as_mut_twice             -> SUCCESSFUL
//!   v08_box_as_mut_any               -> SUCCESSFUL
//!   v10_box_as_mut_then_read_other   -> SUCCESSFUL
//!   x06_box_as_mut_closure           -> SUCCESSFUL
//!   x07_box_deref_mut_explicit       -> SUCCESSFUL
//!   x08_as_mut_trait_generic         -> SUCCESSFUL
//!   bug_u01_box_as_mut_scalar        -> FAILED ('assertion failed: *b == 1')
//!   bug_u02_box_as_mut_field         -> FAILED ('assertion failed: b.x == 1')
//!   bug_v03_borrow_mut_box           -> FAILED ('assertion failed: b.x == 1')
//!   bug_x06_box_as_mut_closure       -> FAILED ('assertion failed: *b == 1')
//!   bug_x07_box_deref_mut_explicit   -> FAILED ('assertion failed: b.x == 1')
//!   bug_x08_as_mut_trait_generic     -> FAILED ('assertion failed: *b == 1')
//!
//! MECHANISM. `Box::as_mut` registers the reference's ref_target as
//! `b.[Field(Unique), Field(NonNull)]`: a place of type `NonNull<T>` whose
//! pointee is the reference's pointee `T`. The referent lives on the heap
//! behind that pointer, the Mem-level store writes it there, and the Box's
//! register holds only the pointer, which does not change. On main
//! e709ca52f59f the register mirror (`mirror_scalar_ref_store`) reached its
//! warn-only last arm and did nothing, which is right for this shape: every
//! row here matched Kani. The fail-closed change (compiler 804ecdaa4fd1) and
//! then the resolver's R4 join check (compiler 58c4145b9bb6) treated the
//! NonNull place as a join mismatch and havocked the Box's pointer slot, so
//! the next `*b` read an arbitrary address and tripped the alignment check:
//! every safe row became FAILED OverApproximation and every bug_ row lost its
//! Genuine certificate. `ref_mirror_join_check` now answers `ThroughPointer`
//! for a pointer-typed place whose pointee type is the reference's pointee,
//! and the mirror leaves the owner alone (compiler 8bc075c5541e).
//!
//! Lane scope: CHC only.
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options --harness-timeout=60s box_pointer_drill_dual.rs

use std::borrow::BorrowMut;

#[derive(Clone, Copy)]
struct Point { x: u32, y: u32 }

#[kani::proof]
fn u01_box_as_mut_scalar() {
    let mut b = Box::new(1u32);
    *b.as_mut() = 5;
    assert!(*b == 5);
}

#[kani::proof]
fn u02_box_as_mut_field() {
    let mut b = Box::new(Point { x: 1, y: 2 });
    b.as_mut().x = 5;
    assert!(b.x == 5 && b.y == 2);
}

#[kani::proof]
fn v03_borrow_mut_box() {
    let mut b = Box::new(Point { x: 1, y: 2 });
    let r: &mut Point = b.borrow_mut();
    r.x = 5;
    assert!(b.x == 5 && b.y == 2);
}

#[kani::proof]
fn v07_box_as_mut_twice() {
    let mut b = Box::new(Point { x: 1, y: 2 });
    b.as_mut().x = 5;
    b.as_mut().y = 6;
    assert!(b.x == 5 && b.y == 6);
}

#[kani::proof]
fn v08_box_as_mut_any() {
    let v: u32 = kani::any();
    kani::assume(v < 100);
    let mut b = Box::new(v);
    *b.as_mut() += 1;
    assert!(*b <= 100);
}

#[kani::proof]
fn v10_box_as_mut_then_read_other() {
    let mut a = Box::new(1u32);
    let b = Box::new(7u32);
    *a.as_mut() = 2;
    assert!(*b == 7 && *a == 2);
}

// Bug twins: Kani must FAIL these on the assertion.
#[kani::proof]
fn bug_u01_box_as_mut_scalar() {
    let mut b = Box::new(1u32);
    *b.as_mut() = 5;
    assert!(*b == 1);
}

#[kani::proof]
fn bug_u02_box_as_mut_field() {
    let mut b = Box::new(Point { x: 1, y: 2 });
    b.as_mut().x = 5;
    assert!(b.x == 1);
}


#[kani::proof]
fn x06_box_as_mut_closure() {
    let mut b = Box::new(1u32);
    let mut f = || { *b.as_mut() += 1; };
    f();
    assert!(*b == 2);
}

#[kani::proof]
fn x07_box_deref_mut_explicit() {
    use std::ops::DerefMut;
    let mut b = Box::new(Point { x: 1, y: 2 });
    b.deref_mut().x = 4;
    assert!(b.x == 4 && b.y == 2);
}

#[kani::proof]
fn x08_as_mut_trait_generic() {
    fn set<T: AsMut<u32>>(mut t: T) -> T { *t.as_mut() = 8; t }
    let b = set(Box::new(1u32));
    assert!(*b == 8);
}

#[kani::proof]
fn bug_v03_borrow_mut_box() {
    let mut b = Box::new(Point { x: 1, y: 2 });
    let r: &mut Point = b.borrow_mut();
    r.x = 5;
    assert!(b.x == 1);
}

#[kani::proof]
fn bug_x06_box_as_mut_closure() {
    let mut b = Box::new(1u32);
    let mut f = || { *b.as_mut() += 1; };
    f();
    assert!(*b == 1);
}

#[kani::proof]
fn bug_x07_box_deref_mut_explicit() {
    use std::ops::DerefMut;
    let mut b = Box::new(Point { x: 1, y: 2 });
    b.deref_mut().x = 4;
    assert!(b.x == 1);
}

#[kani::proof]
fn bug_x08_as_mut_trait_generic() {
    fn set<T: AsMut<u32>>(mut t: T) -> T { *t.as_mut() = 8; t }
    let b = set(Box::new(1u32));
    assert!(*b == 1);
}
