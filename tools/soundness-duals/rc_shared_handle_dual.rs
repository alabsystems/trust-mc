// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL -- two `Rc`/`Arc` handles to one allocation (the R5 review's
//! open item, docs/chc-hole-fix-designs-2026-09-24.md, "R5 review follow-up":
//! `let r2 = r.clone(); r2.set(200); r.get()`, probes p2.rs::safe_rc and
//! p4_shapes.rs::rc_cell_counter_safe). Traced on main d0ad2c7e8, the store
//! through one handle IS seen through the other; two other lanes certified the
//! false counterexamples:
//!
//! - DROP: `Rc::clone` is pointer identity and no strong count was kept, so
//!   every handle's drop freed the allocation. With a pointee the no-drop test
//!   refuses (`Cell<T>`: its generic field `UnsafeCell<T>` is never
//!   substituted), the second drop was a Genuine double free and a read through
//!   the surviving handle a Genuine use-after-free. With a pointee it accepts,
//!   no handle ever freed the allocation. Fixed by a strong-count state
//!   variable per cloned allocation site (rc_strong_count.rs): `new` sets 1, a
//!   clone adds 1, a drop subtracts 1 and frees the allocation only at 0.
//! - DEREF: `Rc::inner` calls `NonNull::as_ref(&(*self).ptr)` when the inliner
//!   leaves it, and that stub was pointer identity on its `&NonNull` argument:
//!   the result was the address of the `Rc` LOCAL, and `get()` read the stack
//!   slot 16 bytes past it. Fixed by reading the `NonNull` through the receiver
//!   (codegen_call_ptr_identity_cast.rs), or failing closed. The counter rows
//!   reach it (the first `Deref` of `other` stays a call); the `NonNull` field
//!   rows are guards (the inliner resolves their `as_ref`, and both bundles
//!   read them right).
//!
//! - ESCAPE (review of item 1): the pre-scan that decides a body's handles
//!   are all accounted for looked only at ADT generic arguments, so a clone
//!   moved into a non-generic `struct SD { r: Rc<D> }` or `enum ED { A(Rc<D>) }`
//!   and pushed into a `Vec` was counted: its real decrement, in the `Vec`'s
//!   element drop, never reached the count, the count stayed at 1, and the
//!   allocation was never freed nor its pointee dropped (the `bug_vec_*` rows
//!   were SUCCESSFUL clean). The pre-scan now looks through ADT fields, refuses
//!   any statement that reads a handle whole outside a move, an unsizing cast
//!   or a borrow, names core's `new`/`clone`/read-only methods by def path,
//!   refuses other `Rc`-family calls and a cloned site on a CFG cycle; such a
//!   body keeps the old encoding.
//!
//! Known-red (manifest): the loop and the raw-read-before-last-drop safe rows
//! are FAILED Unknown (the solver stops at 30 s), and
//! safe_rc_u32_raw_read_before_last_drop is a pre-existing false certificate
//! of another lane: `Rc::as_ptr` inlined, `&raw const (*inner).value` resolves
//! the `RcInner` pointer through a ref target naming the `Rc` local, so the
//! read lands 16 bytes into that 8-byte stack slot (main reads it the same).
//! safe_vec_struct_read_in_scope is FAILED Unknown on main and here, and
//! bug_vec_u64_uaf is a pre-existing missed bug of the old encoding's
//! clone-alias branch (a cloned allocation whose pointee passes the no-drop
//! test is never freed in a body the pre-scan refuses).
//!
//! Oracle: the corpus-rev Kani 4c0fce8c3 (Kani 0.67.0) FAILS every bug_ row on
//! the check it names and verifies every safe_ row (manifest entry).
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options --harness-timeout=30s rc_shared_handle_dual.rs

use std::cell::Cell;
use std::ptr::NonNull;
use std::rc::Rc;
use std::sync::Arc;
use std::sync::atomic::{AtomicU8, Ordering};

// ---- the review's two probes -------------------------------------------------

#[kani::proof]
fn bug_rc_set_through_clone() {
    let r = Rc::new(Cell::new(0u8));
    let r2 = r.clone();
    r2.set(200);
    assert!(r.get() < 100);
}

#[kani::proof]
fn safe_rc_set_through_clone() {
    let r = Rc::new(Cell::new(0u8));
    let r2 = r.clone();
    r2.set(200);
    assert!(r.get() == 200);
}

#[kani::proof]
fn bug_rc_counter() {
    let shared = Rc::new(Cell::new(0u32));
    let other = Rc::clone(&shared);
    other.set(other.get() + 1);
    assert!(shared.get() == 0);
}

#[kani::proof]
fn safe_rc_counter() {
    let shared = Rc::new(Cell::new(0u32));
    let other = Rc::clone(&shared);
    other.set(other.get() + 1);
    assert!(shared.get() == 1);
}

// ---- drops of shared handles --------------------------------------------------

#[kani::proof]
fn safe_rc_clone_then_scope_end() {
    let r = Rc::new(Cell::new(3u8));
    let _r2 = r.clone();
}

#[kani::proof]
fn bug_rc_read_after_clone_dropped() {
    let r = Rc::new(Cell::new(5u32));
    let r2 = r.clone();
    r2.set(6);
    drop(r2);
    assert!(r.get() == 5);
}

#[kani::proof]
fn safe_rc_read_after_clone_dropped() {
    let r = Rc::new(Cell::new(5u32));
    let r2 = r.clone();
    r2.set(6);
    drop(r2);
    assert!(r.get() == 6);
}

#[kani::proof]
fn bug_rc_raw_read_after_last_drop() {
    let r = Rc::new(Cell::new(5u32));
    let p = Rc::as_ptr(&r);
    let r2 = r.clone();
    drop(r);
    drop(r2);
    assert!(unsafe { (*p).get() } == 5);
}

#[kani::proof]
fn safe_rc_raw_read_before_last_drop() {
    let r = Rc::new(Cell::new(5u32));
    let p = Rc::as_ptr(&r);
    let r2 = r.clone();
    drop(r);
    assert!(unsafe { (*p).get() } == 5);
    drop(r2);
}

#[kani::proof]
fn bug_rc_u32_raw_read_after_last_drop() {
    let r = Rc::new(5u32);
    let p = Rc::as_ptr(&r);
    let r2 = r.clone();
    drop(r2);
    drop(r);
    assert!(unsafe { *p } == 5);
}

#[kani::proof]
fn safe_rc_u32_raw_read_before_last_drop() {
    let r = Rc::new(5u32);
    let p = Rc::as_ptr(&r);
    let r2 = r.clone();
    drop(r2);
    assert!(unsafe { *p } == 5);
}

#[kani::proof]
fn bug_rc_conditional_drop() {
    let r = Rc::new(Cell::new(1u8));
    let r2 = r.clone();
    if kani::any() {
        drop(r2);
    }
    r.set(2);
    assert!(r.get() == 1);
}

#[kani::proof]
fn safe_rc_conditional_drop() {
    let r = Rc::new(Cell::new(1u8));
    let r2 = r.clone();
    if kani::any() {
        drop(r2);
    }
    r.set(2);
    assert!(r.get() == 2);
}

#[kani::proof]
#[kani::unwind(4)]
fn bug_rc_clone_in_loop() {
    let r = Rc::new(Cell::new(0u8));
    for _ in 0..3 {
        let c = r.clone();
        c.set(c.get() + 1);
    }
    assert!(r.get() == 2);
}

#[kani::proof]
#[kani::unwind(4)]
fn safe_rc_clone_in_loop() {
    let r = Rc::new(Cell::new(0u8));
    for _ in 0..3 {
        let c = r.clone();
        c.set(c.get() + 1);
    }
    assert!(r.get() == 3);
}

#[kani::proof]
fn bug_arc_set_through_clone() {
    let a = Arc::new(Cell::new(0u16));
    let b = Arc::clone(&a);
    b.set(7);
    drop(b);
    assert!(a.get() == 0);
}

#[kani::proof]
fn safe_arc_set_through_clone() {
    let a = Arc::new(Cell::new(0u16));
    let b = Arc::clone(&a);
    b.set(7);
    drop(b);
    assert!(a.get() == 7);
}

// ---- NonNull::as_ref through a projected receiver (guards) --------------------

struct H {
    k: u8,
    p: NonNull<u8>,
}

#[kani::proof]
fn bug_nonnull_field_as_ref() {
    let x = 7u8;
    let h = H { k: 1, p: NonNull::from(&x) };
    let v = unsafe { *h.p.as_ref() };
    assert!(v == 8 || h.k != 1);
}

#[kani::proof]
fn safe_nonnull_field_as_ref() {
    let x = 7u8;
    let h = H { k: 1, p: NonNull::from(&x) };
    let v = unsafe { *h.p.as_ref() };
    assert!(v == 7 && h.k == 1);
}

// ---- a handle that leaves the tracked locals (review of item 1) ---------------
//
// A clone moved into a non-generic struct or enum and pushed into a Vec: the
// Vec's element drop releases it, out of the host's sight. Kani frees the
// allocation (and drops D) when the scope ends.

static DROPS: AtomicU8 = AtomicU8::new(0);

pub struct D(pub u64);

impl Drop for D {
    fn drop(&mut self) {
        DROPS.fetch_add(1, Ordering::SeqCst);
    }
}

pub struct SD {
    pub r: Rc<D>,
}

pub struct AD {
    pub r: Arc<D>,
}

pub enum ED {
    A(Rc<D>),
    B,
}

#[kani::proof]
fn bug_vec_struct_uaf() {
    let p: *const u64;
    {
        let a = Rc::new(D(7));
        p = &a.0 as *const u64;
        let mut v: Vec<SD> = Vec::new();
        v.push(SD { r: a.clone() });
    }
    let x = unsafe { *p };
    assert!(x == 7);
}

#[kani::proof]
fn bug_vec_struct_uaf_arc() {
    let p: *const u64;
    {
        let a = Arc::new(D(7));
        p = &a.0 as *const u64;
        let mut v: Vec<AD> = Vec::new();
        v.push(AD { r: a.clone() });
    }
    let x = unsafe { *p };
    assert!(x == 7);
}

#[kani::proof]
fn bug_vec_struct_pointee_never_dropped() {
    {
        let a = Rc::new(D(7));
        let mut v: Vec<SD> = Vec::new();
        v.push(SD { r: a.clone() });
    }
    assert!(DROPS.load(Ordering::SeqCst) == 0);
}

#[kani::proof]
fn bug_vec_enum_pointee_never_dropped() {
    {
        let a = Rc::new(D(7));
        let mut v: Vec<ED> = Vec::new();
        v.push(ED::A(a.clone()));
    }
    assert!(DROPS.load(Ordering::SeqCst) == 0);
}

#[kani::proof]
fn safe_vec_struct_read_in_scope() {
    let a = Rc::new(D(7));
    let p = &a.0 as *const u64;
    let mut v: Vec<SD> = Vec::new();
    v.push(SD { r: a.clone() });
    let x = unsafe { *p };
    assert!(x == 7);
}

// Known-red (pre-existing on main, another lane): the same escape with a
// pointee the no-drop test accepts. A body the pre-scan refuses keeps the old
// encoding, whose clone-alias branch skips the dealloc of every handle of a
// cloned allocation: it is never freed, and the read after the scope is missed.

pub struct SU {
    pub r: Rc<u64>,
}

#[kani::proof]
fn bug_vec_u64_uaf() {
    let p: *const u64;
    {
        let a = Rc::new(7u64);
        p = &*a as *const u64;
        let mut v: Vec<SU> = Vec::new();
        v.push(SU { r: a.clone() });
    }
    let x = unsafe { *p };
    assert!(x == 7);
}
