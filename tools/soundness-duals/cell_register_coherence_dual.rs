// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL -- register-mirror coherence of the CHC Cell/RefCell store
//! lane, beyond the R5 tracker (cell_set_lost_write_dual.rs).
//!
//! The Cell store lane (trust-mc-compiler/src/codegen_ay/chc/call/
//! codegen_call_cell.rs) writes a `set`/`replace`/`take` to the referent's
//! memory mirror. The referent local keeps a second copy, its state variable,
//! which a whole-local borrow (`&c`, `&s`) copies back into memory. Every shape
//! below reached that re-mirror, or another stale read, on main 1f7de891d
//! (ay e7a607d9e, chc, 30 s): the bug_ rows proved SUCCESSFUL
//! [AY:PROOF_QUALIFIERS:clean] and their safe_ twins FAILED
//! [AY:CTREX_CAT:Genuine], except where the manifest note says otherwise.
//! The repair (codegen_call_cell_register.rs) binds the referent's state
//! variable to the stored value, supersedes a same-block assignment of it,
//! binds every slot of a flattened `get` result, and fails closed where the
//! register cannot be updated exactly and would be re-mirrored (every RefCell
//! store: its register is a (flag, value) pair the lane does not model).
//!
//! Oracle: the corpus-rev Kani 4c0fce8c3 (Kani 0.67.0) FAILS every bug_ row
//! on the assertion it carries and verifies every safe_ row (manifest entry).
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options --harness-timeout=30s cell_register_coherence_dual.rs

use std::cell::{Cell, RefCell};

struct S {
    a: u8,
    c: Cell<u8>,
}

#[inline(never)]
fn read_s(s: &S) -> u8 {
    s.c.get()
}

#[inline(never)]
fn set_it(c: &Cell<u8>) {
    c.set(200);
}

const CC: Cell<u8> = Cell::new(3);

// ---- a whole-struct borrow after a field store ------------------------------

#[kani::proof]
fn bug_field_whole_borrow() {
    let s = S { a: 1, c: Cell::new(0) };
    s.c.set(200);
    assert!(read_s(&s) < 100);
}

#[kani::proof]
fn safe_field_whole_borrow() {
    let s = S { a: 1, c: Cell::new(0) };
    s.c.set(200);
    assert!(read_s(&s) == 200 && s.a == 1);
}

// ---- the store through another reference ------------------------------------

#[kani::proof]
fn bug_ref_of_ref() {
    let c = Cell::new(0u8);
    let r = &c;
    let rr = &r;
    rr.set(200);
    assert!(c.get() < 100);
}

#[kani::proof]
fn safe_ref_of_ref() {
    let c = Cell::new(0u8);
    let r = &c;
    let rr = &r;
    rr.set(200);
    assert!(c.get() == 200);
}

#[kani::proof]
fn bug_closure_capture() {
    let c = Cell::new(0u8);
    let f = || c.set(200);
    f();
    assert!(c.get() < 100);
}

#[kani::proof]
fn safe_closure_capture() {
    let c = Cell::new(0u8);
    let f = || c.set(200);
    f();
    assert!(c.get() == 200);
}

#[kani::proof]
fn bug_callee_set() {
    let c = Cell::new(0u8);
    set_it(&c);
    assert!(c.get() < 100);
}

#[kani::proof]
fn safe_callee_set() {
    let c = Cell::new(0u8);
    set_it(&c);
    assert!(c.get() == 200);
}

// ---- payloads and accessors -------------------------------------------------

#[kani::proof]
fn bug_tuple_payload() {
    let c = Cell::new((0u8, 0u8));
    c.set((1, 2));
    assert!(c.get().1 == 0);
}

#[kani::proof]
fn safe_tuple_payload() {
    let c = Cell::new((0u8, 0u8));
    c.set((1, 2));
    assert!(c.get().1 == 2);
}

#[kani::proof]
fn bug_take() {
    let c = Cell::new(5u8);
    let old = c.take();
    assert!(old == 5);
    assert!(c.get() == 5);
}

#[kani::proof]
fn safe_take() {
    let c = Cell::new(5u8);
    let old = c.take();
    assert!(old == 5 && c.get() == 0);
}

#[kani::proof]
fn bug_cell_bool() {
    let c = Cell::new(false);
    c.set(true);
    assert!(!c.get());
}

#[kani::proof]
fn safe_cell_bool() {
    let c = Cell::new(false);
    c.set(true);
    assert!(c.get());
}

#[kani::proof]
fn bug_i64_replace_twice() {
    let c = Cell::new(-1i64);
    let a = c.replace(5);
    let b = c.replace(9);
    assert!(a == -1 && b == -1);
}

#[kani::proof]
fn safe_i64_replace_twice() {
    let c = Cell::new(-1i64);
    let a = c.replace(5);
    let b = c.replace(9);
    assert!(a == -1 && b == 5 && c.get() == 9);
}

#[kani::proof]
fn bug_set_as_ptr_read() {
    let c = Cell::new(0u8);
    c.set(200);
    assert!(unsafe { *c.as_ptr() } < 100);
}

#[kani::proof]
fn safe_set_as_ptr_read() {
    let c = Cell::new(0u8);
    c.set(200);
    assert!(unsafe { *c.as_ptr() } == 200);
}

// ---- repeated stores, reassignment, loops -----------------------------------

#[kani::proof]
fn bug_set_twice() {
    let c = Cell::new(0u8);
    c.set(7);
    let x = c.get();
    c.set(200);
    assert!(x == 7);
    assert!(c.get() < 100);
}

#[kani::proof]
fn safe_set_twice() {
    let c = Cell::new(0u8);
    c.set(7);
    let x = c.get();
    c.set(200);
    assert!(x == 7 && c.get() == 200);
}

#[kani::proof]
fn bug_mut_binding_reassign() {
    let mut c = Cell::new(0u8);
    c.set(7);
    assert!(c.get() == 7);
    c = Cell::new(1);
    c.set(200);
    assert!(c.get() < 100);
}

#[kani::proof]
fn safe_mut_binding_reassign() {
    let mut c = Cell::new(0u8);
    c.set(7);
    assert!(c.get() == 7);
    c = Cell::new(1);
    assert!(c.get() == 1);
    c.set(200);
    assert!(c.get() == 200);
}

#[kani::proof]
fn bug_const_item_cell() {
    let c = CC;
    c.set(200);
    assert!(c.get() == 3);
}

#[kani::proof]
fn safe_const_item_cell() {
    let c = CC;
    c.set(200);
    assert!(c.get() == 200);
}

#[kani::proof]
#[kani::unwind(5)]
fn bug_loop_set() {
    let c = Cell::new(0u8);
    let n: u8 = kani::any();
    kani::assume(n <= 3);
    let mut i = 0u8;
    while i < n {
        c.set(c.get() + 1);
        i += 1;
    }
    assert!(c.get() == 0);
}

#[kani::proof]
#[kani::unwind(5)]
fn safe_loop_set() {
    let c = Cell::new(0u8);
    let n: u8 = kani::any();
    kani::assume(n <= 3);
    let mut i = 0u8;
    while i < n {
        c.set(c.get() + 1);
        i += 1;
    }
    assert!(c.get() == n);
}

// ---- reachability: the paths through and around the store stay feasible ----

#[kani::proof]
fn bug_noset_path_reachable() {
    let b: bool = kani::any();
    let c = Cell::new(0u8);
    if b {
        c.set(200);
    }
    assert!(c.get() == 200);
}

#[kani::proof]
fn bug_after_set_reachable() {
    let c = Cell::new(0u8);
    c.set(200);
    let x = c.get();
    assert!(x != 200);
}

// ---- RefCell (fails closed where the register is re-mirrored) ---------------

#[kani::proof]
fn bug_refcell_replace_replace() {
    let r = RefCell::new(0u8);
    r.replace(200);
    let old = r.replace(1);
    assert!(old < 100);
}

#[kani::proof]
fn safe_refcell_replace_replace() {
    let r = RefCell::new(0u8);
    r.replace(200);
    let old = r.replace(1);
    assert!(old == 200);
}

#[kani::proof]
fn bug_refcell_replace_branch() {
    let r = RefCell::new(0u32);
    if kani::any() {
        r.replace(7);
    }
    assert!(r.replace(0) == 0);
}

#[kani::proof]
fn safe_refcell_replace_branch() {
    let b: bool = kani::any();
    let r = RefCell::new(0u32);
    if b {
        r.replace(7);
    }
    assert!(r.replace(0) == if b { 7 } else { 0 });
}

#[kani::proof]
fn bug_refcell_as_ptr_read() {
    let r = RefCell::new(0u8);
    r.replace(200);
    assert!(unsafe { *r.as_ptr() } < 100);
}

#[kani::proof]
fn safe_refcell_as_ptr_read() {
    let r = RefCell::new(0u8);
    r.replace(200);
    assert!(unsafe { *r.as_ptr() } == 200);
}

#[kani::proof]
fn bug_refcell_replace_get_mut() {
    let mut r = RefCell::new(0u8);
    r.replace(200);
    assert!(*r.get_mut() < 100);
}

#[kani::proof]
fn safe_refcell_replace_get_mut() {
    let mut r = RefCell::new(0u8);
    r.replace(200);
    assert!(*r.get_mut() == 200);
}
