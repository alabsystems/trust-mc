// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL -- the adversarial review of fix/chc-cell-set-write
//! (2026-09-26): shapes the first repair of the Cell register mirror
//! (cell_register_coherence_dual.rs) still got wrong, and the precision it
//! cost, one bug_/safe_ pair per shape.
//!
//! - RefCell stores whose referent the same block assigned: the havoc skipped
//!   a register the block had bound, so the check read SUCCESS on the stale
//!   value; and the RefCell lane read its payload at the object base, where
//!   the `&r` mirror keeps the BORROW FLAG (`RefCell::new(5).replace(6) == 0`
//!   verified SUCCESSFUL clean on main).
//! - A by-value move of an interior-mutable local after a store the register
//!   lane could not rebind (an array element, an enum payload).
//! - A Cell store inside a callee reached through a function pointer: the
//!   walker received the referent's VALUE and dropped the write.
//! - A projected re-assignment of a Cell place (`s.c = Cell::new(200)`) after
//!   a store: the register took it, the memory mirror kept the store.
//! - A `Cell<[T; N]>` payload: element 1 and up read stale (a whole-array load
//!   was forwarded one element, and the `&c` mirror stored the array whole).
//! - A quarantined Cell mutator (`swap`, `update`) havocked only its result.
//! - An atomic store to a struct field followed by a whole-struct borrow.
//! - A store through an `Rc`/`Vec`/phi pointer havocked every interior-mutable
//!   local of the body; an array element or enum payload store with an earlier
//!   whole borrow demoted the harness.
//!
//! Oracle: the corpus-rev Kani 4c0fce8c3 (Kani 0.67.0) FAILS every bug_ row on
//! the assertion it carries and verifies every safe_ row (manifest entry).
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options --harness-timeout=30s cell_register_review_dual.rs

use std::cell::{Cell, RefCell};
use std::rc::Rc;
use std::sync::atomic::{AtomicU8, Ordering::SeqCst};

struct S {
    a: u8,
    c: Cell<u8>,
}

struct T {
    x: u32,
    r: RefCell<u32>,
}

struct AC {
    k: u8,
    cells: [Cell<u8>; 2],
}

enum E {
    A(Cell<u8>),
    B(u8),
}

struct SA {
    k: u8,
    a: AtomicU8,
}

const RC: RefCell<u8> = RefCell::new(0);

fn set200(c: &Cell<u8>) {
    c.set(200)
}

fn set_via(c: &Cell<u8>, v: u8) {
    c.set(v)
}

fn set_s(s: &S) {
    s.c.set(200)
}

fn replace_ret(c: &Cell<u8>) -> u8 {
    c.replace(200)
}

#[inline(never)]
fn read_ac(s: &AC) -> u8 {
    s.cells[1].get()
}

#[inline(never)]
fn consume_ac(s: AC) -> u8 {
    s.cells[1].get()
}

#[inline(never)]
fn read_e(e: &E) -> u8 {
    match e {
        E::A(c) => c.get(),
        E::B(x) => *x,
    }
}

#[inline(never)]
fn read_sa(s: &SA) -> u8 {
    s.a.load(SeqCst)
}

fn sum2(a: &[Cell<u32>; 2]) -> u32 {
    a[0].get() + a[1].get()
}

// ---- RefCell: a referent the same block assigned ---------------------------

#[kani::proof]
fn bug_rc_struct_lit_whole() {
    let t = T { x: 1, r: RefCell::new(0) };
    t.r.replace(7);
    let rt = &t;
    assert!(rt.r.replace(1) == 0);
}

#[kani::proof]
fn safe_rc_struct_lit_whole() {
    let t = T { x: 1, r: RefCell::new(0) };
    t.r.replace(7);
    let rt = &t;
    assert!(rt.r.replace(1) == 7);
}

#[kani::proof]
fn bug_rc_const_local() {
    let r = RC;
    r.replace(200);
    assert!(r.replace(1) == 0);
}

#[kani::proof]
fn safe_rc_const_local() {
    let r = RC;
    r.replace(200);
    assert!(r.replace(1) == 200);
}

#[kani::proof]
fn bug_rc_field_assign_same_block() {
    let mut t = T { x: 0, r: RefCell::new(0) };
    let v: u32 = kani::any();
    t.x = v;
    t.r.replace(7);
    let rt = &t;
    assert!(rt.r.replace(1) == 0);
}

#[kani::proof]
fn safe_rc_field_assign_same_block() {
    let mut t = T { x: 0, r: RefCell::new(0) };
    let v: u32 = kani::any();
    t.x = v;
    t.r.replace(7);
    let rt = &t;
    assert!(rt.r.replace(1) == 7);
}

// ---- RefCell: the payload is not at the object base ------------------------

#[kani::proof]
fn bug_rc_replace_reads_flag() {
    let r = RefCell::new(5u32);
    let old = r.replace(6);
    assert!(old == 0);
}

#[kani::proof]
fn safe_rc_replace_reads_flag() {
    let r = RefCell::new(5u32);
    let old = r.replace(6);
    assert!(old == 5);
}

#[kani::proof]
fn bug_rc_sym_replace_zero() {
    let v: u32 = kani::any();
    kani::assume(v != 0);
    let r = RefCell::new(v);
    let old = r.replace(6);
    assert!(old == 0);
}

#[kani::proof]
fn safe_rc_sym_replace_zero() {
    let v: u32 = kani::any();
    kani::assume(v != 0);
    let r = RefCell::new(v);
    let old = r.replace(6);
    assert!(old == v);
}

// ---- a by-value move after an element or payload store ---------------------

#[kani::proof]
fn bug_ac_move_then_whole() {
    let s = AC { k: 1, cells: [Cell::new(0), Cell::new(0)] };
    s.cells[1].set(200);
    let t = s;
    assert!(read_ac(&t) == 0);
}

#[kani::proof]
fn safe_ac_move_then_whole() {
    let s = AC { k: 1, cells: [Cell::new(0), Cell::new(0)] };
    s.cells[1].set(200);
    let t = s;
    assert!(read_ac(&t) == 200 && t.k == 1);
}

#[kani::proof]
fn bug_ac_move_field_get() {
    let s = AC { k: 1, cells: [Cell::new(0), Cell::new(0)] };
    s.cells[1].set(200);
    let t = s;
    assert!(t.cells[1].get() == 0);
}

#[kani::proof]
fn safe_ac_move_field_get() {
    let s = AC { k: 1, cells: [Cell::new(0), Cell::new(0)] };
    s.cells[1].set(200);
    let t = s;
    assert!(t.cells[1].get() == 200);
}

#[kani::proof]
fn bug_ac_consume() {
    let s = AC { k: 1, cells: [Cell::new(0), Cell::new(0)] };
    s.cells[1].set(200);
    assert!(consume_ac(s) == 0);
}

#[kani::proof]
fn safe_ac_consume() {
    let s = AC { k: 1, cells: [Cell::new(0), Cell::new(0)] };
    s.cells[1].set(200);
    assert!(consume_ac(s) == 200);
}

#[kani::proof]
fn bug_enum_ref_pat_move() {
    let e = E::A(Cell::new(0));
    match e {
        E::A(ref c) => c.set(200),
        E::B(_) => {}
    }
    let f = e;
    assert!(read_e(&f) == 0);
}

#[kani::proof]
fn safe_enum_ref_pat_move() {
    let e = E::A(Cell::new(0));
    match e {
        E::A(ref c) => c.set(200),
        E::B(_) => {}
    }
    let f = e;
    assert!(read_e(&f) == 200);
}

// ---- a Cell store inside a callee reached through a function pointer --------

#[kani::proof]
fn bug_fnptr() {
    let c = Cell::new(0u8);
    let f: fn(&Cell<u8>) = set200;
    f(&c);
    assert!(c.get() < 100);
}

#[kani::proof]
fn safe_fnptr() {
    let c = Cell::new(0u8);
    let f: fn(&Cell<u8>) = set200;
    f(&c);
    assert!(c.get() == 200);
}

#[kani::proof]
fn bug_fnptr_any() {
    let v: u8 = kani::any();
    let c = Cell::new(0u8);
    let f: fn(&Cell<u8>, u8) = set_via;
    f(&c, v);
    assert!(c.get() == 0);
}

#[kani::proof]
fn safe_fnptr_any() {
    let v: u8 = kani::any();
    let c = Cell::new(0u8);
    let f: fn(&Cell<u8>, u8) = set_via;
    f(&c, v);
    assert!(c.get() == v);
}

#[kani::proof]
fn bug_closure_fnptr() {
    let c = Cell::new(0u8);
    let f: fn(&Cell<u8>) = |c| c.set(200);
    f(&c);
    assert!(c.get() < 100);
}

#[kani::proof]
fn safe_closure_fnptr() {
    let c = Cell::new(0u8);
    let f: fn(&Cell<u8>) = |c| c.set(200);
    f(&c);
    assert!(c.get() == 200);
}

#[kani::proof]
fn bug_struct_fnptr() {
    let s = S { a: 1, c: Cell::new(0) };
    let f: fn(&S) = set_s;
    f(&s);
    assert!(s.c.get() < 100);
}

#[kani::proof]
fn safe_struct_fnptr() {
    let s = S { a: 1, c: Cell::new(0) };
    let f: fn(&S) = set_s;
    f(&s);
    assert!(s.c.get() == 200 && s.a == 1);
}

#[kani::proof]
fn bug_replace_fnptr() {
    let c = Cell::new(7u8);
    let f: fn(&Cell<u8>) -> u8 = replace_ret;
    let old = f(&c);
    assert!(old == 7);
    assert!(c.get() == 7);
}

#[kani::proof]
fn safe_replace_fnptr() {
    let c = Cell::new(7u8);
    let f: fn(&Cell<u8>) -> u8 = replace_ret;
    let old = f(&c);
    assert!(old == 7 && c.get() == 200);
}

// ---- a projected re-assignment of a Cell place after a store ----------------

#[kani::proof]
fn bug_field_reassign() {
    let mut s = S { a: 1, c: Cell::new(0) };
    s.c.set(7);
    s.c = Cell::new(200);
    assert!(s.c.get() < 100);
}

#[kani::proof]
fn safe_field_reassign() {
    let mut s = S { a: 1, c: Cell::new(0) };
    s.c.set(7);
    s.c = Cell::new(200);
    assert!(s.c.get() == 200);
}

#[kani::proof]
fn bug_elem_reassign() {
    let mut a = [Cell::new(0u8), Cell::new(0u8)];
    a[0].set(7);
    a[0] = Cell::new(200);
    assert!(a[0].get() < 100);
}

#[kani::proof]
fn safe_elem_reassign() {
    let mut a = [Cell::new(0u8), Cell::new(0u8)];
    a[0].set(7);
    a[0] = Cell::new(200);
    assert!(a[0].get() == 200);
}

// ---- a Cell<[T; N]> payload -------------------------------------------------

#[kani::proof]
fn bug_arrpay_elem1() {
    let v: [u8; 2] = kani::any();
    kani::assume(v[1] != 0);
    let c = Cell::new([0u8; 2]);
    c.set(v);
    assert!(c.get()[1] == 0);
}

#[kani::proof]
fn safe_arrpay_elem1() {
    let v: [u8; 2] = kani::any();
    let c = Cell::new([0u8; 2]);
    c.set(v);
    assert!(c.get()[1] == v[1]);
}

#[kani::proof]
fn bug_arrpay_u32_replace() {
    let c = Cell::new([1u32, 2, 3]);
    c.replace([4, 5, 6]);
    assert!(c.get()[2] == 3);
}

#[kani::proof]
fn safe_arrpay_u32_replace() {
    let c = Cell::new([1u32, 2, 3]);
    let old = c.replace([4, 5, 6]);
    assert!(old[2] == 3 && c.get()[2] == 6);
}

// ---- quarantined Cell mutators (`swap`, `update`) -----------------------------

#[kani::proof]
fn bug_swap() {
    let a = Cell::new(1u8);
    let b = Cell::new(2u8);
    a.swap(&b);
    assert!(a.get() == 1);
}

#[kani::proof]
fn safe_swap() {
    let a = Cell::new(1u8);
    let b = Cell::new(2u8);
    a.swap(&b);
    assert!(a.get() == 2 && b.get() == 1);
}

#[kani::proof]
fn bug_update() {
    let c = Cell::new(1u8);
    c.update(|x| x + 10);
    assert!(c.get() == 1);
}

#[kani::proof]
fn safe_update() {
    let c = Cell::new(1u8);
    c.update(|x| x + 10);
    assert!(c.get() == 11);
}

// ---- an atomic store to a struct field, then a whole-struct borrow ----------

#[kani::proof]
fn bug_atomic_field_whole() {
    let s = SA { k: 1, a: AtomicU8::new(0) };
    s.a.store(200, SeqCst);
    assert!(read_sa(&s) < 100);
}

#[kani::proof]
fn safe_atomic_field_whole() {
    let s = SA { k: 1, a: AtomicU8::new(0) };
    s.a.store(200, SeqCst);
    assert!(read_sa(&s) == 200 && s.k == 1);
}

// ---- stores the register lane now keeps exact (precision) --------------------

#[kani::proof]
fn bug_rc_cell_with_local_cell() {
    let a = Cell::new(1u32);
    let b = Rc::new(Cell::new(0u32));
    b.set(7);
    assert!(a.get() == 2);
}

#[kani::proof]
fn safe_rc_cell_with_local_cell() {
    let a = Cell::new(1u32);
    let b = Rc::new(Cell::new(0u32));
    b.set(7);
    assert!(a.get() == 1 && b.get() == 7);
}

#[kani::proof]
fn bug_rc_cell_with_atomic() {
    let a = AtomicU8::new(5);
    let b = Rc::new(Cell::new(0u32));
    b.set(7);
    assert!(a.load(SeqCst) == 6);
}

#[kani::proof]
fn safe_rc_cell_with_atomic() {
    let a = AtomicU8::new(5);
    let b = Rc::new(Cell::new(0u32));
    b.set(7);
    assert!(a.load(SeqCst) == 5);
}

#[kani::proof]
fn bug_vec_cell_with_local_cell() {
    let a = Cell::new(3u32);
    let v = vec![Cell::new(0u32)];
    v[0].set(9);
    assert!(a.get() == 9);
}

#[kani::proof]
fn safe_vec_cell_with_local_cell() {
    let a = Cell::new(3u32);
    let v = vec![Cell::new(0u32)];
    v[0].set(9);
    assert!(a.get() == 3);
}

#[kani::proof]
fn bug_phi_ref() {
    let c1 = Cell::new(0u32);
    let c2 = Cell::new(0u32);
    let b: bool = kani::any();
    let r = if b { &c1 } else { &c2 };
    r.set(5);
    assert!(c1.get() + c2.get() == 0);
}

#[kani::proof]
fn safe_phi_ref() {
    let c1 = Cell::new(0u32);
    let c2 = Cell::new(0u32);
    let b: bool = kani::any();
    let r = if b { &c1 } else { &c2 };
    r.set(5);
    assert!(r.get() == 5);
}

#[kani::proof]
fn bug_arr_index_with_whole_borrow() {
    let arr = [Cell::new(0u32), Cell::new(0u32)];
    let r = &arr;
    arr[1].set(5);
    assert!(arr[1].get() == 0);
}

#[kani::proof]
fn safe_arr_index_with_whole_borrow() {
    let arr = [Cell::new(0u32), Cell::new(0u32)];
    let r = &arr;
    arr[1].set(5);
    assert!(arr[1].get() == 5);
    assert!(r[0].get() == 0);
}

#[kani::proof]
fn bug_arr_index_passed_whole() {
    let arr = [Cell::new(1u32), Cell::new(2u32)];
    arr[0].replace(10);
    assert!(sum2(&arr) == 3);
}

#[kani::proof]
fn safe_arr_index_passed_whole() {
    let arr = [Cell::new(1u32), Cell::new(2u32)];
    let old = arr[0].replace(10);
    assert!(old == 1);
    assert!(sum2(&arr) == 12);
}

#[kani::proof]
fn bug_option_cell_whole() {
    let o = Some(Cell::new(0u8));
    if let Some(c) = &o {
        c.set(200);
    }
    let ro = &o;
    assert!(ro.as_ref().unwrap().get() < 100);
}

#[kani::proof]
fn safe_option_cell_whole() {
    let o = Some(Cell::new(0u8));
    if let Some(c) = &o {
        c.set(200);
    }
    let ro = &o;
    assert!(ro.as_ref().unwrap().get() == 200);
}

#[kani::proof]
fn bug_view_same_block() {
    let mut x = 0u8;
    let c: &Cell<u8> = unsafe { &*(&mut x as *mut u8 as *const Cell<u8>) };
    c.set(200);
    assert!(x == 0);
}

#[kani::proof]
fn safe_view_same_block() {
    let mut x = 0u8;
    let c: &Cell<u8> = unsafe { &*(&mut x as *mut u8 as *const Cell<u8>) };
    c.set(200);
    assert!(x == 200);
}
