// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z function-contracts
//
// NEGATIVE PACK: stores outside a NON-EMPTY `#[kani::modifies]` footprint made
// where the frame classifier has no `&mut` to look at: interior mutability through
// a SHARED reference (`Cell`, `AtomicU32`, `RefCell`, `UnsafeCell`), raw pointers
// cast from a `&mut` (`*p = v`, `ptr::write`, `write_unaligned`, `write_volatile`),
// `mem::replace` / `mem::swap`, an element of `&mut [T]` / `&mut [T; N]`, a field
// reached by pointer offset from a covered field, a `static` written through a raw
// pointer, plus the zero-count `write_bytes` / `copy` and the reborrow that stay
// inside the footprint.
//
// Written by the adversarial review of m3/soundness-fixes-2 (2026-09-13) against
// statement/modifies_frame.rs, modifies_frame_calls.rs (64749f9a3) and
// chc/modifies_frame.rs (7cf7fa252).
//
// Oracle (per harness):
//   *_must_fail   -> VERIFICATION:- FAILED (frame); never SUCCESSFUL
//   *_safe        -> never a Genuine counterexample

use std::cell::{Cell, RefCell, UnsafeCell};
use std::sync::atomic::{AtomicU32, Ordering};

#[repr(C)]
struct Pair {
    a: u32,
    b: u32,
}

static mut G: u32 = 0;

#[kani::modifies(a)]
fn cell_outside(a: &mut u32, c: &Cell<u32>) {
    c.set(1);
    *a = 1;
}

#[kani::proof_for_contract(cell_outside)]
fn cell_shared_store_must_fail() {
    let mut a: u32 = kani::any();
    let c = Cell::new(kani::any());
    cell_outside(&mut a, &c);
}

#[kani::modifies(c)]
fn cell_inside(c: &Cell<u32>) {
    c.set(1);
}

#[kani::proof_for_contract(cell_inside)]
fn cell_shared_store_safe() {
    let c = Cell::new(kani::any());
    cell_inside(&c);
}

#[kani::modifies(a)]
fn atomic_outside(a: &mut u32, c: &AtomicU32) {
    c.store(1, Ordering::SeqCst);
    *a = 1;
}

#[kani::proof_for_contract(atomic_outside)]
fn atomic_shared_store_must_fail() {
    let mut a: u32 = kani::any();
    let c = AtomicU32::new(kani::any());
    atomic_outside(&mut a, &c);
}

#[kani::modifies(a)]
fn atomic_fetch_add_outside(a: &mut u32, c: &AtomicU32) {
    c.fetch_add(1, Ordering::SeqCst);
    *a = 1;
}

#[kani::proof_for_contract(atomic_fetch_add_outside)]
fn atomic_fetch_add_must_fail() {
    let mut a: u32 = kani::any();
    let c = AtomicU32::new(kani::any());
    atomic_fetch_add_outside(&mut a, &c);
}

#[kani::modifies(a)]
fn refcell_outside(a: &mut u32, c: &RefCell<u32>) {
    *c.borrow_mut() = 1;
    *a = 1;
}

#[kani::proof_for_contract(refcell_outside)]
fn refcell_shared_store_must_fail() {
    let mut a: u32 = kani::any();
    let c = RefCell::new(kani::any());
    refcell_outside(&mut a, &c);
}

#[kani::modifies(a)]
fn unsafecell_outside(a: &mut u32, c: &UnsafeCell<u32>) {
    unsafe { *c.get() = 1 };
    *a = 1;
}

#[kani::proof_for_contract(unsafecell_outside)]
fn unsafecell_shared_store_must_fail() {
    let mut a: u32 = kani::any();
    let c = UnsafeCell::new(kani::any());
    unsafecell_outside(&mut a, &c);
}

#[kani::modifies(a)]
fn raw_cast_outside(a: &mut u32, b: &mut u32) {
    let p = b as *mut u32;
    unsafe { *p = 1 };
    *a = 1;
}

#[kani::proof_for_contract(raw_cast_outside)]
fn raw_cast_store_must_fail() {
    let mut a: u32 = kani::any();
    let mut b: u32 = kani::any();
    raw_cast_outside(&mut a, &mut b);
}

#[kani::modifies(a)]
fn raw_cast_inside(a: &mut u32) {
    let p = a as *mut u32;
    unsafe { *p = 1 };
}

#[kani::proof_for_contract(raw_cast_inside)]
fn raw_cast_store_safe() {
    let mut a: u32 = kani::any();
    raw_cast_inside(&mut a);
}

#[kani::modifies(a)]
fn ptr_write_outside(a: &mut u32, b: &mut u32) {
    unsafe { std::ptr::write(b, 1) };
    *a = 1;
}

#[kani::proof_for_contract(ptr_write_outside)]
fn ptr_write_store_must_fail() {
    let mut a: u32 = kani::any();
    let mut b: u32 = kani::any();
    ptr_write_outside(&mut a, &mut b);
}

#[kani::modifies(a)]
fn ptr_write_unaligned_outside(a: &mut u32, b: &mut u32) {
    unsafe { std::ptr::write_unaligned(b, 1) };
    *a = 1;
}

#[kani::proof_for_contract(ptr_write_unaligned_outside)]
fn ptr_write_unaligned_store_must_fail() {
    let mut a: u32 = kani::any();
    let mut b: u32 = kani::any();
    ptr_write_unaligned_outside(&mut a, &mut b);
}

#[kani::modifies(a)]
fn ptr_write_volatile_outside(a: &mut u32, b: &mut u32) {
    unsafe { std::ptr::write_volatile(b, 1) };
    *a = 1;
}

#[kani::proof_for_contract(ptr_write_volatile_outside)]
fn ptr_write_volatile_store_must_fail() {
    let mut a: u32 = kani::any();
    let mut b: u32 = kani::any();
    ptr_write_volatile_outside(&mut a, &mut b);
}

#[kani::modifies(a)]
fn mem_replace_outside(a: &mut u32, b: &mut u32) {
    let _old = std::mem::replace(b, 1);
    *a = 1;
}

#[kani::proof_for_contract(mem_replace_outside)]
fn mem_replace_store_must_fail() {
    let mut a: u32 = kani::any();
    let mut b: u32 = kani::any();
    mem_replace_outside(&mut a, &mut b);
}

#[kani::modifies(a)]
fn mem_swap_outside(a: &mut u32, b: &mut u32) {
    std::mem::swap(a, b);
}

#[kani::proof_for_contract(mem_swap_outside)]
fn mem_swap_store_must_fail() {
    let mut a: u32 = kani::any();
    let mut b: u32 = kani::any();
    mem_swap_outside(&mut a, &mut b);
}

#[kani::modifies(a, b)]
fn mem_swap_inside(a: &mut u32, b: &mut u32) {
    std::mem::swap(a, b);
}

#[kani::proof_for_contract(mem_swap_inside)]
fn mem_swap_store_safe() {
    let mut a: u32 = kani::any();
    let mut b: u32 = kani::any();
    mem_swap_inside(&mut a, &mut b);
}

#[kani::modifies(a)]
fn slice_elem_outside(a: &mut u32, s: &mut [u32]) {
    s[0] = 1;
    *a = 1;
}

#[kani::proof_for_contract(slice_elem_outside)]
fn slice_elem_store_must_fail() {
    let mut a: u32 = kani::any();
    let mut s = [0u32; 2];
    slice_elem_outside(&mut a, &mut s);
}

#[kani::modifies(a)]
fn array_ref_elem_outside(a: &mut u32, s: &mut [u32; 2]) {
    s[1] = 1;
    *a = 1;
}

#[kani::proof_for_contract(array_ref_elem_outside)]
fn array_ref_elem_store_must_fail() {
    let mut a: u32 = kani::any();
    let mut s = [0u32; 2];
    array_ref_elem_outside(&mut a, &mut s);
}

#[kani::modifies(s)]
fn array_ref_elem_inside(s: &mut [u32; 2]) {
    s[1] = 1;
}

#[kani::proof_for_contract(array_ref_elem_inside)]
fn array_ref_elem_store_safe() {
    let mut s = [0u32; 2];
    array_ref_elem_inside(&mut s);
}

#[kani::modifies(s)]
fn slice_elem_symbolic_inside(s: &mut [u32], i: usize) {
    if i < s.len() {
        s[i] = 1;
    }
}

#[kani::proof_for_contract(slice_elem_symbolic_inside)]
fn slice_elem_symbolic_store_safe() {
    let mut s = [0u32; 3];
    let i: usize = kani::any();
    slice_elem_symbolic_inside(&mut s, i);
}

#[kani::modifies(&p.a)]
fn field_offset_escape(p: &mut Pair) {
    let q = &mut p.a as *mut u32;
    unsafe { *q.add(1) = 1 };
}

#[kani::proof_for_contract(field_offset_escape)]
fn field_offset_escape_must_fail() {
    let mut p = Pair { a: kani::any(), b: kani::any() };
    field_offset_escape(&mut p);
}

#[kani::modifies(&p.a)]
fn field_other_outside(p: &mut Pair) {
    p.b = 1;
}

#[kani::proof_for_contract(field_other_outside)]
fn field_other_store_must_fail() {
    let mut p = Pair { a: kani::any(), b: kani::any() };
    field_other_outside(&mut p);
}

#[kani::modifies(&p.a)]
fn field_inside(p: &mut Pair) {
    p.a = 1;
}

#[kani::proof_for_contract(field_inside)]
fn field_store_safe() {
    let mut p = Pair { a: kani::any(), b: kani::any() };
    field_inside(&mut p);
}

#[kani::modifies(&p.a)]
fn field_via_raw_inside(p: &mut Pair) {
    let q = &mut p.a as *mut u32;
    unsafe { *q = 1 };
}

#[kani::proof_for_contract(field_via_raw_inside)]
fn field_via_raw_store_safe() {
    let mut p = Pair { a: kani::any(), b: kani::any() };
    field_via_raw_inside(&mut p);
}

#[kani::modifies(a)]
fn static_via_ptr_outside(a: &mut u32) {
    let p = &raw mut G;
    unsafe { *p = 1 };
    *a = 1;
}

#[kani::proof_for_contract(static_via_ptr_outside)]
fn static_via_ptr_store_must_fail() {
    let mut a: u32 = kani::any();
    static_via_ptr_outside(&mut a);
}

#[kani::modifies(a)]
fn reborrow_inside(a: &mut u32) {
    let r = &mut *a;
    *r = 1;
}

#[kani::proof_for_contract(reborrow_inside)]
fn reborrow_store_safe() {
    let mut a: u32 = kani::any();
    reborrow_inside(&mut a);
}

#[kani::modifies(a)]
fn write_bytes_zero_count(a: &mut u32, b: &mut u32) {
    unsafe { std::ptr::write_bytes(b, 0, 0) };
    *a = 1;
}

#[kani::proof_for_contract(write_bytes_zero_count)]
fn write_bytes_zero_count_safe() {
    let mut a: u32 = kani::any();
    let mut b: u32 = kani::any();
    write_bytes_zero_count(&mut a, &mut b);
}

#[kani::modifies(a)]
fn copy_zero_count(a: &mut u32, b: &mut u32) {
    unsafe { std::ptr::copy(a, b, 0) };
    *a = 1;
}

#[kani::proof_for_contract(copy_zero_count)]
fn copy_zero_count_safe() {
    let mut a: u32 = kani::any();
    let mut b: u32 = kani::any();
    copy_zero_count(&mut a, &mut b);
}

#[kani::modifies(a)]
fn write_bytes_one_count_outside(a: &mut u32, b: &mut u32) {
    unsafe { std::ptr::write_bytes(b, 0, 1) };
    *a = 1;
}

#[kani::proof_for_contract(write_bytes_one_count_outside)]
fn write_bytes_one_count_must_fail() {
    let mut a: u32 = kani::any();
    let mut b: u32 = kani::any();
    write_bytes_one_count_outside(&mut a, &mut b);
}
