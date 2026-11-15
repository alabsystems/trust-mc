// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z function-contracts
//
// NEGATIVE PACK: stores outside a NON-EMPTY `#[kani::modifies]` footprint made
// through a closure capture, a struct field holding a `&mut`, a trait object, a
// generic callee, a contracted callee, a `Box`, a `static`, an `Option<&mut T>`,
// an array of `&mut`, a loop, `Vec::{insert, extend_from_slice, clear,
// truncate}`, `mem::take`, and `ptr::write_bytes` / `ptr::copy` with a symbolic
// count. Written by the adversarial review of m3/soundness-fixes-2 (2026-09-12)
// against the BMC frame classifier's name-based attribution
// (statement/modifies_frame.rs, modifies_frame_calls.rs) and the CHC
// address-range checks (chc/modifies_frame.rs).
//
// Oracle (per harness):
//   *_must_fail   -> VERIFICATION:- FAILED (frame); never SUCCESSFUL
//   *_safe        -> never a Genuine counterexample

use std::sync::atomic::{AtomicU32, Ordering};

#[repr(C)]
struct Pair {
    a: u32,
    b: u32,
}

struct Holder<'a> {
    p: &'a mut u32,
}

impl Holder<'_> {
    fn set(&mut self, v: u32) {
        *self.p = v;
    }
}

trait Sink {
    fn put(&mut self, v: u32);
}

struct W<'a>(&'a mut u32);

impl Sink for W<'_> {
    fn put(&mut self, v: u32) {
        *self.0 = v;
    }
}

fn set_generic<T: Copy>(p: &mut T, v: T) {
    *p = v;
}

static mut G: u32 = 0;
static COUNTER: AtomicU32 = AtomicU32::new(0);

// ---- closure capture ----

#[kani::modifies(a)]
fn closure_outside(a: &mut u32, b: &mut u32) {
    let mut g = || {
        *b = 1;
    };
    g();
    *a = 1;
}

#[kani::proof_for_contract(closure_outside)]
fn closure_capture_write_must_fail() {
    let mut a: u32 = kani::any();
    let mut b: u32 = kani::any();
    closure_outside(&mut a, &mut b);
}

#[kani::modifies(a)]
fn closure_inside(a: &mut u32) {
    let mut g = || {
        *a = 1;
    };
    g();
}

#[kani::proof_for_contract(closure_inside)]
fn closure_capture_write_safe() {
    let mut a: u32 = kani::any();
    closure_inside(&mut a);
}

// ---- struct field holding a `&mut` ----

#[kani::modifies(a)]
fn holder_method_outside(a: &mut u32, b: &mut u32) {
    let mut h = Holder { p: b };
    h.set(1);
    *a = 1;
}

#[kani::proof_for_contract(holder_method_outside)]
fn struct_field_ptr_method_write_must_fail() {
    let mut a: u32 = kani::any();
    let mut b: u32 = kani::any();
    holder_method_outside(&mut a, &mut b);
}

#[kani::modifies(a)]
fn holder_method_inside(a: &mut u32) {
    let mut h = Holder { p: a };
    h.set(1);
}

#[kani::proof_for_contract(holder_method_inside)]
fn struct_field_ptr_method_write_safe() {
    let mut a: u32 = kani::any();
    holder_method_inside(&mut a);
}

#[kani::modifies(a)]
fn holder_direct_outside(a: &mut u32, b: &mut u32) {
    let mut h = Holder { p: b };
    *h.p = 1;
    *a = 1;
}

#[kani::proof_for_contract(holder_direct_outside)]
fn struct_field_ptr_direct_write_must_fail() {
    let mut a: u32 = kani::any();
    let mut b: u32 = kani::any();
    holder_direct_outside(&mut a, &mut b);
}

// ---- trait object ----

#[kani::modifies(a)]
fn dyn_outside(a: &mut u32, b: &mut u32) {
    let mut w = W(b);
    let d: &mut dyn Sink = &mut w;
    d.put(1);
    *a = 1;
}

#[kani::proof_for_contract(dyn_outside)]
fn trait_object_write_must_fail() {
    let mut a: u32 = kani::any();
    let mut b: u32 = kani::any();
    dyn_outside(&mut a, &mut b);
}

#[kani::modifies(a)]
fn dyn_inside(a: &mut u32) {
    let mut w = W(a);
    let d: &mut dyn Sink = &mut w;
    d.put(1);
}

#[kani::proof_for_contract(dyn_inside)]
fn trait_object_write_safe() {
    let mut a: u32 = kani::any();
    dyn_inside(&mut a);
}

// ---- generic callee ----

#[kani::modifies(a)]
fn generic_outside(a: &mut u32, b: &mut u32) {
    set_generic(b, 1);
    *a = 1;
}

#[kani::proof_for_contract(generic_outside)]
fn generic_callee_write_must_fail() {
    let mut a: u32 = kani::any();
    let mut b: u32 = kani::any();
    generic_outside(&mut a, &mut b);
}

#[kani::modifies(a)]
fn generic_inside(a: &mut u32) {
    set_generic(a, 1);
}

#[kani::proof_for_contract(generic_inside)]
fn generic_callee_write_safe() {
    let mut a: u32 = kani::any();
    generic_inside(&mut a);
}

// ---- contract calling a contracted callee ----

#[kani::modifies(b)]
fn inner_writes(b: &mut u32) {
    *b = 1;
}

#[kani::modifies(a)]
fn outer_calls_inner(a: &mut u32, b: &mut u32) {
    inner_writes(b);
    *a = 1;
}

#[kani::proof_for_contract(outer_calls_inner)]
fn contract_callee_outside_must_fail() {
    let mut a: u32 = kani::any();
    let mut b: u32 = kani::any();
    outer_calls_inner(&mut a, &mut b);
}

#[kani::modifies(a)]
fn inner_writes_a(a: &mut u32) {
    *a = 1;
}

#[kani::modifies(a)]
fn outer_calls_inner_same(a: &mut u32) {
    inner_writes_a(a);
}

#[kani::proof_for_contract(outer_calls_inner_same)]
fn contract_callee_inside_safe() {
    let mut a: u32 = kani::any();
    outer_calls_inner_same(&mut a);
}

// ---- Box ----

#[kani::modifies(a)]
fn box_outside(a: &mut u32, b: &mut Box<u32>) {
    **b = 1;
    *a = 1;
}

#[kani::proof_for_contract(box_outside)]
fn box_deref_store_must_fail() {
    let mut a: u32 = kani::any();
    let mut b: Box<u32> = Box::new(kani::any());
    box_outside(&mut a, &mut b);
}

#[kani::modifies(a)]
fn box_inside(a: &mut u32) {
    let mut bx: Box<u32> = Box::new(0);
    *bx = 1;
    *a = *bx;
}

#[kani::proof_for_contract(box_inside)]
fn box_local_store_safe() {
    let mut a: u32 = kani::any();
    box_inside(&mut a);
}

// ---- statics ----

#[kani::modifies(a)]
fn static_outside(a: &mut u32) {
    unsafe {
        G = 1;
    }
    *a = 1;
}

#[kani::proof_for_contract(static_outside)]
fn static_mut_store_must_fail() {
    let mut a: u32 = kani::any();
    static_outside(&mut a);
}

#[kani::modifies(a)]
fn static_read(a: &mut u32) {
    *a = unsafe { G };
}

#[kani::proof_for_contract(static_read)]
fn static_mut_read_safe() {
    let mut a: u32 = kani::any();
    static_read(&mut a);
}

#[kani::modifies(a)]
fn atomic_static_outside(a: &mut u32) {
    COUNTER.store(1, Ordering::SeqCst);
    *a = 1;
}

#[kani::proof_for_contract(atomic_static_outside)]
fn atomic_static_store_must_fail() {
    let mut a: u32 = kani::any();
    atomic_static_outside(&mut a);
}

// ---- Option<&mut T> ----

#[kani::modifies(a)]
fn option_outside(a: &mut u32, b: Option<&mut u32>) {
    if let Some(r) = b {
        *r = 1;
    }
    *a = 1;
}

#[kani::proof_for_contract(option_outside)]
fn option_ref_store_must_fail() {
    let mut a: u32 = kani::any();
    let mut b: u32 = kani::any();
    option_outside(&mut a, Some(&mut b));
}

// ---- array of `&mut` with a symbolic index ----

#[kani::modifies(a)]
fn array_ptrs_outside(a: &mut u32, b: &mut u32, i: usize) {
    let mut ptrs: [&mut u32; 2] = [a, b];
    *ptrs[i] = 1;
}

#[kani::proof_for_contract(array_ptrs_outside)]
fn array_of_refs_store_must_fail() {
    let mut a: u32 = kani::any();
    let mut b: u32 = kani::any();
    let i: usize = kani::any();
    kani::assume(i < 2);
    array_ptrs_outside(&mut a, &mut b, i);
}

#[kani::modifies(a, b)]
fn array_ptrs_covered(a: &mut u32, b: &mut u32, i: usize) {
    let mut ptrs: [&mut u32; 2] = [a, b];
    *ptrs[i] = 1;
}

#[kani::proof_for_contract(array_ptrs_covered)]
fn array_of_refs_store_safe() {
    let mut a: u32 = kani::any();
    let mut b: u32 = kani::any();
    let i: usize = kani::any();
    kani::assume(i < 2);
    array_ptrs_covered(&mut a, &mut b, i);
}

// ---- loop ----

#[kani::modifies(a)]
fn loop_outside(a: &mut u32, b: &mut u32, n: u8) {
    let mut i = 0u8;
    while i < n {
        *b = (*b).wrapping_add(1);
        i += 1;
    }
    *a = 1;
}

#[kani::proof_for_contract(loop_outside)]
#[kani::unwind(4)]
fn loop_store_outside_must_fail() {
    let mut a: u32 = kani::any();
    let mut b: u32 = kani::any();
    let n: u8 = kani::any();
    kani::assume(n >= 1 && n < 3);
    loop_outside(&mut a, &mut b, n);
}

#[kani::modifies(a)]
fn loop_inside(a: &mut u32, n: u8) {
    let mut i = 0u8;
    while i < n {
        *a = (*a).wrapping_add(1);
        i += 1;
    }
}

#[kani::proof_for_contract(loop_inside)]
#[kani::unwind(4)]
fn loop_store_inside_safe() {
    let mut a: u32 = kani::any();
    let n: u8 = kani::any();
    kani::assume(n < 3);
    loop_inside(&mut a, n);
}

// ---- Vec operations outside the footprint ----

#[kani::modifies(&p.a)]
fn vec_insert_outside(p: &mut Pair, v: &mut Vec<u8>) {
    p.a = 1;
    v.insert(0, 7);
}

#[kani::proof_for_contract(vec_insert_outside)]
fn vec_insert_outside_must_fail() {
    let mut p = Pair { a: kani::any(), b: kani::any() };
    let mut v: Vec<u8> = vec![1, 2];
    vec_insert_outside(&mut p, &mut v);
}

#[kani::modifies(&p.a)]
fn vec_extend_outside(p: &mut Pair, v: &mut Vec<u8>) {
    p.a = 1;
    v.extend_from_slice(&[1, 2]);
}

#[kani::proof_for_contract(vec_extend_outside)]
fn vec_extend_outside_must_fail() {
    let mut p = Pair { a: kani::any(), b: kani::any() };
    let mut v: Vec<u8> = vec![1, 2];
    vec_extend_outside(&mut p, &mut v);
}

#[kani::modifies(&p.a)]
fn vec_clear_outside(p: &mut Pair, v: &mut Vec<u8>) {
    p.a = 1;
    v.clear();
}

#[kani::proof_for_contract(vec_clear_outside)]
fn vec_clear_outside_must_fail() {
    let mut p = Pair { a: kani::any(), b: kani::any() };
    let mut v: Vec<u8> = vec![1, 2];
    vec_clear_outside(&mut p, &mut v);
}

#[kani::modifies(&p.a)]
fn vec_truncate_outside(p: &mut Pair, v: &mut Vec<u8>) {
    p.a = 1;
    v.truncate(1);
}

#[kani::proof_for_contract(vec_truncate_outside)]
fn vec_truncate_outside_must_fail() {
    let mut p = Pair { a: kani::any(), b: kani::any() };
    let mut v: Vec<u8> = vec![1, 2];
    vec_truncate_outside(&mut p, &mut v);
}

#[kani::modifies(&p.a)]
fn vec_take_outside(p: &mut Pair, v: &mut Vec<u8>) {
    p.a = 1;
    let _old = std::mem::take(v);
}

#[kani::proof_for_contract(vec_take_outside)]
fn vec_take_outside_must_fail() {
    let mut p = Pair { a: kani::any(), b: kani::any() };
    let mut v: Vec<u8> = vec![1, 2];
    vec_take_outside(&mut p, &mut v);
}

#[kani::modifies(v)]
fn vec_clear_inside(v: &mut Vec<u8>) {
    v.clear();
}

#[kani::proof_for_contract(vec_clear_inside)]
fn vec_clear_inside_safe() {
    let mut v: Vec<u8> = vec![1, 2];
    vec_clear_inside(&mut v);
}

#[kani::modifies(v)]
fn vec_insert_inside(v: &mut Vec<u8>) {
    v.insert(0, 7);
}

#[kani::proof_for_contract(vec_insert_inside)]
fn vec_insert_inside_safe() {
    let mut v: Vec<u8> = vec![1, 2];
    vec_insert_inside(&mut v);
}

// ---- write_bytes / copy with a symbolic count ----

#[kani::modifies(&p.a)]
fn write_bytes_symbolic_outside(p: &mut Pair, q: &mut [u8; 4], n: usize) {
    p.a = 1;
    unsafe { std::ptr::write_bytes(q.as_mut_ptr(), 0xAB, n) };
}

#[kani::proof_for_contract(write_bytes_symbolic_outside)]
fn write_bytes_symbolic_count_outside_must_fail() {
    let mut p = Pair { a: kani::any(), b: kani::any() };
    let mut q = [0u8; 4];
    let n: usize = kani::any();
    kani::assume(n >= 1 && n <= 4);
    write_bytes_symbolic_outside(&mut p, &mut q, n);
}

#[kani::modifies(q)]
fn write_bytes_symbolic_inside(q: &mut [u8; 4], n: usize) {
    unsafe { std::ptr::write_bytes(q.as_mut_ptr(), 0xAB, n) };
}

#[kani::proof_for_contract(write_bytes_symbolic_inside)]
fn write_bytes_symbolic_count_inside_safe() {
    let mut q = [0u8; 4];
    let n: usize = kani::any();
    kani::assume(n <= 4);
    write_bytes_symbolic_inside(&mut q, n);
}

#[kani::modifies(&p.a)]
fn copy_symbolic_outside(p: &mut Pair, q: &mut [u8; 4], n: usize) {
    p.a = 1;
    let src = [9u8; 4];
    unsafe { std::ptr::copy(src.as_ptr(), q.as_mut_ptr(), n) };
}

#[kani::proof_for_contract(copy_symbolic_outside)]
fn copy_symbolic_count_outside_must_fail() {
    let mut p = Pair { a: kani::any(), b: kani::any() };
    let mut q = [0u8; 4];
    let n: usize = kani::any();
    kani::assume(n >= 1 && n <= 4);
    copy_symbolic_outside(&mut p, &mut q, n);
}

#[kani::modifies(q)]
fn copy_symbolic_inside(q: &mut [u8; 4], n: usize) {
    let src = [9u8; 4];
    unsafe { std::ptr::copy(src.as_ptr(), q.as_mut_ptr(), n) };
}

#[kani::proof_for_contract(copy_symbolic_inside)]
fn copy_symbolic_count_inside_safe() {
    let mut q = [0u8; 4];
    let n: usize = kani::any();
    kani::assume(n <= 4);
    copy_symbolic_inside(&mut q, n);
}
