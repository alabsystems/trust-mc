// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z function-contracts
//
// T2 review (fix/chc-row72-small e14e943ba): a call inside a modifies frame whose
// `&mut` / interior-mutable `&` argument POINTEE lies in the footprint, but which
// writes storage OUTSIDE the footprint reachable through that pointee (a Vec's
// pre-existing buffer, the referent of a reference field). The FC-06 argument
// check passes; before T2 its own tag demoted the harness, after T2 nothing does.
//
// Oracle (Kani 0.67 at ~/tmc-measure/kani-src, 2026-09-24):
//   *_must_fail -> VERIFICATION:- FAILED ("Check that ... is assignable")
//   *_safe      -> VERIFICATION:- SUCCESSFUL
#![allow(dead_code)]
use std::cell::Cell;

struct CH<'a> { c: Cell<u32>, r: &'a Cell<u32> }
fn bump_other(h: &CH) { h.r.set(5); }
fn bump_own(h: &CH) { h.c.set(5); }
struct VW { v: Vec<u8>, n: u32 }
struct HM<'a> { n: u32, p: &'a mut u32 }
struct Holder<'a> { p: &'a mut u32 }
impl Holder<'_> { fn set(&mut self, v: u32) { *self.p = v; } }

// ---- Vec: modifies(v) names the 24-byte header; the buffer pre-exists ----
#[kani::modifies(v)]
fn vec_index(v: &mut Vec<u8>) { v[0] = 9; }
#[kani::proof_for_contract(vec_index)]
fn vec_index_header_footprint_must_fail() { let mut v: Vec<u8> = vec![1, 2]; vec_index(&mut v); }

#[kani::modifies(v)]
fn vec_index_u32(v: &mut Vec<u32>, i: usize) { if i < v.len() { v[i] = 9; } }
#[kani::proof_for_contract(vec_index_u32)]
fn vec_index_sym_header_footprint_must_fail() { let mut v: Vec<u32> = vec![kani::any(), kani::any()]; let i: usize = kani::any(); kani::assume(i < 2); vec_index_u32(&mut v, i); }

#[kani::modifies(v)]
fn vec_push_spare(v: &mut Vec<u8>) { v.push(7); }
#[kani::proof_for_contract(vec_push_spare)]
fn vec_push_spare_capacity_must_fail() { let mut v: Vec<u8> = Vec::with_capacity(4); v.push(1); vec_push_spare(&mut v); }

#[kani::modifies(v)]
fn vec_extend_spare(v: &mut Vec<u8>) { v.extend_from_slice(&[3]); }
#[kani::proof_for_contract(vec_extend_spare)]
fn vec_extend_spare_capacity_must_fail() { let mut v: Vec<u8> = Vec::with_capacity(4); v.push(1); vec_extend_spare(&mut v); }

#[kani::modifies(w)]
fn vw_index(w: &mut VW) { w.v[0] = 9; }
#[kani::proof_for_contract(vw_index)]
fn struct_vec_field_index_must_fail() { let mut w = VW { v: vec![1, 2], n: 0 }; vw_index(&mut w); }

// ---- a reference field to a Cell outside the footprint ----
#[kani::modifies(h)]
fn cell_holder(h: &CH) { bump_other(h); }
#[kani::proof_for_contract(cell_holder)]
fn cell_ref_field_heap_helper_must_fail() {
    let other: Box<Cell<u32>> = Box::new(Cell::new(kani::any()));
    let h = CH { c: Cell::new(0), r: &*other };
    cell_holder(&h);
}
#[kani::proof_for_contract(cell_holder)]
fn cell_ref_field_rc_helper_must_fail() {
    let other = std::rc::Rc::new(Cell::new(kani::any::<u32>()));
    let h = CH { c: Cell::new(0), r: &*other };
    cell_holder(&h);
}
#[kani::modifies(h)]
fn cell_holder_direct(h: &CH) { h.r.set(5); }
#[kani::proof_for_contract(cell_holder_direct)]
fn cell_ref_field_heap_direct_must_fail() {
    let other: Box<Cell<u32>> = Box::new(Cell::new(kani::any()));
    let h = CH { c: Cell::new(0), r: &*other };
    cell_holder_direct(&h);
}
// footprint = only the reference SLOT h.r; the write lands on its heap referent
#[kani::modifies(&h.r)]
fn set_via_r(h: &CH) { h.r.set(5); }
#[kani::proof_for_contract(set_via_r)]
fn cell_ref_slot_footprint_heap_must_fail() {
    let other: Box<Cell<u32>> = Box::new(Cell::new(kani::any()));
    let h = CH { c: Cell::new(0), r: &*other };
    set_via_r(&h);
}

// ---- pre-existing (SUCCESSFUL on main too): &mut field referent on the heap ----
#[kani::modifies(h)]
fn hm_store(h: &mut HM) { *h.p = 7; }
#[kani::proof_for_contract(hm_store)]
fn preexisting_mut_field_heap_direct_must_fail() {
    let mut bx: Box<u32> = Box::new(kani::any());
    let mut h = HM { n: 0, p: &mut *bx };
    hm_store(&mut h);
}
#[kani::modifies(h)]
fn holder_method(h: &mut Holder) { h.set(7); }
#[kani::proof_for_contract(holder_method)]
fn preexisting_mut_field_heap_method_must_fail() {
    let mut bx: Box<u32> = Box::new(kani::any());
    let mut h = Holder { p: &mut *bx };
    holder_method(&mut h);
}

// ---- safe controls ----
#[kani::modifies(h)]
fn cell_holder_own(h: &CH) { bump_own(h); }
#[kani::proof_for_contract(cell_holder_own)]
fn cell_own_field_safe() {
    let other: Box<Cell<u32>> = Box::new(Cell::new(kani::any()));
    let h = CH { c: Cell::new(0), r: &*other };
    cell_holder_own(&h);
}
#[kani::modifies(c)]
fn heap_cell_inside(c: &Cell<u32>) { c.set(5); }
#[kani::proof_for_contract(heap_cell_inside)]
fn heap_cell_inside_safe() {
    let c: Box<Cell<u32>> = Box::new(Cell::new(kani::any()));
    heap_cell_inside(&*c);
}
