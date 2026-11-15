// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z function-contracts
//
// NEGATIVE PACK: variants of negative/modifies_frame_residual.rs.
//
// Found while fixing that file (2026-09-12). Measured on bundle 31793ccc3:
//   bmc SUCCESSFUL on string_push, vec_pop, callee_merge, early_return_pick;
//   chc SUCCESSFUL on string_push, vec_pop, swap, copy_nonoverlapping,
//   write_unaligned, callee_merge, early_return_pick.
// Covered constructs: a path merge through a loop, an early return and a
// function boundary; a nested footprint; ptr::write, write_unaligned,
// copy_nonoverlapping, mem::swap and mem::replace outside and inside the
// footprint; model-handled containers (Vec, VecDeque, String) and Cell.
//
// Oracle (per harness):
//   *_must_fail                    -> VERIFICATION:- FAILED (frame)
//   nested_outside_must_fail       -> never SUCCESSFUL
//   ptr_write/replace/swap_inside_safe -> VERIFICATION:- SUCCESSFUL
//   merge_both_covered_safe, nested_inside_safe,
//   copy_nonoverlapping_inside_safe, vec_push_inside_safe
//                                  -> never a Genuine counterexample
#[repr(C)]
struct Pair { a: u32, b: u32 }
struct Inner { x: u32, y: u32 }
struct Outer { inner: Inner, z: u32 }

fn pick<'x>(a: &'x mut u32, b: &'x mut u32, c: bool) -> &'x mut u32 { if c { return b; } a }
fn store_one(p: &mut u32) { *p = 1; }

#[kani::modifies(a)]
fn loop_merge(a: &mut u32, b: &mut u32, n: u8) { let mut p: &mut u32 = a; let mut i = 0u8; while i < n { p = &mut *b; i += 1; } *p = 1; }
#[kani::proof_for_contract(loop_merge)]
#[kani::unwind(4)]
fn loop_merge_must_fail() { let mut a: u32 = kani::any(); let mut b: u32 = kani::any(); let n: u8 = kani::any(); kani::assume(n < 3); loop_merge(&mut a, &mut b, n); }

#[kani::modifies(a)]
fn early_return_pick(a: &mut u32, b: &mut u32, c: bool) { let p = pick(a, b, c); *p = 1; }
#[kani::proof_for_contract(early_return_pick)]
fn early_return_pick_must_fail() { let mut a: u32 = kani::any(); let mut b: u32 = kani::any(); let c: bool = kani::any(); early_return_pick(&mut a, &mut b, c); }

#[kani::modifies(a)]
fn callee_merge(a: &mut u32, b: &mut u32, c: bool) { let p = if c { b } else { a }; store_one(p); }
#[kani::proof_for_contract(callee_merge)]
fn callee_merge_must_fail() { let mut a: u32 = kani::any(); let mut b: u32 = kani::any(); let c: bool = kani::any(); callee_merge(&mut a, &mut b, c); }

#[kani::modifies(a, b)]
fn merge_both_covered(a: &mut u32, b: &mut u32, c: bool) { let p = if c { b } else { a }; *p = 1; }
#[kani::proof_for_contract(merge_both_covered)]
fn merge_both_covered_safe() { let mut a: u32 = kani::any(); let mut b: u32 = kani::any(); let c: bool = kani::any(); merge_both_covered(&mut a, &mut b, c); }

#[kani::modifies(&o.inner.x)]
fn nested_outside(o: &mut Outer) { o.inner.y = 1; }
#[kani::proof_for_contract(nested_outside)]
fn nested_outside_must_fail() { let mut o = Outer { inner: Inner { x: kani::any(), y: kani::any() }, z: kani::any() }; nested_outside(&mut o); }

#[kani::modifies(&o.inner.x)]
fn nested_inside(o: &mut Outer) { o.inner.x = 1; }
#[kani::proof_for_contract(nested_inside)]
fn nested_inside_safe() { let mut o = Outer { inner: Inner { x: kani::any(), y: kani::any() }, z: kani::any() }; nested_inside(&mut o); }

#[kani::modifies(&p.a)]
fn ptr_write_outside(p: &mut Pair, q: &mut u32) { p.a = 1; unsafe { core::ptr::write(q as *mut u32, 5) }; }
#[kani::proof_for_contract(ptr_write_outside)]
fn ptr_write_outside_must_fail() { let mut p = Pair { a: kani::any(), b: kani::any() }; let mut q: u32 = kani::any(); ptr_write_outside(&mut p, &mut q); }

#[kani::modifies(&p.a)]
fn write_unaligned_outside(p: &mut Pair, q: &mut u32) { p.a = 1; unsafe { core::ptr::write_unaligned(q as *mut u32, 5) }; }
#[kani::proof_for_contract(write_unaligned_outside)]
fn write_unaligned_outside_must_fail() { let mut p = Pair { a: kani::any(), b: kani::any() }; let mut q: u32 = kani::any(); write_unaligned_outside(&mut p, &mut q); }

#[kani::modifies(&p.a)]
fn copy_nonoverlapping_outside(p: &mut Pair, q: &mut u32) { p.a = 1; let src: u32 = 5; unsafe { core::ptr::copy_nonoverlapping(&src as *const u32, q as *mut u32, 1) }; }
#[kani::proof_for_contract(copy_nonoverlapping_outside)]
fn copy_nonoverlapping_outside_must_fail() { let mut p = Pair { a: kani::any(), b: kani::any() }; let mut q: u32 = kani::any(); copy_nonoverlapping_outside(&mut p, &mut q); }

#[kani::modifies(&p.a)]
fn swap_outside(p: &mut Pair, q: &mut u32, r: &mut u32) { p.a = 1; core::mem::swap(q, r); }
#[kani::proof_for_contract(swap_outside)]
fn swap_outside_must_fail() { let mut p = Pair { a: kani::any(), b: kani::any() }; let mut q: u32 = kani::any(); let mut r: u32 = kani::any(); swap_outside(&mut p, &mut q, &mut r); }

#[kani::modifies(&p.a)]
fn replace_outside(p: &mut Pair, q: &mut u32) { p.a = 1; let _ = core::mem::replace(q, 5); }
#[kani::proof_for_contract(replace_outside)]
fn replace_outside_must_fail() { let mut p = Pair { a: kani::any(), b: kani::any() }; let mut q: u32 = kani::any(); replace_outside(&mut p, &mut q); }

#[kani::modifies(&p.a)]
fn ptr_write_inside(p: &mut Pair) { unsafe { core::ptr::write(&mut p.a as *mut u32, 5) }; }
#[kani::proof_for_contract(ptr_write_inside)]
fn ptr_write_inside_safe() { let mut p = Pair { a: kani::any(), b: kani::any() }; ptr_write_inside(&mut p); }

#[kani::modifies(&p.a)]
fn copy_nonoverlapping_inside(p: &mut Pair) { let src: u32 = 5; unsafe { core::ptr::copy_nonoverlapping(&src as *const u32, &mut p.a as *mut u32, 1) }; }
#[kani::proof_for_contract(copy_nonoverlapping_inside)]
fn copy_nonoverlapping_inside_safe() { let mut p = Pair { a: kani::any(), b: kani::any() }; copy_nonoverlapping_inside(&mut p); }

#[kani::modifies(&p.a)]
fn replace_inside(p: &mut Pair) { let _ = core::mem::replace(&mut p.a, 5); }
#[kani::proof_for_contract(replace_inside)]
fn replace_inside_safe() { let mut p = Pair { a: kani::any(), b: kani::any() }; replace_inside(&mut p); }

#[kani::modifies(q, r)]
fn swap_inside(q: &mut u32, r: &mut u32) { core::mem::swap(q, r); }
#[kani::proof_for_contract(swap_inside)]
fn swap_inside_safe() { let mut q: u32 = kani::any(); let mut r: u32 = kani::any(); swap_inside(&mut q, &mut r); }

#[kani::modifies(&p.a)]
fn vec_pop_outside(p: &mut Pair, v: &mut Vec<u8>) { p.a = 1; let _ = v.pop(); }
#[kani::proof_for_contract(vec_pop_outside)]
fn vec_pop_outside_must_fail() { let mut p = Pair { a: kani::any(), b: kani::any() }; let mut v: Vec<u8> = vec![1, 2]; vec_pop_outside(&mut p, &mut v); }

#[kani::modifies(v)]
fn vec_push_inside(v: &mut Vec<u8>) { v.push(7); }
#[kani::proof_for_contract(vec_push_inside)]
fn vec_push_inside_safe() { let mut v: Vec<u8> = Vec::new(); vec_push_inside(&mut v); }

#[kani::modifies(&p.a)]
fn vecdeque_push_outside(p: &mut Pair, v: &mut std::collections::VecDeque<u8>) { p.a = 1; v.push_back(7); }
#[kani::proof_for_contract(vecdeque_push_outside)]
fn vecdeque_push_outside_must_fail() { let mut p = Pair { a: kani::any(), b: kani::any() }; let mut v = std::collections::VecDeque::new(); vecdeque_push_outside(&mut p, &mut v); }

#[kani::modifies(&p.a)]
fn string_push_outside(p: &mut Pair, s: &mut String) { p.a = 1; s.push('x'); }
#[kani::proof_for_contract(string_push_outside)]
fn string_push_outside_must_fail() { let mut p = Pair { a: kani::any(), b: kani::any() }; let mut s = String::new(); string_push_outside(&mut p, &mut s); }

#[kani::modifies(&p.a)]
fn cell_set_outside(p: &mut Pair, c: &core::cell::Cell<u32>) { p.a = 1; c.set(9); }
#[kani::proof_for_contract(cell_set_outside)]
fn cell_set_outside_must_fail() { let mut p = Pair { a: kani::any(), b: kani::any() }; let c = core::cell::Cell::new(kani::any::<u32>()); cell_set_outside(&mut p, &c); }
