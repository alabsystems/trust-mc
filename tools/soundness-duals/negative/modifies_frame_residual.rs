// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z function-contracts
//
// NEGATIVE PACK: stores outside a NON-EMPTY `#[kani::modifies]` footprint that
// still verify after m3/soundness-fixes-1 (contract-frames, f43c601c8).
//
// Found by the adversarial review of that branch, 2026-09-12. Every must-fail
// harness here is a clean false proof somewhere; none is a regression against
// 07b812dd1, where the same harnesses verified too.
//
// - merge_*: the BMC classifier CERTIFIES a store by the pointee NAME in
//   `ref_pointees`, a flow-insensitive side table. `if c { b } else { a }`
//   leaves the last-codegen'd arm's pointee there, so `*p = 1` is certified
//   against `modifies(a)` although the `c` path writes `*b`
//   (BMC: "Check that *...::local_2 is assignable: SUCCESS", SUCCESSFUL).
// - vec_push_*: a store made inside a model/stub call handler (Vec::push) is
//   never classified; only deref stores, call destinations and
//   SetDiscriminant are (BMC and CHC: SUCCESSFUL). Fixed 2026-09-15 on
//   fix/walker-modifies-frame: CHC by the nested-walker frame net, BMC by the
//   container-stub `&mut` argument hook (fail-closed). vec_push_local_safe is
//   the frame-local twin: a push onto a Vec created inside the checked
//   function is assignable.
// - write_bytes_* / copy_*: byte stores through the copy family (BMC now
//   demotes through copy_shadow; CHC: SUCCESSFUL).
//
// Oracle (per harness):
//   merge_last_in_footprint_must_fail   -> VERIFICATION:- FAILED (frame)
//   merge_first_in_footprint_must_fail  -> VERIFICATION:- FAILED (frame)
//   vec_push_outside_must_fail          -> VERIFICATION:- FAILED (frame)
//   write_bytes_outside_must_fail       -> VERIFICATION:- FAILED (frame)
//   copy_outside_must_fail              -> VERIFICATION:- FAILED (frame)
//   merge_both_in_footprint_safe        -> VERIFICATION:- SUCCESSFUL
//   inside_only_safe                    -> VERIFICATION:- SUCCESSFUL
//   vec_push_local_safe                 -> VERIFICATION:- SUCCESSFUL

#[repr(C)]
struct Pair {
    a: u32,
    b: u32,
}

#[kani::modifies(a)]
fn merge_last_in(a: &mut u32, b: &mut u32, c: bool) {
    let p: &mut u32 = if c { b } else { a };
    *p = 1;
}

#[kani::proof_for_contract(merge_last_in)]
fn merge_last_in_footprint_must_fail() {
    let mut a: u32 = kani::any();
    let mut b: u32 = kani::any();
    let c: bool = kani::any();
    merge_last_in(&mut a, &mut b, c);
}

#[kani::modifies(a)]
fn merge_first_in(a: &mut u32, b: &mut u32, c: bool) {
    let p: &mut u32 = if c { a } else { b };
    *p = 1;
}

#[kani::proof_for_contract(merge_first_in)]
fn merge_first_in_footprint_must_fail() {
    let mut a: u32 = kani::any();
    let mut b: u32 = kani::any();
    let c: bool = kani::any();
    merge_first_in(&mut a, &mut b, c);
}

#[kani::modifies(&p.a)]
fn vec_push_outside(p: &mut Pair, v: &mut Vec<u8>) {
    p.a = 1;
    v.push(7);
}

#[kani::proof_for_contract(vec_push_outside)]
fn vec_push_outside_must_fail() {
    let mut p = Pair { a: kani::any(), b: kani::any() };
    let mut v: Vec<u8> = Vec::new();
    vec_push_outside(&mut p, &mut v);
}

#[kani::modifies(&p.a)]
fn write_bytes_outside(p: &mut Pair, q: &mut u32) {
    p.a = 1;
    unsafe { core::ptr::write_bytes(q as *mut u32, 0xAB, 1) };
}

#[kani::proof_for_contract(write_bytes_outside)]
fn write_bytes_outside_must_fail() {
    let mut p = Pair { a: kani::any(), b: kani::any() };
    let mut q: u32 = kani::any();
    write_bytes_outside(&mut p, &mut q);
}

#[kani::modifies(&p.a)]
fn copy_outside(p: &mut Pair, q: &mut u32) {
    p.a = 1;
    let src: u32 = 5;
    unsafe { core::ptr::copy(&src as *const u32, q as *mut u32, 1) };
}

#[kani::proof_for_contract(copy_outside)]
fn copy_outside_must_fail() {
    let mut p = Pair { a: kani::any(), b: kani::any() };
    let mut q: u32 = kani::any();
    copy_outside(&mut p, &mut q);
}

#[kani::modifies(a)]
fn both_in(a: &mut u32, c: bool) {
    if c {
        *a = 1;
    } else {
        *a = 2;
    }
}

#[kani::proof_for_contract(both_in)]
fn merge_both_in_footprint_safe() {
    let mut a: u32 = kani::any();
    let c: bool = kani::any();
    both_in(&mut a, c);
}

#[kani::modifies(&p.a)]
fn inside_only(p: &mut Pair) {
    p.a = 2;
}

#[kani::proof_for_contract(inside_only)]
fn inside_only_safe() {
    let mut p = Pair { a: kani::any(), b: kani::any() };
    inside_only(&mut p);
}

#[kani::modifies(&p.a)]
fn vec_push_local(p: &mut Pair) -> usize {
    p.a = 1;
    let mut w: Vec<u8> = Vec::new();
    w.push(7);
    w.len()
}

#[kani::proof_for_contract(vec_push_local)]
fn vec_push_local_safe() {
    let mut p = Pair { a: kani::any(), b: kani::any() };
    vec_push_local(&mut p);
}
