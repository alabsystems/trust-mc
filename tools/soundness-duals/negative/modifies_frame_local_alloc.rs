// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// NEGATIVE PACK: DFCC freshness for storage the CHECKED FUNCTION allocated.
//
// A `modifies` clause restricts writes to memory that existed before the call.
// Storage the function itself creates is assignable whatever the clause says.
// The CHC frame check exempted only STACK locals, so a `Box` allocated inside
// the function and written through was accused: `#[kani::modifies(a)] fn f(a:
// &mut u32) { let mut bx = Box::new(0); *bx = 1; *a = *bx; }` was FAILED
// [AY:CTREX_CAT:Genuine] on a `memory_safety` check — the gating row of the
// branch's own dual gate (negative/modifies_frame_shapes.rs
// ::box_local_store_safe), red on origin/main as well.
//
// Oracle (per harness):
//   *_safe        -> never a Genuine counterexample (these programs have no bug)
//   *_must_fail   -> VERIFICATION:- FAILED; never SUCCESSFUL

#[kani::modifies(a)]
fn box_local_store(a: &mut u32) {
    let mut bx: Box<u32> = Box::new(0);
    *bx = 1;
    *a = *bx;
}

#[kani::proof_for_contract(box_local_store)]
fn box_local_store_inside_frame_safe() {
    let mut a: u32 = kani::any();
    box_local_store(&mut a);
}

#[kani::modifies(a)]
fn box_local_no_store(a: &mut u32) {
    let bx: Box<u32> = Box::new(1);
    *a = *bx;
}

#[kani::proof_for_contract(box_local_no_store)]
fn box_local_no_store_inside_frame_safe() {
    let mut a: u32 = kani::any();
    box_local_no_store(&mut a);
}

#[kani::modifies(a)]
fn vec_local_push(a: &mut u32) {
    let mut v: Vec<u32> = Vec::new();
    v.push(7);
    *a = v[0];
}

#[kani::proof_for_contract(vec_local_push)]
fn vec_local_push_inside_frame_safe() {
    let mut a: u32 = kani::any();
    vec_local_push(&mut a);
}

#[kani::modifies(a)]
fn stack_local_store(a: &mut u32) {
    let mut v: u32 = 0;
    let r = &mut v;
    *r = 1;
    *a = v;
}

#[kani::proof_for_contract(stack_local_store)]
fn stack_local_store_inside_frame_safe() {
    let mut a: u32 = kani::any();
    stack_local_store(&mut a);
}

// --- the other edge: a real frame violation must still be caught -----------

static mut G: u32 = 0;

#[kani::modifies(a)]
fn writes_outside_frame(a: &mut u32, b: &mut u32) {
    *b = 1;
    *a = 1;
}

#[kani::proof_for_contract(writes_outside_frame)]
fn writes_outside_frame_must_fail() {
    let mut a: u32 = kani::any();
    let mut b: u32 = kani::any();
    writes_outside_frame(&mut a, &mut b);
}

#[kani::modifies(a)]
fn box_arg_store_outside_frame(a: &mut u32, b: &mut Box<u32>) {
    **b = 1;
    *a = 1;
}

#[kani::proof_for_contract(box_arg_store_outside_frame)]
fn box_arg_store_outside_frame_must_fail() {
    let mut a: u32 = kani::any();
    let mut b: Box<u32> = Box::new(kani::any());
    box_arg_store_outside_frame(&mut a, &mut b);
}

#[kani::modifies(a)]
fn static_store_outside_frame(a: &mut u32) {
    unsafe {
        G = 1;
    }
    *a = 1;
}

#[kani::proof_for_contract(static_store_outside_frame)]
fn static_store_outside_frame_must_fail() {
    let mut a: u32 = kani::any();
    static_store_outside_frame(&mut a);
}
