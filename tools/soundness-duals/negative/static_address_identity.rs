// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// NEGATIVE PACK: the address of a place inside a CONSTANT ALLOCATION.
//
// `derived_place_address` places `&s.f` and `&a[i]` inside a LOCAL's own
// object and `&*b` inside a Box's allocation, but bailed on every other
// dereference — which is how a `static` is reached (a const reference the
// encoder resolves through `ref_pointees`). `&S1[0]` and `&S1[1]` were then
// the SAME symbol (the index never reached the name), and `&S1[0]` and
// `&S2[0]` two unrelated ones, so in BMC
// `assert!(!ptr::eq(&S1[0], &S2[0]) && !ptr::eq(&S1[0], &S1[1]))` and
// `assert!(!ptr::eq(&a[0], &S1[0]))` were FAILED [AY:CTREX_CAT:Genuine] on
// programs whose assertions are true in real Rust. Found by the third
// adversarial review (2026-09-14); red on origin/main too. CHC answered both
// correctly, which isolates the fault to the BMC address lane.
//
// Oracle (per harness):
//   *_must_fail   -> VERIFICATION:- FAILED; never SUCCESSFUL
//   *_safe        -> never a Genuine counterexample

static S1: [u8; 2] = [1, 2];
static S2: [u8; 2] = [3, 4];
static W: [u32; 2] = [1, 2];

#[kani::proof]
fn static_elem_addrs_differ_safe() {
    assert!(!std::ptr::eq(&S1[0], &S2[0]) && !std::ptr::eq(&S1[0], &S1[1]));
}

#[kani::proof]
fn static_elem_addrs_eq_must_fail() {
    assert!(std::ptr::eq(&S1[1], &S2[0]));
}

#[kani::proof]
fn same_static_elem_addr_eq_safe() {
    // Two borrows of ONE static element are the SAME address: the object must
    // be keyed on the allocation, not on the borrow.
    assert!(std::ptr::eq(&S1[0], &S1[0]));
}

#[kani::proof]
fn same_static_elem_addr_differ_must_fail() {
    assert!(!std::ptr::eq(&S1[0], &S1[0]));
}

#[kani::proof]
fn stack_vs_static_addrs_differ_safe() {
    let a = [1u8, 2];
    assert!(!std::ptr::eq(&a[0], &S1[0]));
}

#[kani::proof]
fn stack_vs_static_addrs_eq_must_fail() {
    let a = [1u8, 2];
    assert!(std::ptr::eq(&a[0], &S1[0]));
}

#[kani::proof]
fn static_elem_addr_offset_ordering_safe() {
    let p0 = &W[0] as *const u32 as usize;
    let p1 = &W[1] as *const u32 as usize;
    assert!(p1 == p0 + 4);
}

#[kani::proof]
fn static_elem_addr_offset_ordering_must_fail() {
    let p0 = &W[0] as *const u32 as usize;
    let p1 = &W[1] as *const u32 as usize;
    assert!(p1 == p0 + 1);
}

#[kani::proof]
fn static_value_still_read_safe() {
    // Over-correction guard: giving the allocation an address must not disturb
    // the folded initializer the value lane reads.
    assert!(S1[0] == 1 && S1[1] == 2 && S2[0] == 3);
}
