// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Oracle (per harness, BMC lane; Kani 0.67.0 semantics):
//   safe_static_then_box                   -> VERIFICATION:- SUCCESSFUL
//   bug_static_then_box_claimed_same       -> VERIFICATION:- FAILED (assertion)
//   safe_static_vs_box                     -> VERIFICATION:- SUCCESSFUL
//   safe_ref_and_raw_const_same_static     -> VERIFICATION:- SUCCESSFUL
//   bug_ref_and_raw_const_claimed_distinct -> VERIFICATION:- FAILED (assertion)
//   safe_const_ref_into_static_field       -> VERIFICATION:- SUCCESSFUL
//   bug_const_ref_into_static_claimed_base -> VERIFICATION:- FAILED (assertion)
//   safe_inlined_and_local_borrow          -> VERIFICATION:- SUCCESSFUL
//   bug_inlined_and_local_borrow_claimed_equal -> VERIFICATION:- FAILED (assertion)
//   safe_const_ref_into_const_array        -> VERIFICATION:- SUCCESSFUL
//   bug_const_ref_into_const_array_claimed_first -> VERIFICATION:- FAILED (assertion)
//
// WHY THIS FILE EXISTS. A static (any global allocation) is ONE object with
// ONE address, disjoint from every heap and stack object. The BMC lane named
// it two ways: a raw-pointer constant (`&raw mut A`, `const P = &raw const S`)
// through `global_alloc_addrs`, and a reference constant (`&S`, `&S[i]`)
// through a second, per-body symbol. Measured on the bmc-round2 merge
// (c3f9f481f): the raw-pointer symbol was kept off other NAMED allocations but
// not off a Box's heap region, so the solver placed `A` on a later Box and
// `safe_static_then_box` FAILED (it is SUCCESSFUL on main 0e21bc2b0), and the
// two schemes gave one static two unrelated addresses, so
// `safe_ref_and_raw_const_same_static` FAILED [AY:CTREX_CAT:Genuine] on main
// and on the merge. A reference constant into the MIDDLE of an allocation was
// read and placed as if it pointed at its start: for `E = &[1u32, 2, 3][1]`,
// `*E == 1` PROVED on main 0e21bc2b0 and on the merge (a false proof), and
// `SECOND = &PAIR.1` was placed at `PAIR`'s base.

static mut A: u8 = 7;
static S: u32 = 11;
const P: *const u32 = &raw const S;
static PAIR: (u32, u32) = (1, 2);
const SECOND: &u32 = &PAIR.1;
static T: [u32; 2] = [1, 2];
const E: &u32 = &[1u32, 2, 3][1];

#[kani::proof]
fn safe_static_then_box() {
    unsafe {
        let a = &raw mut A;
        *a = 1;
        let b = Box::new(2u8);
        assert!(*a == 1);
        assert!(*b == 2);
    }
}

#[kani::proof]
fn bug_static_then_box_claimed_same() {
    unsafe {
        let a = &raw mut A;
        let b = Box::new(2u8);
        assert!(a as *const u8 == &*b as *const u8);
    }
}

#[kani::proof]
fn safe_static_vs_box() {
    let b = Box::into_raw(Box::new(2u8));
    unsafe {
        *b = 9;
        let a = &raw mut A;
        assert!(*a == 7);
        drop(Box::from_raw(b));
    }
}

#[kani::proof]
fn safe_ref_and_raw_const_same_static() {
    let r: &u32 = &S;
    let p: *const u32 = P;
    assert!(core::ptr::eq(r as *const u32, p));
}

#[kani::proof]
fn bug_ref_and_raw_const_claimed_distinct() {
    let r: &u32 = &S;
    let p: *const u32 = P;
    assert!(!core::ptr::eq(r as *const u32, p));
}

#[kani::proof]
fn safe_const_ref_into_static_field() {
    assert!(core::ptr::eq(SECOND, &PAIR.1));
    assert!(!core::ptr::eq(SECOND, &PAIR.0));
    assert!(*SECOND == 2);
}

#[kani::proof]
fn bug_const_ref_into_static_claimed_base() {
    assert!(core::ptr::eq(SECOND, &PAIR.0));
}

#[inline(never)]
fn first_addr() -> *const u32 {
    &T[0]
}

#[kani::proof]
fn safe_inlined_and_local_borrow() {
    let a = first_addr();
    let b: *const u32 = &T[1];
    assert!(a != b);
    assert!(a == &T[0] as *const u32);
}

#[kani::proof]
fn bug_inlined_and_local_borrow_claimed_equal() {
    let a = first_addr();
    let b: *const u32 = &T[1];
    assert!(a == b);
}

#[kani::proof]
fn safe_const_ref_into_const_array() {
    assert!(*E == 2);
}

#[kani::proof]
fn bug_const_ref_into_const_array_claimed_first() {
    assert!(*E == 1);
}
