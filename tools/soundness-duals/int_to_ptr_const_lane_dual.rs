// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL -- a pointer made from a COMPUTED integer constant whose high
//! word is a model object's number (`(5usize << 32) as *const u32`, a transmute of
//! `k << 32`, a `const fn` result), in a body that exposes a stack address and in
//! one that does not (review of fix/chc-lost-writes, lostwrite track round 1,
//! findings 1 and 9). The model numbers its objects by the high word, so such a
//! constant names a stack slot, and a stack slot's accesses never read `obj_valid`:
//! the integer-to-pointer invalidation did not reach it, and the read or write
//! verified SUCCESSFUL clean where Kani reports an invalid integer address. On main
//! the hole was open in a body that exposes no address; folding every constant in
//! `int_to_ptr_value_of_operand` opened it in exposing bodies too. Such a lane now
//! fails closed (`int_to_ptr_names_always_valid_object`) and the slot's accesses
//! read `obj_valid`, where the invalidation landed.
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3):
//!   bug_exposed_hi5_read              -> FAILED ('dereference failure: invalid integer address')
//!   bug_exposed_hi4_write_then_check  -> FAILED ('dereference failure: invalid integer address')
//!   bug_exposed_transmute_hi6_read    -> FAILED ('dereference failure: invalid integer address')
//!   bug_exposed_const_fn_hi7_read     -> FAILED ('dereference failure: invalid integer address')
//!   bug_exposed_hi5_read_u8           -> FAILED ('dereference failure: invalid integer address')
//!   bug_plain_hi5_read                -> FAILED ('dereference failure: invalid integer address')
//!   bug_plain_hi5_read_with_ref_taken -> FAILED ('dereference failure: invalid integer address')
//!   bug_plain_hi9_write               -> FAILED ('dereference failure: invalid integer address')
//!   bug_plain_without_provenance_hi5  -> FAILED ('dereference failure: invalid integer address')
//!   safe_plain_hi5_compare_only       -> SUCCESSFUL
//!   safe_exposed_null_lane_compare    -> SUCCESSFUL
//!   safe_plain_low_address_compare    -> SUCCESSFUL
//!   bug_exposed_nonnull_transmute_hi6_read -> FAILED ('dereference failure: invalid integer address')
//!   safe_nonnull_from_exposed_address -> SUCCESSFUL
//!   bug_exposed_array1_transmute_hi6_read -> FAILED ('dereference failure: invalid integer address')
//!   bug_exposed_union_int_hi6_read    -> FAILED ('dereference failure: invalid integer address')
//!   safe_array1_transmute_exposed_address -> SUCCESSFUL
//!   bug_box_cell_hi1_read             -> FAILED ('dereference failure: invalid integer address')
//!
//! The last two rows were added when main dbfe268fc (Kani's address layout,
//! `region << 48 | offset`) was merged into fix/chc-lost-writes: an integer is an
//! address there, not an identity term, and a transmute into a `NonNull` passed
//! the integer through as the identity. Measured with the corpus-rev Kani
//! 4c0fce8c3 on 2026-10-15. The array, union and `Box` cell rows are a hole of
//! the same class, identical on main f61920d1a: those routes made the pointer
//! without the invalidation (or, for the `Box` cell, stored the integer as the
//! identity), so a number naming no object read clean once carried into another
//! block. A symbolic lane at or past OBJECT_ID_LIMIT now fails the access, as a
//! constant one does, and `Box::new` stores the cast's value.
//!
#![allow(unused)]

#[kani::proof]
fn bug_exposed_hi5_read() {
    let x: u32 = 5;
    let a = &x as *const u32 as usize;
    let hi: usize = 5;
    let p = (hi << 32) as *const u32;
    let v = unsafe { *p };
    assert!(v == v || a == 0);
}

#[kani::proof]
fn bug_exposed_hi4_write_then_check() {
    let mut x: u32 = 5;
    let a = &mut x as *mut u32 as usize;
    let hi: usize = 4;
    let p = (hi << 32) as *mut u32;
    unsafe { *p = 9 };
    assert!(a != 0);
}

#[kani::proof]
fn bug_exposed_transmute_hi6_read() {
    let x: u32 = 5;
    let a = &x as *const u32 as usize;
    let k: usize = 6;
    let p: *const u32 = unsafe { std::mem::transmute::<usize, *const u32>(k << 32) };
    let v = unsafe { *p };
    assert!(v == v || a == 0);
}

#[kani::proof]
fn bug_exposed_const_fn_hi7_read() {
    const fn addr() -> usize {
        7 << 32
    }
    let x: u32 = 5;
    let a = &x as *const u32 as usize;
    let p = addr() as *const u64;
    let v = unsafe { *p };
    assert!(v == v || a == 0);
}

#[kani::proof]
fn bug_exposed_hi5_read_u8() {
    let x: u32 = 5;
    let a = &x as *const u32 as usize;
    let hi: usize = 5;
    let p = (hi << 32) as *const u8;
    let v = unsafe { *p };
    assert!(v == v || a == 0);
}

#[kani::proof]
fn bug_plain_hi5_read() {
    let x: u32 = 5;
    let hi: usize = 5;
    let addr = hi << 32;
    let p = addr as *const u32;
    let v = unsafe { *p };
    assert!(v == v || x == 0);
}

#[kani::proof]
fn bug_plain_hi5_read_with_ref_taken() {
    let x: u32 = 5;
    let r = &x;
    let hi: usize = 5;
    let p = (hi << 32) as *const u32;
    let v = unsafe { *p };
    assert!(v == v || *r == 0);
}

#[kani::proof]
fn bug_plain_hi9_write() {
    let k: usize = 9;
    let p = (k << 32) as *mut u32;
    unsafe { *p = 1 };
}

#[kani::proof]
fn bug_plain_without_provenance_hi5() {
    let x: u32 = 5;
    let hi: usize = 5;
    let p: *const u32 = std::ptr::without_provenance(hi << 32);
    let v = unsafe { *p };
    assert!(v == v || x == 0);
}

// A computed constant naming a model object that is only compared: the rule
// fails an access closed, not the cast (round 2, finding 3; round 1 failed this
// closed, Kani proves it).
#[kani::proof]
fn safe_plain_hi5_compare_only() {
    let hi: usize = 5;
    let p = (hi << 32) as *const u32;
    assert!(!p.is_null());
}

// A computed constant in the null object (high word 0) names no object and is
// decided first, whatever stack range it may fall in.
#[kani::proof]
fn safe_exposed_null_lane_compare() {
    let x: u32 = 5;
    let a = &x as *const u32 as usize;
    let lo: usize = 0x10;
    let p = (lo << 4) as *const u32;
    assert!(!p.is_null() && a != 0);
}

#[kani::proof]
fn safe_plain_low_address_compare() {
    let lo: usize = 0x1000;
    let p = (lo + 8) as *const u64;
    assert!(p as usize == 0x1008);
}

// An integer naming no object transmuted into a `NonNull` (merge with main
// dbfe268fc): main took the integer as the identity term and read clean.
#[kani::proof]
fn bug_exposed_nonnull_transmute_hi6_read() {
    let x: u32 = 5;
    let a = &x as *const u32 as usize;
    let k: usize = 6;
    let p = unsafe { std::mem::transmute::<usize, std::ptr::NonNull<u32>>(k << 32) };
    let v = unsafe { *p.as_ptr() };
    assert!(v == v || a == 0);
}

// The exposed address of `x` transmuted into a `NonNull` names `x` again.
#[kani::proof]
fn safe_nonnull_from_exposed_address() {
    let x: u32 = 5;
    let a = &x as *const u32 as usize;
    let p = unsafe { std::mem::transmute::<usize, std::ptr::NonNull<u32>>(a) };
    assert!(unsafe { *p.as_ptr() } == 5);
}

// An integer naming no object made into a pointer by an aggregate transmute
// and by a union (the routes other than a scalar transmute; missed on main
// f61920d1a).
#[kani::proof]
fn bug_exposed_array1_transmute_hi6_read() {
    let x: u32 = 5;
    let a = &x as *const u32 as usize;
    let k: usize = 6;
    let p: *const u32 = unsafe { std::mem::transmute::<[usize; 1], *const u32>([k << 32]) };
    let v = unsafe { *p };
    assert!(v == v || a == 0);
}

#[kani::proof]
fn bug_exposed_union_int_hi6_read() {
    union U {
        i: usize,
        p: *const u32,
    }
    let x: u32 = 5;
    let a = &x as *const u32 as usize;
    let k: usize = 6;
    let u = U { i: k << 32 };
    let p = unsafe { u.p };
    let v = unsafe { *p };
    assert!(v == v || a == 0);
}

#[kani::proof]
fn safe_array1_transmute_exposed_address() {
    let x: u32 = 5;
    let a = &x as *const u32 as usize;
    let p: *const u32 = unsafe { std::mem::transmute::<[usize; 1], *const u32>([a]) };
    assert!(unsafe { *p } == 5);
}

// A pointer made from a number naming no object, stored in a `Box` cell and
// read back after another allocation (the round 3 review's
// `t5_int_ptr_carried.rs::bug_via_box_then_alloc_k1`).
#[kani::proof]
fn bug_box_cell_hi1_read() {
    let cell: Box<*const u32> = Box::new((1usize << 32) as *const u32);
    let b = Box::new(5u32);
    let p = *cell;
    let v = unsafe { *p };
    assert!(v == v || *b == 0);
}
