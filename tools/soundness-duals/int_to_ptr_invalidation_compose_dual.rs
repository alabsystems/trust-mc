// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL -- an integer-to-pointer cast and an allocation in the same basic
//! block, and a constant lane naming an object the harness allocates after the cast
//! (review of fix/chc-lost-writes, lostwrite track round 2, finding 5). The cast
//! invalidates `obj_valid` of the object its result names; the allocating call that
//! ends the block wrote `obj_valid__out = store(obj_valid, id, true)` from the
//! block's INPUT, and the rule kept the call's definition and dropped the
//! statement's (`filter_superseded_store_chains`). The read through the cast
//! pointer then saw a valid object and verified SUCCESSFUL, on main and the branch
//! alike, where Kani reports an invalid integer address. The call's definition is
//! now composed onto the block's. A constant lane naming an object that is a stack
//! slot, a provably-valid backing or allocated after the cast fails closed at the
//! access (`int_to_ptr_names_always_valid_object`).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3):
//!   bug_cast_vec_same_block_read            -> FAILED ('dereference failure: invalid integer address')
//!   bug_cast_box_same_block_read            -> FAILED ('dereference failure: invalid integer address')
//!   bug_cast_vec_same_block_read_lane2      -> FAILED ('dereference failure: invalid integer address')
//!   bug_const_lane1_then_vec_read           -> FAILED ('dereference failure: invalid integer address')
//!   safe_cast_then_vec_use_vec              -> SUCCESSFUL
//!   safe_cast_then_box_read_box             -> SUCCESSFUL
//!   safe_const_lane1_then_vec_compare_only  -> SUCCESSFUL
//!
#![allow(unused)]

#[kani::proof]
fn bug_cast_vec_same_block_read() {
    let a: usize = kani::any();
    let p = a as *const u8;
    let v: Vec<u8> = vec![1, 2, 3];
    kani::assume(a == 1usize << 32);
    let x = unsafe { *p };
    assert!(x == x || v[0] == 0);
}

#[kani::proof]
fn bug_cast_box_same_block_read() {
    let a: usize = kani::any();
    let p = a as *const u8;
    let b = Box::new(5u32);
    kani::assume(a == 1usize << 32);
    let x = unsafe { *p };
    assert!(x == x || *b == 0);
}

#[kani::proof]
fn bug_cast_vec_same_block_read_lane2() {
    let a: usize = kani::any();
    let p = a as *const u8;
    let v: Vec<u8> = vec![1, 2, 3];
    kani::assume(a == 2usize << 32);
    let x = unsafe { *p };
    assert!(x == x || v[0] == 0);
}

#[kani::proof]
fn bug_const_lane1_then_vec_read() {
    let p = (1usize << 32) as *const u8;
    let v: Vec<u8> = vec![1, 2, 3];
    let x = unsafe { *p };
    assert!(x == x || v[0] == 0);
}

#[kani::proof]
fn safe_cast_then_vec_use_vec() {
    let a: usize = kani::any();
    let p = a as *const u8;
    let v: Vec<u8> = vec![1, 2, 3];
    assert!(v.len() == 3 && v[2] == 3);
}

#[kani::proof]
fn safe_cast_then_box_read_box() {
    let a: usize = kani::any();
    let p = a as *const u8;
    let b = Box::new(5u32);
    assert!(*b == 5);
}

#[kani::proof]
fn safe_const_lane1_then_vec_compare_only() {
    let p = (1usize << 32) as *const u8;
    let v: Vec<u8> = vec![1, 2, 3];
    assert!(!p.is_null() && v[0] == 1);
}
