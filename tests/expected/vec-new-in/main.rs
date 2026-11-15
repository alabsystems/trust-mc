// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
//! `Vec::new_in(alloc)` routes to the VecNew stub (the model carries no
//! allocator, exactly as `with_capacity_in` already does). The call survives
//! the inline pass; before the table entry only the BMC mini-inliner (with the
//! RawVec::new_in stub underneath) rescued it.
#![feature(allocator_api)]

use std::alloc::Global;

#[kani::proof]
fn new_in_is_empty_then_push() {
    let mut v: Vec<u8> = Vec::new_in(Global);
    assert!(v.is_empty());
    v.push(7);
    assert_eq!(v.len(), 1);
}

// Deliberately broken: a fresh Vec is empty — must FAIL.
#[kani::proof]
fn new_in_claimed_nonempty_fails() {
    let v: Vec<u8> = Vec::new_in(Global);
    assert_eq!(v.len(), 1);
}
