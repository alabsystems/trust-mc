// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Oracle (per harness; Rust semantics, confirmed by running the program
// natively under Trust seal 9192, one process per harness):
//   safe_atomic_through_offset_ref -> VERIFICATION:- SUCCESSFUL
//   bug_atomic_through_offset_ref  -> VERIFICATION:- FAILED (assertion)
//
// WHY THIS FILE EXISTS. A constant reference at an offset into an array of
// atomics: the store goes to the live object at that offset, never to the
// initializer. The rule is stated once, in
// trust-mc-compiler/src/codegen_ay/shared/const_pointer.rs.
//
// Measured on main 5b8582dd4 (round-10 design, 30 s per harness, ay 48c98a43d):
// the CHC lane ICEs on the `AtomicU32` static
// (`chc::dyn_coercion::single_field_storage_ty`), a separate root cause that
// also kills rc_shared_handle_dual.rs; the BMC lane fails closed (EncodingGap).

#![allow(dead_code)]

use std::sync::atomic::{AtomicU32, Ordering};

static ATOMS: [AtomicU32; 2] = [AtomicU32::new(1), AtomicU32::new(2)];
static RA: &AtomicU32 = &ATOMS[1];

#[kani::proof]
fn safe_atomic_through_offset_ref() {
    RA.store(5, Ordering::SeqCst);
    assert!(ATOMS[1].load(Ordering::SeqCst) == 5);
}

#[kani::proof]
fn bug_atomic_through_offset_ref() {
    RA.store(5, Ordering::SeqCst);
    assert!(ATOMS[1].load(Ordering::SeqCst) == 2);
}
