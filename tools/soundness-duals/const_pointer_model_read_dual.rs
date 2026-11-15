// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Oracle (per harness; Rust semantics, confirmed by running the program
// natively under Trust seal 9192, one process per harness):
//   safe_copy_from_const     -> VERIFICATION:- SUCCESSFUL
//   bug_copy_from_const      -> VERIFICATION:- FAILED (assertion)
//   safe_copy_past_window    -> VERIFICATION:- SUCCESSFUL
//   bug_copy_past_window     -> VERIFICATION:- FAILED (assertion)
//   safe_copy_static_u16     -> VERIFICATION:- SUCCESSFUL
//   bug_copy_static_u16      -> VERIFICATION:- FAILED (assertion)
//   safe_bytes_eq_const      -> VERIFICATION:- SUCCESSFUL
//   bug_bytes_eq_const       -> VERIFICATION:- FAILED (assertion)
//   safe_read_unaligned_u16  -> VERIFICATION:- SUCCESSFUL
//   bug_read_unaligned_u16   -> VERIFICATION:- FAILED (assertion)
//
// WHY THIS FILE EXISTS. A FIXED constant target is known whole, at every
// type and offset the harness reads it through a pointer
// (trust-mc-compiler/src/codegen_ay/shared/const_pointer.rs). These harnesses
// read it through a MODEL rather than a MIR dereference: `copy_nonoverlapping`
// into a local, slice equality over `slice::from_raw_parts`, and
// `ptr::read_unaligned` at an odd offset, inside and past the window the
// constant names.
//
// Measured on main 5b8582dd4 (round-10 resume, 30 s per harness, ay
// 48c98a43d): CHC false certificate on safe_read_unaligned_u16; every other
// row fails closed or matches on both lanes. With the rule: no missed bug and
// no false certificate on either lane; the copy and equality rows fail closed
// (EncodingGap / OverApproximation), and CHC's safe_read_unaligned_u16 runs
// out of budget (FAILED Unknown, measured at 30 s and at 240 s).
#![allow(dead_code)]
const E: &u32 = &[1u32, 2, 3][1];
static S: [u32; 3] = [1, 2, 3];

// E's pointee is [2, 0, 0, 0] as bytes; the copy intrinsic reads them.
#[kani::proof]
fn safe_copy_from_const() {
    let mut dst = [0u8; 4];
    unsafe { std::ptr::copy_nonoverlapping(E as *const u32 as *const u8, dst.as_mut_ptr(), 4) };
    assert!(dst[0] == 2);
    assert!(dst[1] == 0);
}

#[kani::proof]
fn bug_copy_from_const() {
    let mut dst = [0u8; 4];
    unsafe { std::ptr::copy_nonoverlapping(E as *const u32 as *const u8, dst.as_mut_ptr(), 4) };
    assert!(dst[0] == 1);
}

// Past the window: the next element of E's array, by a byte copy.
#[kani::proof]
fn safe_copy_past_window() {
    let mut dst = [0u8; 4];
    unsafe {
        std::ptr::copy_nonoverlapping((E as *const u32 as *const u8).wrapping_add(4), dst.as_mut_ptr(), 4)
    };
    assert!(dst[0] == 3);
}

#[kani::proof]
fn bug_copy_past_window() {
    let mut dst = [0u8; 4];
    unsafe {
        std::ptr::copy_nonoverlapping((E as *const u32 as *const u8).wrapping_add(4), dst.as_mut_ptr(), 4)
    };
    assert!(dst[0] == 2);
}

// A static's bytes through a u16 copy.
#[kani::proof]
fn safe_copy_static_u16() {
    let mut dst = [0u16; 2];
    unsafe { std::ptr::copy_nonoverlapping(&S[1] as *const u32 as *const u16, dst.as_mut_ptr(), 2) };
    assert!(dst[0] == 2);
    assert!(dst[1] == 0);
}

#[kani::proof]
fn bug_copy_static_u16() {
    let mut dst = [0u16; 2];
    unsafe { std::ptr::copy_nonoverlapping(&S[1] as *const u32 as *const u16, dst.as_mut_ptr(), 2) };
    assert!(dst[0] == 1);
}

// Slice equality on bytes of a constant (a memcmp-like model).
#[kani::proof]
fn safe_bytes_eq_const() {
    let b = unsafe { std::slice::from_raw_parts(E as *const u32 as *const u8, 4) };
    assert!(b == [2u8, 0, 0, 0]);
}

#[kani::proof]
fn bug_bytes_eq_const() {
    let b = unsafe { std::slice::from_raw_parts(E as *const u32 as *const u8, 4) };
    assert!(b == [1u8, 0, 0, 0]);
}

// read_unaligned at u16.
#[kani::proof]
fn safe_read_unaligned_u16() {
    let v = unsafe { std::ptr::read_unaligned((E as *const u32 as *const u8).wrapping_add(1) as *const u16) };
    assert!(v == 0);
}

#[kani::proof]
fn bug_read_unaligned_u16() {
    let v = unsafe { std::ptr::read_unaligned((E as *const u32 as *const u8).wrapping_add(1) as *const u16) };
    assert!(v == 2);
}
