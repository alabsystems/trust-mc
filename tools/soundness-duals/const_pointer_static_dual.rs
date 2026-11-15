// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Oracle (per harness; Rust semantics, confirmed by running the program
// natively under Trust seal 9192, one process per harness):
//   safe_mut_static_write_through_offset_ptr -> VERIFICATION:- SUCCESSFUL
//   bug_mut_static_write_through_offset_ptr  -> VERIFICATION:- FAILED (assertion)
//   safe_mut_static_read_through_offset_ptr  -> VERIFICATION:- SUCCESSFUL
//   bug_mut_static_read_through_offset_ptr   -> VERIFICATION:- FAILED (assertion)
//   safe_same_alloc_arith                    -> VERIFICATION:- SUCCESSFUL
//   bug_same_alloc_arith                     -> VERIFICATION:- FAILED (assertion)
//   safe_static_substr                       -> VERIFICATION:- SUCCESSFUL
//   bug_static_substr                        -> VERIFICATION:- FAILED (assertion)
//   safe_ref_array_elem                      -> VERIFICATION:- SUCCESSFUL
//   bug_ref_array_elem                       -> VERIFICATION:- FAILED (assertion)
//   safe_deep_field                          -> VERIFICATION:- SUCCESSFUL
//   bug_deep_field                           -> VERIFICATION:- FAILED (assertion)
//   safe_ptr_static_offset0_write            -> VERIFICATION:- SUCCESSFUL
//   bug_ptr_static_offset0_write             -> VERIFICATION:- FAILED (assertion)
//   safe_runtime_ptr_into_mut_static         -> VERIFICATION:- SUCCESSFUL
//   bug_runtime_ptr_into_mut_static          -> VERIFICATION:- FAILED (assertion)
//   safe_str_windows_share_allocation        -> VERIFICATION:- SUCCESSFUL
//   bug_str_windows_claimed_same_start       -> VERIFICATION:- FAILED (assertion)
//   safe_repointed_static_ptr                -> VERIFICATION:- SUCCESSFUL
//   bug_repointed_static_ptr                 -> VERIFICATION:- FAILED (assertion)
//   safe_static_reordered_field              -> VERIFICATION:- SUCCESSFUL
//   bug_static_reordered_field               -> VERIFICATION:- FAILED (assertion)
//   safe_static_distinct_fields              -> VERIFICATION:- SUCCESSFUL
//   bug_static_distinct_fields               -> VERIFICATION:- FAILED (assertion)
//   safe_static_base_vs_first_field          -> VERIFICATION:- SUCCESSFUL
//   bug_static_base_vs_first_field           -> VERIFICATION:- FAILED (assertion)
//   safe_const_vs_runtime_projection         -> VERIFICATION:- SUCCESSFUL
//   bug_const_vs_runtime_projection          -> VERIFICATION:- FAILED (assertion)
//   safe_static_ref_ref                      -> VERIFICATION:- SUCCESSFUL
//   bug_static_ref_ref                       -> VERIFICATION:- FAILED (assertion)
//   safe_static_slice_window                 -> VERIFICATION:- SUCCESSFUL
//   bug_static_slice_window_len              -> VERIFICATION:- FAILED (assertion)
//   bug_static_slice_window_elem             -> VERIFICATION:- FAILED (assertion)
//   safe_equal_statics_distinct              -> VERIFICATION:- SUCCESSFUL
//   bug_equal_statics_same                   -> VERIFICATION:- FAILED (assertion)
//
// WHY THIS FILE EXISTS. A static is ONE object with ONE address. A constant
// pointer into it at an offset addresses that field, not the static's root; a
// pointer-typed static's value (and a `&[T]` static's length) comes from the
// static's own bytes; and what a store through a pointer into a static writes
// is what the static holds afterwards. The rule is stated once, in
// trust-mc-compiler/src/codegen_ay/shared/const_pointer.rs.
//
// Measured on main 5b8582dd4 (round-10 design and challenge, 30 s per harness,
// ay 48c98a43d): on the CHC lane `ptr::eq(F0, F1)`, `!ptr::eq(&PAIR.y, F1)`,
// `SLS.len() == 3`, `SLS[0] == 1`, `*PX = 7; X == 1` (one static minted twice)
// and `*PP = 7; MP[1] == 2` PROVED, and `safe_static_ref_ref`,
// `safe_static_slice_window` and `safe_deep_field` FAILED certified Genuine.

#![allow(dead_code)]
#![allow(static_mut_refs)]

static mut MP: [u32; 2] = [1, 2];
static mut PP: *mut u32 = unsafe { &raw mut MP[1] };
const A3: &[u32; 3] = &[10, 20, 30];
const E0: &u32 = &A3[0];
const E1: &u32 = &A3[1];
static SS2: &str = "hello".split_at(2).1;
const RR: &&u32 = &[&1u32, &2u32][1];
struct Two {
    a: u8,
    b: (u16, u32),
}
static TWO: [Two; 2] = [Two { a: 1, b: (2, 3) }, Two { a: 4, b: (5, 6) }];
const DEEP: &u32 = &TWO[1].b.1;

static mut X: u32 = 1;
static mut PX: *mut u32 = unsafe { &raw mut X };
static mut MQ: [u32; 2] = [1, 2];

const H: &str = "hello";
const T1: &str = H.split_at(2).1;
const T2: &str = H.split_at(1).1;

static mut X2: u32 = 1;
static mut Y2: u32 = 2;
static mut PX2: *mut u32 = unsafe { &raw mut X2 };

struct S3 {
    a: u8,
    b: u32,
    c: u16,
}
static SS3: S3 = S3 { a: 1, b: 2, c: 3 };
const FC: &u16 = &SS3.c;
#[repr(C)]
struct PairC {
    x: u32,
    y: u32,
}
static PAIR: PairC = PairC { x: 1, y: 2 };
const F0: &u32 = &PAIR.x;
const F1: &u32 = &PAIR.y;
static ARR: [u32; 3] = [1, 2, 3];
static R2: &&u32 = &&ARR[2];
static SLS: &[u32] = ARR.split_at(1).1;
static A1: u32 = 1;
static B1: u32 = 1;
const RA: &u32 = &A1;
const RB: &u32 = &B1;

#[kani::proof]
fn safe_mut_static_write_through_offset_ptr() {
    unsafe {
        *PP = 7;
        assert!(MP[1] == 7);
    }
}

#[kani::proof]
fn bug_mut_static_write_through_offset_ptr() {
    unsafe {
        *PP = 7;
        assert!(MP[1] == 2);
    }
}

#[kani::proof]
fn safe_mut_static_read_through_offset_ptr() {
    unsafe {
        MP[1] = 9;
        assert!(*PP == 9);
    }
}

#[kani::proof]
fn bug_mut_static_read_through_offset_ptr() {
    unsafe {
        MP[1] = 9;
        assert!(*PP == 2);
    }
}

#[kani::proof]
fn safe_same_alloc_arith() {
    let p = unsafe { (E0 as *const u32).add(1) };
    assert!(std::ptr::eq(p, E1));
    assert!(unsafe { *p } == 20);
}

#[kani::proof]
fn bug_same_alloc_arith() {
    let p = unsafe { (E0 as *const u32).add(1) };
    assert!(!std::ptr::eq(p, E1));
}

#[kani::proof]
fn safe_static_substr() {
    assert!(SS2.len() == 3);
    assert!(SS2.as_bytes()[0] == b'l');
}

#[kani::proof]
fn bug_static_substr() {
    assert!(SS2.as_bytes()[0] == b'h');
}

#[kani::proof]
fn safe_ref_array_elem() {
    assert!(**RR == 2);
}

#[kani::proof]
fn bug_ref_array_elem() {
    assert!(**RR == 1);
}

#[kani::proof]
fn safe_deep_field() {
    assert!(*DEEP == 6);
}

#[kani::proof]
fn bug_deep_field() {
    assert!(*DEEP == 3);
}

#[kani::proof]
fn safe_ptr_static_offset0_write() {
    unsafe {
        *PX = 7;
        assert!(X == 7);
    }
}

#[kani::proof]
fn bug_ptr_static_offset0_write() {
    unsafe {
        *PX = 7;
        assert!(X == 1);
    }
}

#[kani::proof]
fn safe_runtime_ptr_into_mut_static() {
    unsafe {
        let p: *mut u32 = &raw mut MQ[1];
        *p = 7;
        assert!(MQ[1] == 7);
    }
}

#[kani::proof]
fn bug_runtime_ptr_into_mut_static() {
    unsafe {
        let p: *mut u32 = &raw mut MQ[1];
        *p = 7;
        assert!(MQ[1] == 2);
    }
}

#[kani::proof]
fn safe_str_windows_share_allocation() {
    assert!(std::ptr::eq(T1.as_ptr(), T2.as_ptr().wrapping_add(1)));
}

#[kani::proof]
fn bug_str_windows_claimed_same_start() {
    assert!(std::ptr::eq(T1.as_ptr(), T2.as_ptr()));
}

#[kani::proof]
fn safe_repointed_static_ptr() {
    unsafe {
        PX2 = &raw mut Y2;
        *PX2 = 7;
        assert!(Y2 == 7);
        assert!(X2 == 1);
    }
}

#[kani::proof]
fn bug_repointed_static_ptr() {
    unsafe {
        PX2 = &raw mut Y2;
        *PX2 = 7;
        assert!(Y2 == 2);
    }
}

#[kani::proof]
fn safe_static_reordered_field() {
    assert!(*FC == 3);
}

#[kani::proof]
fn bug_static_reordered_field() {
    assert!(*FC == 2);
}

#[kani::proof]
fn safe_static_distinct_fields() {
    assert!(!std::ptr::eq(F0, F1));
    assert!(std::ptr::eq((F0 as *const u32).wrapping_add(1), F1));
    assert!(*F0 == 1 && *F1 == 2);
}

#[kani::proof]
fn bug_static_distinct_fields() {
    assert!(std::ptr::eq(F0, F1));
}

#[kani::proof]
fn safe_static_base_vs_first_field() {
    assert!(std::ptr::eq(&PAIR as *const PairC as *const u32, F0));
}

#[kani::proof]
fn bug_static_base_vs_first_field() {
    assert!(!std::ptr::eq(&PAIR as *const PairC as *const u32, F0));
}

#[kani::proof]
fn safe_const_vs_runtime_projection() {
    assert!(std::ptr::eq(&PAIR.y, F1));
}

#[kani::proof]
fn bug_const_vs_runtime_projection() {
    assert!(!std::ptr::eq(&PAIR.y, F1));
}

#[kani::proof]
fn safe_static_ref_ref() {
    assert!(**R2 == 3);
}

#[kani::proof]
fn bug_static_ref_ref() {
    assert!(**R2 == 1);
}

#[kani::proof]
fn safe_static_slice_window() {
    assert!(SLS.len() == 2);
    assert!(SLS[0] == 2);
}

#[kani::proof]
fn bug_static_slice_window_len() {
    assert!(SLS.len() == 3);
}

#[kani::proof]
fn bug_static_slice_window_elem() {
    assert!(SLS[0] == 1);
}

#[kani::proof]
fn safe_equal_statics_distinct() {
    assert!(!std::ptr::eq(RA, RB));
}

#[kani::proof]
fn bug_equal_statics_same() {
    assert!(std::ptr::eq(RA, RB));
}
