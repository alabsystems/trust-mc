// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Oracle (per harness; Rust semantics, confirmed by running the program
// natively under Trust seal 9192, one process per harness):
//   safe_struct_value_ref_field   -> VERIFICATION:- SUCCESSFUL
//   bug_struct_value_ref_field    -> VERIFICATION:- FAILED (assertion)
//   safe_tuple_value_refs         -> VERIFICATION:- SUCCESSFUL
//   bug_tuple_value_refs          -> VERIFICATION:- FAILED (assertion)
//   safe_array_value_refs         -> VERIFICATION:- SUCCESSFUL
//   bug_array_value_refs          -> VERIFICATION:- FAILED (assertion)
//   safe_raw_ptr_array_non_null   -> VERIFICATION:- SUCCESSFUL
//   bug_raw_ptr_array_null        -> VERIFICATION:- FAILED (assertion)
//   safe_raw_ptr_array_identity   -> VERIFICATION:- SUCCESSFUL
//   bug_raw_ptr_array_identity    -> VERIFICATION:- FAILED (assertion)
//   safe_raw_ptr_array_deref      -> VERIFICATION:- SUCCESSFUL
//   bug_raw_ptr_array_deref       -> VERIFICATION:- FAILED (assertion)
//   safe_str_slice_elem           -> VERIFICATION:- SUCCESSFUL
//   bug_str_slice_elem            -> VERIFICATION:- FAILED (assertion)
//   safe_fn_ptr_array             -> VERIFICATION:- SUCCESSFUL
//   bug_fn_ptr_array              -> VERIFICATION:- FAILED (assertion)
//   safe_struct_value_raw_ptr     -> VERIFICATION:- SUCCESSFUL
//   bug_struct_value_raw_ptr_null -> VERIFICATION:- FAILED (assertion)
//
// WHY THIS FILE EXISTS. Bytes covered by a relocation are never data. A pointer
// stored inside a constant VALUE (an array element, a tuple or struct field) is
// that relocation's target plus the offset its bytes carry, never the offset
// read as an integer. The rule is stated once, in
// trust-mc-compiler/src/codegen_ay/shared/const_pointer.rs.
//
// Measured on main 5b8582dd4 (round-10 challenge, 30 s per harness, ay
// 48c98a43d): for `PTRS: [*const u32; 2] = [&raw const PAIR.0, &raw const
// PAIR.1]`, `PTRS[0].is_null()` PROVED on BOTH lanes (the slot decoded as its
// raw offset 0), and `safe_raw_ptr_array_{non_null,identity,deref}`,
// `safe_struct_value_raw_ptr` and (CHC) `safe_struct_value_ref_field` /
// `safe_array_value_refs` FAILED certified Genuine.

#![allow(dead_code)]

static PAIR: (u32, u32) = (1, 2);
const A3: &[u32; 3] = &[10, 20, 30];
#[repr(C)]
struct H {
    tag: u64,
    r: &'static u32,
}
const HC: H = H { tag: 7, r: &[1u32, 2, 3][1] };
const T2: (&u32, &u32) = (&A3[0], &A3[2]);
const REFS: [&u32; 2] = [&10, &20];
const PTRS: [*const u32; 2] = [&raw const PAIR.0, &raw const PAIR.1];
const WORDS: &[&str] = &["ab", "cd"];
fn one() -> u32 {
    1
}
fn two() -> u32 {
    2
}
const FS: [fn() -> u32; 2] = [one, two];

#[repr(C)]
struct RawHolder {
    tag: u64,
    p: *const u32,
}
const RH: RawHolder = RawHolder { tag: 9, p: &raw const PAIR.1 };

#[kani::proof]
fn safe_struct_value_ref_field() {
    assert!(HC.tag == 7);
    assert!(*HC.r == 2);
}

#[kani::proof]
fn bug_struct_value_ref_field() {
    assert!(*HC.r == 1);
}

#[kani::proof]
fn safe_tuple_value_refs() {
    assert!(*T2.0 == 10);
    assert!(*T2.1 == 30);
}

#[kani::proof]
fn bug_tuple_value_refs() {
    assert!(*T2.1 == 10);
}

#[kani::proof]
fn safe_array_value_refs() {
    assert!(*REFS[1] == 20);
}

#[kani::proof]
fn bug_array_value_refs() {
    assert!(*REFS[1] == 10);
}

#[kani::proof]
fn safe_raw_ptr_array_non_null() {
    assert!(!PTRS[0].is_null());
    assert!(!PTRS[1].is_null());
}

#[kani::proof]
fn bug_raw_ptr_array_null() {
    assert!(PTRS[0].is_null());
}

#[kani::proof]
fn safe_raw_ptr_array_identity() {
    assert!(std::ptr::eq(PTRS[1], &PAIR.1));
    assert!(std::ptr::eq(PTRS[0], &PAIR.0));
}

#[kani::proof]
fn bug_raw_ptr_array_identity() {
    assert!(std::ptr::eq(PTRS[0], PTRS[1]));
}

#[kani::proof]
fn safe_raw_ptr_array_deref() {
    assert!(unsafe { *PTRS[1] } == 2);
}

#[kani::proof]
fn bug_raw_ptr_array_deref() {
    assert!(unsafe { *PTRS[1] } == 1);
}

#[kani::proof]
fn safe_str_slice_elem() {
    assert!(WORDS[1].len() == 2);
    assert!(WORDS[1].as_bytes()[0] == b'c');
}

#[kani::proof]
fn bug_str_slice_elem() {
    assert!(WORDS[1].as_bytes()[0] == b'a');
}

#[kani::proof]
fn safe_fn_ptr_array() {
    assert!(FS[1]() == 2);
}

#[kani::proof]
fn bug_fn_ptr_array() {
    assert!(FS[1]() == 1);
}

#[kani::proof]
fn safe_struct_value_raw_ptr() {
    assert!(!RH.p.is_null());
    assert!(unsafe { *RH.p } == 2);
}

#[kani::proof]
fn bug_struct_value_raw_ptr_null() {
    assert!(RH.p.is_null());
}
