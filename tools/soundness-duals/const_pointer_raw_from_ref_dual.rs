// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Oracle (per harness; Rust semantics, confirmed by running the program
// natively under Trust seal 9192, one process per harness and seed):
//   safe_str_as_ptr           -> VERIFICATION:- SUCCESSFUL
//   bug_str_as_ptr            -> VERIFICATION:- FAILED (assertion)
//   safe_slice_as_ptr         -> VERIFICATION:- SUCCESSFUL
//   bug_slice_as_ptr          -> VERIFICATION:- FAILED (assertion)
//   safe_subslice_wrapping    -> VERIFICATION:- SUCCESSFUL
//   bug_subslice_wrapping     -> VERIFICATION:- FAILED (assertion)
//   safe_coerced_wrapping     -> VERIFICATION:- SUCCESSFUL
//   bug_coerced_wrapping      -> VERIFICATION:- FAILED (assertion)
//   safe_wrapping_sub         -> VERIFICATION:- SUCCESSFUL
//   bug_wrapping_sub          -> VERIFICATION:- FAILED (assertion)
//   safe_byte_add             -> VERIFICATION:- SUCCESSFUL
//   bug_byte_add              -> VERIFICATION:- FAILED (assertion)
//   safe_ptr_read             -> VERIFICATION:- SUCCESSFUL
//   bug_ptr_read              -> VERIFICATION:- FAILED (assertion)
//   safe_from_raw_parts       -> VERIFICATION:- SUCCESSFUL
//   bug_from_raw_parts        -> VERIFICATION:- FAILED (assertion)
//   safe_nested_wrapping      -> VERIFICATION:- SUCCESSFUL
//   bug_nested_wrapping       -> VERIFICATION:- FAILED (assertion)
//   safe_substr_as_ptr        -> VERIFICATION:- SUCCESSFUL
//   bug_substr_as_ptr         -> VERIFICATION:- FAILED (assertion)
//   safe_static_byte_wrapping -> VERIFICATION:- SUCCESSFUL
//   bug_static_byte_wrapping  -> VERIFICATION:- FAILED (assertion)
//   safe_int_roundtrip        -> VERIFICATION:- SUCCESSFUL
//   bug_int_roundtrip         -> VERIFICATION:- FAILED (assertion)
//
// WHY THIS FILE EXISTS. A constant pointer's target is known WHOLE when it
// is fixed, at every type and offset the harness reads it through a pointer
// (trust-mc-compiler/src/codegen_ay/shared/const_pointer.rs). These harnesses
// derive a RAW pointer from a constant REFERENCE (a cast, a coercion,
// `as_ptr`, `wrapping_add`/`wrapping_sub`, `byte_add`, `ptr::read`,
// `slice::from_raw_parts`, a nested `&&T` hop, a static's element, an integer
// round trip) and read the target through memory, outside the window the
// constant names.
//
// Measured on main 5b8582dd4 (round-10 resume, 30 s per harness, ay
// 48c98a43d): CHC 2 missed bugs (`bug_subslice_wrapping`,
// `bug_substr_as_ptr`: a subslice constant read from its target's byte 0) and
// 8 false certificates; BMC 7 false certificates (the reference lane named
// the target's address without putting its bytes on the initial memory, so
// the raw read saw free memory). With the rule: CHC no missed bug and no
// false certificate; BMC none (statement/global_alloc.rs
// `global_alloc_address` materializes a fixed target it names).
// `safe_int_roundtrip` was a CHC false certificate on main and with the rule
// until the integer-to-pointer cast recorded its invalidation
// (`PointerWithExposedProvenance`, chc/stmt/codegen_stmt_rvalue_ref/
// cast_dispatch.rs, #3350, invalidates the object its identity term names,
// here the constant's own object): it is now a false failure on both lanes,
// never certified (CHC records `int_to_ptr_obj_invalidated`, BMC
// `pointer_with_exposed_provenance`: soundness.md, "Integer-to-pointer casts:
// one rule, both lanes").


#![allow(dead_code)]

const E: &u32 = &[1u32, 2, 3][1];
const S: &str = "hello";
const SL: &[u32] = &[1, 2, 3];
const SUB: &[u32] = [1u32, 2, 3, 4].split_at(1).1;
const NE: &&u32 = &&[1u32, 2, 3][1];
const T: &str = "hello".split_at(2).1;
static ARR: [u32; 3] = [1, 2, 3];

#[kani::proof]
fn safe_str_as_ptr() {
    let p = S.as_ptr();
    unsafe { assert!(*p.add(1) == b'e') }
}
#[kani::proof]
fn bug_str_as_ptr() {
    let p = S.as_ptr();
    unsafe { assert!(*p.add(1) == b'h') }
}
#[kani::proof]
fn safe_slice_as_ptr() {
    let p = SL.as_ptr();
    unsafe { assert!(*p.add(2) == 3) }
}
#[kani::proof]
fn bug_slice_as_ptr() {
    let p = SL.as_ptr();
    unsafe { assert!(*p.add(2) == 2) }
}
#[kani::proof]
fn safe_subslice_wrapping() {
    let p = SUB.as_ptr();
    unsafe { assert!(*p.wrapping_add(1) == 3) }
}
#[kani::proof]
fn bug_subslice_wrapping() {
    let p = SUB.as_ptr();
    unsafe { assert!(*p.wrapping_add(1) == 2) }
}
#[kani::proof]
fn safe_coerced_wrapping() {
    let p: *const u32 = E;
    unsafe { assert!(*p.wrapping_add(1) == 3) }
}
#[kani::proof]
fn bug_coerced_wrapping() {
    let p: *const u32 = E;
    unsafe { assert!(*p.wrapping_add(1) == 2) }
}
#[kani::proof]
fn safe_wrapping_sub() {
    let p = (E as *const u32).wrapping_sub(1);
    unsafe { assert!(*p == 1) }
}
#[kani::proof]
fn bug_wrapping_sub() {
    let p = (E as *const u32).wrapping_sub(1);
    unsafe { assert!(*p == 2) }
}
#[kani::proof]
fn safe_byte_add() {
    let p = unsafe { (E as *const u32).byte_add(4) };
    unsafe { assert!(*p == 3) }
}
#[kani::proof]
fn bug_byte_add() {
    let p = unsafe { (E as *const u32).byte_add(4) };
    unsafe { assert!(*p == 2) }
}
#[kani::proof]
fn safe_ptr_read() {
    let v = unsafe { std::ptr::read((E as *const u32).wrapping_add(1)) };
    assert!(v == 3);
}
#[kani::proof]
fn bug_ptr_read() {
    let v = unsafe { std::ptr::read((E as *const u32).wrapping_add(1)) };
    assert!(v == 2);
}
#[kani::proof]
fn safe_from_raw_parts() {
    let s = unsafe { std::slice::from_raw_parts(E as *const u32, 2) };
    assert!(s[1] == 3);
}
#[kani::proof]
fn bug_from_raw_parts() {
    let s = unsafe { std::slice::from_raw_parts(E as *const u32, 2) };
    assert!(s[1] == 2);
}
#[kani::proof]
fn safe_nested_wrapping() {
    let p = (*NE as *const u32).wrapping_add(1);
    unsafe { assert!(*p == 3) }
}
#[kani::proof]
fn bug_nested_wrapping() {
    let p = (*NE as *const u32).wrapping_add(1);
    unsafe { assert!(*p == 2) }
}
#[kani::proof]
fn safe_substr_as_ptr() {
    let p = T.as_ptr();
    unsafe { assert!(*p.wrapping_add(2) == b'o') }
}
#[kani::proof]
fn bug_substr_as_ptr() {
    let p = T.as_ptr();
    unsafe { assert!(*p.wrapping_add(2) == b'l') }
}
#[kani::proof]
fn safe_static_byte_wrapping() {
    let p = (&ARR[0] as *const u32 as *const u8).wrapping_add(8) as *const u32;
    unsafe { assert!(*p == 3) }
}
#[kani::proof]
fn bug_static_byte_wrapping() {
    let p = (&ARR[0] as *const u32 as *const u8).wrapping_add(8) as *const u32;
    unsafe { assert!(*p == 1) }
}
#[kani::proof]
fn safe_int_roundtrip() {
    let a = E as *const u32 as usize;
    let p = (a + 4) as *const u32;
    unsafe { assert!(*p == 3) }
}
#[kani::proof]
fn bug_int_roundtrip() {
    let a = E as *const u32 as usize;
    let p = (a + 4) as *const u32;
    unsafe { assert!(*p == 2) }
}
