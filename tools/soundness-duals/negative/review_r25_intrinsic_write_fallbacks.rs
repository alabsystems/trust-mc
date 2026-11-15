// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// NEGATIVE PACK (review bypass r25): Pointer-writing intrinsics on a JOINED local, then a read of that local. A fallback that drops the write
// leaves the pre-write state; the new ReadThrough binder turns that state into an exact `==`.
//
// Audit evidence: review of m3/chc-joined-option-eq at f1373b8d1 (2026-09-12),
// bypass pack r25. Every `_must_fail` assertion is violated on a path native Rust
// takes; every `_safe` assertion holds on every path. A `SUCCESSFUL` on a `_must_fail`
// harness in either lane is a false proof.
//
// Oracle (per harness):
//   ptr_swap_then_eq_must_fail            -> VERIFICATION:- FAILED (assertion)
//   ptr_swap_then_eq_safe                 -> VERIFICATION:- SUCCESSFUL
//   copy_nonoverlapping_then_eq_must_fail -> VERIFICATION:- FAILED (assertion)
//   copy_nonoverlapping_then_eq_safe      -> VERIFICATION:- SUCCESSFUL
//   write_volatile_then_eq_must_fail      -> VERIFICATION:- FAILED (assertion)
//   write_volatile_then_eq_safe           -> VERIFICATION:- SUCCESSFUL
//   slice_swap_then_eq_must_fail          -> VERIFICATION:- FAILED (assertion)
//   slice_swap_then_eq_safe               -> VERIFICATION:- SUCCESSFUL
//   mem_swap_then_matches_must_fail       -> VERIFICATION:- FAILED (assertion)
//   mem_swap_then_matches_safe            -> VERIFICATION:- SUCCESSFUL

#[kani::proof]
fn ptr_swap_then_eq_must_fail() {
    let b: bool = kani::any();
    let mut o: Option<u8> = if b { Some(1) } else { Some(2) };
    let mut q: Option<u8> = None;
    unsafe { core::ptr::swap(&mut o, &mut q) };
    assert!(!(o == None));
}
#[kani::proof]
fn ptr_swap_then_eq_safe() {
    let b: bool = kani::any();
    let mut o: Option<u8> = if b { Some(1) } else { Some(2) };
    let mut q: Option<u8> = None;
    unsafe { core::ptr::swap(&mut o, &mut q) };
    assert!(o == None && (q == Some(1)) == b);
}
#[kani::proof]
fn copy_nonoverlapping_then_eq_must_fail() {
    let b: bool = kani::any();
    let mut o: Option<u8> = if b { Some(1) } else { Some(2) };
    let q: Option<u8> = None;
    unsafe { core::ptr::copy_nonoverlapping(&q, &mut o, 1) };
    assert!(!(o == None));
}
#[kani::proof]
fn copy_nonoverlapping_then_eq_safe() {
    let b: bool = kani::any();
    let mut o: Option<u8> = if b { Some(1) } else { Some(2) };
    let q: Option<u8> = None;
    unsafe { core::ptr::copy_nonoverlapping(&q, &mut o, 1) };
    assert!(o == None);
}
#[kani::proof]
fn write_volatile_then_eq_must_fail() {
    let b: bool = kani::any();
    let mut o: Option<u8> = if b { Some(1) } else { Some(2) };
    unsafe { core::ptr::write_volatile(&mut o, None) };
    assert!(!(o == None));
}
#[kani::proof]
fn write_volatile_then_eq_safe() {
    let b: bool = kani::any();
    let mut o: Option<u8> = if b { Some(1) } else { Some(2) };
    unsafe { core::ptr::write_volatile(&mut o, None) };
    assert!(o == None);
}
#[kani::proof]
fn slice_swap_then_eq_must_fail() {
    let b: bool = kani::any();
    let mut a: [Option<u8>; 2] = if b { [Some(1), None] } else { [Some(2), None] };
    a.swap(0, 1);
    assert!(!(a[0] == None));
}
#[kani::proof]
fn slice_swap_then_eq_safe() {
    let b: bool = kani::any();
    let mut a: [Option<u8>; 2] = if b { [Some(1), None] } else { [Some(2), None] };
    a.swap(0, 1);
    assert!(a[0] == None && (a[1] == Some(1)) == b);
}
#[kani::proof]
fn mem_swap_then_matches_must_fail() {
    let b: bool = kani::any();
    let mut o: Option<u8> = if b { Some(1) } else { Some(2) };
    let mut q: Option<u8> = None;
    core::mem::swap(&mut o, &mut q);
    assert!(!matches!(o, None));
}
#[kani::proof]
fn mem_swap_then_matches_safe() {
    let b: bool = kani::any();
    let mut o: Option<u8> = if b { Some(1) } else { Some(2) };
    let mut q: Option<u8> = None;
    core::mem::swap(&mut o, &mut q);
    assert!(matches!(o, None) && matches!(q, Some(_)));
}
