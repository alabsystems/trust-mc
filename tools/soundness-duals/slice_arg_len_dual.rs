// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (both directions) -- the length `Vec::extend_from_slice`
//! gives a slice argument that is not a whole array, on the CHC lane (walker
//! fail-closed review, round 2 of the repair after the merge with main's
//! Rule D, 2026-10-15, finding 1).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, measured 2026-10-15):
//!   r1_raw_parts_index3_bug          -> VERIFICATION:- FAILED  ('index out of bounds')
//!   r2_raw_parts_len2_safe           -> VERIFICATION:- SUCCESSFUL
//!   r3_raw_parts_mut_len4_bug        -> VERIFICATION:- FAILED  ('assertion failed: v.len() == 4')
//!   r4_raw_parts_sym_index3_bug      -> VERIFICATION:- FAILED  ('index out of bounds')
//!   r5_raw_parts_from_u16_len4_bug   -> VERIFICATION:- FAILED  ('assertion failed: v.len() == 4')
//!   r6_raw_ptr_then_ref_len4_bug     -> VERIFICATION:- FAILED  ('assertion failed: v.len() == 4')
//!   r7_raw_parts_offset_len4_bug     -> VERIFICATION:- FAILED  ('assertion failed: v.len() == 4')
//!   r8_raw_parts_offset_len3_safe    -> VERIFICATION:- SUCCESSFUL
//!   r9_whole_array_len4_safe         -> VERIFICATION:- SUCCESSFUL
//!   r10_whole_array_len3_bug         -> VERIFICATION:- FAILED  ('assertion failed: v.len() == 3')
//!   r11_whole_u16_array_len3_safe    -> VERIFICATION:- SUCCESSFUL
//!
//! MECHANISM UNDER TEST. Round 1 of the repair gave `resolve_slice_arg_length`
//! a strategy that returned the static length of whatever array local the
//! slice argument's reference names, ignoring its subslice length and its
//! pointer metadata. `&*ptr::slice_from_raw_parts(a.as_ptr(), 2)` names the
//! whole array `a`, so `v.extend_from_slice(s)` appended 4 elements and the
//! out-of-bounds `v[3]` verified clean where Kani fails (r1, r3-r7), and
//! `v.len() == 2` failed certified Genuine (r2, r8). The strategy now asks the
//! resolver `PtrMetadata` itself uses (`resolve_ptr_metadata_known`): the
//! static length of an unsized `&[T; N]`, a subslice's length, a raw slice's
//! `len` argument, a flattened wide pointer's metadata word
//! (`codegen_call_vec_resolve.rs`). r9-r11 are the whole-array rows round 1
//! fixed.
//!
//! Lane scope: CHC (the length resolution is the CHC lane's).
//!
//! Run: trust-mc-driver -Z unstable-options --harness-timeout=30s --ay-chc slice_arg_len_dual.rs

#[kani::proof]
fn r1_raw_parts_index3_bug() {
    let a: [u8; 4] = [1, 2, 3, 4];
    let s: &[u8] = unsafe { &*core::ptr::slice_from_raw_parts(a.as_ptr(), 2) };
    let mut v: Vec<u8> = Vec::new();
    v.extend_from_slice(s);
    let _ = v[3];
}

#[kani::proof]
fn r2_raw_parts_len2_safe() {
    let a: [u8; 4] = kani::any();
    let s: &[u8] = unsafe { &*core::ptr::slice_from_raw_parts(a.as_ptr(), 2) };
    let mut v: Vec<u8> = Vec::new();
    v.extend_from_slice(s);
    assert!(v.len() == 2);
}

#[kani::proof]
fn r3_raw_parts_mut_len4_bug() {
    let mut a: [u8; 4] = kani::any();
    let s: &mut [u8] = unsafe { &mut *core::ptr::slice_from_raw_parts_mut(a.as_mut_ptr(), 2) };
    let mut v: Vec<u8> = Vec::new();
    v.extend_from_slice(s);
    assert!(v.len() == 4);
}

#[kani::proof]
fn r4_raw_parts_sym_index3_bug() {
    let a: [u8; 4] = kani::any();
    let s: &[u8] = unsafe { &*core::ptr::slice_from_raw_parts(a.as_ptr(), 2) };
    let mut v: Vec<u8> = Vec::new();
    v.extend_from_slice(s);
    let _ = v[3];
}

#[kani::proof]
fn r5_raw_parts_from_u16_len4_bug() {
    let a: [u16; 4] = kani::any();
    let s: &[u8] = unsafe { &*core::ptr::slice_from_raw_parts(a.as_ptr() as *const u8, 8) };
    let mut v: Vec<u8> = Vec::new();
    v.extend_from_slice(s);
    assert!(v.len() == 4);
}

#[kani::proof]
fn r6_raw_ptr_then_ref_len4_bug() {
    let a: [u8; 4] = kani::any();
    let p: *const [u8] = core::ptr::slice_from_raw_parts(a.as_ptr(), 2);
    let s: &[u8] = unsafe { &*p };
    let mut v: Vec<u8> = Vec::new();
    v.extend_from_slice(s);
    assert!(v.len() == 4);
}

#[kani::proof]
fn r7_raw_parts_offset_len4_bug() {
    let a: [u8; 4] = kani::any();
    let s: &[u8] = unsafe { &*core::ptr::slice_from_raw_parts(a.as_ptr().add(1), 3) };
    let mut v: Vec<u8> = Vec::new();
    v.extend_from_slice(s);
    assert!(v.len() == 4);
}

#[kani::proof]
fn r8_raw_parts_offset_len3_safe() {
    let a: [u8; 4] = kani::any();
    let s: &[u8] = unsafe { &*core::ptr::slice_from_raw_parts(a.as_ptr().add(1), 3) };
    let mut v: Vec<u8> = Vec::new();
    v.extend_from_slice(s);
    assert!(v.len() == 3);
}

#[kani::proof]
fn r9_whole_array_len4_safe() {
    let a: [u8; 4] = kani::any();
    let mut v: Vec<u8> = Vec::new();
    v.extend_from_slice(&a);
    assert!(v.len() == 4);
}

#[kani::proof]
fn r10_whole_array_len3_bug() {
    let a: [u8; 4] = kani::any();
    let mut v: Vec<u8> = Vec::new();
    v.extend_from_slice(&a);
    assert!(v.len() == 3);
}

#[kani::proof]
fn r11_whole_u16_array_len3_safe() {
    let a: [u16; 3] = kani::any();
    let s: &[u16] = &a;
    let mut v: Vec<u16> = Vec::new();
    v.extend_from_slice(s);
    assert!(v.len() == 3);
}
