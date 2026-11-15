// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL -- typed element copies of pointer arrays
//! (`copy_nonoverlapping::<&u32>`, `ptr::copy` within `[&u32; 3]`), and the
//! byte writes over pointer-carrying locals that must still fail closed.
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, measured 2026-09-28):
//!   bug_copy_nonoverlapping_refs             -> FAILED ('assertion failed: *dst[0] == 1')
//!   safe_copy_nonoverlapping_refs            -> SUCCESSFUL
//!   bug_copy_nonoverlapping_raw_ptrs         -> FAILED ('assertion failed: unsafe { *dst[0] } == 1')
//!   safe_copy_nonoverlapping_raw_ptrs        -> SUCCESSFUL
//!   bug_copy_within_refs                     -> FAILED ('assertion failed: *a[0] == 1')
//!   safe_copy_within_refs                    -> SUCCESSFUL
//!   bug_copy_into_ptr_array_then_store       -> FAILED ('assertion failed: *y != 7')
//!   safe_copy_into_ptr_array_then_store      -> SUCCESSFUL
//!   bug_copy_into_one_elem_array_then_store  -> FAILED ('assertion failed: *y != 7')
//!   safe_copy_into_one_elem_array_then_store -> SUCCESSFUL
//!   bug_write_bytes_option_ref_none          -> FAILED ('assertion failed: o.is_some()')
//!   safe_write_bytes_option_ref_none         -> SUCCESSFUL
//!
//! MECHANISM. A local array of two or more pointers is read through memory:
//! `*dst[0]` loads the element and follows the pointer value, so a typed copy
//! into it is exact (main proves the safe rows and certifies the bug rows
//! Genuine). The round-7 untyped-view net refused every byte copy whose
//! destination pointee can hold a pointer, so these clean proofs became
//! FAILED and the bug rows lost their certificates (review of
//! fix/chc-lost-writes round 7, finding 5).
//!
//! FIX (fix/chc-lost-writes round 8): a copy or byte writer fails closed only
//! when its destination is punned or may address a local whose facts are
//! definition-based: a pointer, a non-array aggregate holding one, a
//! one-element array (a pointer wrapper), an integer holding an exposed
//! address. An array of two or more elements and heap memory are exempt. The
//! array rows that store through a copied element pin the exemption's
//! soundness; the one-element array and `Option<&u32>` rows still fail closed.

#![allow(unused)]

#[kani::proof]
fn bug_copy_nonoverlapping_refs() {
    let x = 1u32;
    let y = 2u32;
    let src = [&y, &x];
    let mut dst = [&x, &x];
    unsafe { core::ptr::copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr(), 2) };
    assert!(*dst[0] == 1);
}

#[kani::proof]
fn safe_copy_nonoverlapping_refs() {
    let x = 1u32;
    let y = 2u32;
    let src = [&y, &x];
    let mut dst = [&x, &x];
    unsafe { core::ptr::copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr(), 2) };
    assert!(*dst[0] == 2);
}

#[kani::proof]
fn bug_copy_nonoverlapping_raw_ptrs() {
    let x = 1u32;
    let y = 2u32;
    let src: [*const u32; 2] = [&y, &x];
    let mut dst: [*const u32; 2] = [&x, &x];
    unsafe { core::ptr::copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr(), 2) };
    assert!(unsafe { *dst[0] } == 1);
}

#[kani::proof]
fn safe_copy_nonoverlapping_raw_ptrs() {
    let x = 1u32;
    let y = 2u32;
    let src: [*const u32; 2] = [&y, &x];
    let mut dst: [*const u32; 2] = [&x, &x];
    unsafe { core::ptr::copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr(), 2) };
    assert!(unsafe { *dst[0] } == 2 && unsafe { *dst[1] } == 1);
}

#[kani::proof]
fn bug_copy_within_refs() {
    let x = 1u32;
    let y = 2u32;
    let mut a = [&x, &y, &x];
    unsafe { core::ptr::copy(a.as_ptr().add(1), a.as_mut_ptr(), 2) };
    assert!(*a[0] == 1);
}

#[kani::proof]
fn safe_copy_within_refs() {
    let x = 1u32;
    let y = 2u32;
    let mut a = [&x, &y, &x];
    unsafe { core::ptr::copy(a.as_ptr().add(1), a.as_mut_ptr(), 2) };
    assert!(*a[0] == 2 && *a[1] == 1);
}

// A typed copy into an array of pointers made from boxes, then a store
// through the copied element.
#[kani::proof]
fn bug_copy_into_ptr_array_then_store() {
    let mut b1: Box<u32> = Box::new(0);
    let mut b2: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let src: [*mut u32; 2] = [yp, yp];
    let mut arr: [*mut u32; 2] = [&mut *b1, &mut *b2];
    unsafe { core::ptr::copy_nonoverlapping(src.as_ptr(), arr.as_mut_ptr(), 1) };
    unsafe { *arr[0] = 7; }
    assert!(*y != 7);
}

#[kani::proof]
fn safe_copy_into_ptr_array_then_store() {
    let mut b1: Box<u32> = Box::new(0);
    let mut b2: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let src: [*mut u32; 2] = [yp, yp];
    let mut arr: [*mut u32; 2] = [&mut *b1, &mut *b2];
    unsafe { core::ptr::copy_nonoverlapping(src.as_ptr(), arr.as_mut_ptr(), 1) };
    unsafe { *arr[0] = 7; }
    assert!(*b1 == 0 && *b2 == 0);
}

// The same into a one-element array, a pointer wrapper: fails closed.
#[kani::proof]
fn bug_copy_into_one_elem_array_then_store() {
    let mut b1: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let src: [*mut u32; 1] = [yp];
    let mut arr: [*mut u32; 1] = [&mut *b1];
    unsafe { core::ptr::copy_nonoverlapping(src.as_ptr(), arr.as_mut_ptr(), 1) };
    unsafe { *arr[0] = 7; }
    assert!(*y != 7);
}

#[kani::proof]
fn safe_copy_into_one_elem_array_then_store() {
    let mut b1: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let src: [*mut u32; 1] = [yp];
    let mut arr: [*mut u32; 1] = [&mut *b1];
    unsafe { core::ptr::copy_nonoverlapping(src.as_ptr(), arr.as_mut_ptr(), 1) };
    unsafe { *arr[0] = 7; }
    assert!(*b1 == 0);
}

// Zeroing an `Option<&u32>` local: fails closed.
#[kani::proof]
fn bug_write_bytes_option_ref_none() {
    let x = 1u32;
    let mut o: Option<&u32> = Some(&x);
    unsafe { core::ptr::write_bytes(&mut o as *mut Option<&u32>, 0, 1) };
    assert!(o.is_some());
}

#[kani::proof]
fn safe_write_bytes_option_ref_none() {
    let x = 1u32;
    let mut o: Option<&u32> = Some(&x);
    unsafe { core::ptr::write_bytes(&mut o as *mut Option<&u32>, 0, 1) };
    assert!(o.is_none());
}
