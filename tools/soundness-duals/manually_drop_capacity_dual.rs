// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (both directions) -- a Vec's capacity read through
//! `ManuallyDrop`'s `Deref` (fix/chc-walker-fail-closed, repair round 1,
//! walker fail-closed review 6 finding 8; the review's probes
//! `m1_manuallydrop_cap_safe`, `m2_manuallydrop_cap_leak_safe` and
//! `e18_vec_buffer_safe`, promoted).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, measured 2026-09-28):
//!   md_cap_mul_safe              -> VERIFICATION:- SUCCESSFUL
//!   md_cap_leak_safe             -> VERIFICATION:- SUCCESSFUL
//!   md_cap_mul_bug               -> VERIFICATION:- FAILED  ('attempt to multiply with overflow')
//!   md_cap_value_bug             -> VERIFICATION:- FAILED  ('assertion failed: cap == 4')
//!   md_vec_buffer_walked_dealloc_safe -> VERIFICATION:- SUCCESSFUL
//!
//! MECHANISM UNDER TEST. `<ManuallyDrop<T> as Deref>::deref` returns
//! `&self.value`, the reference it was handed. The statement path's stub
//! table routed it to the `GlobalAllocImpl` havoc, which left the returned
//! reference unconstrained and booked nothing; `Vec::capacity` through it
//! then read the reference local's own capacity side state, which nothing
//! wrote, and `cap * 2` failed "attempt to multiply with overflow",
//! certified Genuine, on main c22e1022e and on the round-2 bundle 5d66fe32
//! (a false certificate on a program Kani proves). `deref` / `deref_mut` are
//! now the address identity in the call spine
//! (`try_dispatch_array_iter_identity_call`), and the result takes the
//! argument's reference target in the precomputed reference analysis
//! (`numeric_ref_propagation.rs`), so the capacity is the wrapped Vec's.
//! The walked-dealloc row frees the Vec's buffer with that capacity through
//! a walked callee: it FAILED Genuine on the round-2 bundle (the capacity was
//! the only freed value, and the walked deallocator booked nothing), and now
//! FAILS uncertified on a havocked nested call inside the walked callee, as
//! it did on main: a known-red precision row, no longer a certificate.
//!
//! Lane scope: CHC only.
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options --harness-timeout=30s manually_drop_capacity_dual.rs

use std::alloc::{Layout, dealloc};

/// Keeps its argument alive through rustc's MIR optimisations.
#[inline(never)]
fn sink<T>(_v: T) {}

#[kani::proof]
fn md_cap_mul_safe() {
    let mut v: Vec<u16> = Vec::with_capacity(3);
    v.push(1);
    let mut v = std::mem::ManuallyDrop::new(v);
    let cap = v.capacity();
    let p = v.as_mut_ptr() as *mut u8;
    sink(p);
    sink(cap * 2);
}
#[kani::proof]
fn md_cap_leak_safe() {
    let mut v: Vec<u16> = Vec::with_capacity(3);
    v.push(1);
    let v = std::mem::ManuallyDrop::new(v);
    let cap = v.capacity();
    sink(cap * 2);
}
#[kani::proof]
fn md_cap_mul_bug() {
    let mut v: Vec<u16> = Vec::with_capacity(3);
    v.push(1);
    let v = std::mem::ManuallyDrop::new(v);
    let cap = v.capacity();
    sink(cap * (usize::MAX / 2));
}
#[kani::proof]
fn md_cap_value_bug() {
    let mut v: Vec<u16> = Vec::with_capacity(3);
    v.push(1);
    let v = std::mem::ManuallyDrop::new(v);
    let cap = v.capacity();
    assert!(cap == 4);
}

fn free_sa(p: *mut u8, size: usize, align: usize) -> u8 {
    unsafe { dealloc(p, Layout::from_size_align_unchecked(size, align)); }
    2
}
#[kani::proof]
fn md_vec_buffer_walked_dealloc_safe() {
    let mut v: Vec<u16> = Vec::with_capacity(3);
    v.push(1);
    let mut v = std::mem::ManuallyDrop::new(v);
    let cap = v.capacity();
    let p = v.as_mut_ptr() as *mut u8;
    let f: fn(*mut u8, usize, usize) -> u8 = free_sa;
    sink(f(p, cap * 2, 2));
}
