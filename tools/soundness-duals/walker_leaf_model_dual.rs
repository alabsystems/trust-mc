// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (both directions) -- body-less callees the CHC walker now
//! models itself: the vtable reads and the deallocator
//! (fix/chc-walker-fail-closed, package round 2 item e).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, measured 2026-09-27):
//!   e2_size_value_safe               -> VERIFICATION:- SUCCESSFUL
//!   e2_size_value_bug                -> VERIFICATION:- FAILED  ('assertion failed: m.measure(meta, 1) == 4')
//!   e2_size_unrelated_overflow_bug   -> VERIFICATION:- FAILED  ('attempt to add with overflow')
//!   e5_fnptr_dealloc_safe            -> VERIFICATION:- SUCCESSFUL
//!   e5_fnptr_double_free_bug         -> VERIFICATION:- FAILED  (the second free)
//!   e5_fnptr_size_mismatch_bug       -> VERIFICATION:- FAILED  ('rust_dealloc must be called on an object whose allocated size matches its layout')
//!
//! MECHANISM UNDER TEST. A call the walker cannot inline is havocked, and a
//! havocked `unsafe` callee of another crate books the demoting
//! `nested_call_dropped_obligation` (Mechanism B). `vtable_size` /
//! `vtable_align` (reached through `DynMetadata::size_of` / `align_of`) and
//! `__rust_dealloc` (through `alloc::dealloc`) took that path, so every safe
//! row here was demoted on the first round's bundle. The walker now models
//! them (`leaf_models.rs`): a vtable read is a read of the registered layout
//! of the identity the pointer holds (a vtable pointer is an identity minted
//! at an unsize coercion, with nothing to check), and the deallocator is the
//! statement path's contract (`dealloc_pointer_terms`: live heap object,
//! base address, matching size; power-of-two alignment) with the free applied
//! to the rule's running `obj_valid`, so a second free is caught. Its layout
//! is read from the packed `Layout` (`bv128 = concat(size, align)`) the
//! walker now builds and reads (`inline_aggregate.rs`, the `Layout` getters).
//!
//! Lane scope: CHC only.
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options --harness-timeout=30s walker_leaf_model_dual.rs

#![feature(ptr_metadata)]
use std::alloc::{alloc, dealloc, Layout};
use std::ptr::DynMetadata;

/// Keeps its argument alive through rustc's MIR optimisations.
#[inline(never)]
fn sink<T>(_v: T) {}

pub trait Shape { fn area(&self) -> u32; }
pub struct Sq(pub u32);
pub struct Wide(pub u64, pub u64);
impl Shape for Sq { fn area(&self) -> u32 { self.0 } }
impl Shape for Wide { fn area(&self) -> u32 { 2 } }

// The vtable read in a walked method: its value, and an unrelated check.
pub trait Meas { fn measure(&self, meta: DynMetadata<dyn Shape>, k: u8) -> usize; }
pub struct M;
pub struct N;
impl Meas for M {
    fn measure(&self, meta: DynMetadata<dyn Shape>, k: u8) -> usize {
        sink(k + 1);
        meta.size_of()
    }
}
impl Meas for N { fn measure(&self, _meta: DynMetadata<dyn Shape>, _k: u8) -> usize { 4 } }

#[kani::proof]
fn e2_size_value_safe() {
    let s: &dyn Shape = &Sq(3);
    let meta = std::ptr::metadata(s as *const dyn Shape);
    let m: Box<dyn Meas> = if kani::any() { Box::new(M) } else { Box::new(N) };
    assert!(m.measure(meta, 1) == 4);
}
#[kani::proof]
fn e2_size_value_bug() {
    let s: &dyn Shape = &Wide(1, 2);
    let meta = std::ptr::metadata(s as *const dyn Shape);
    let m: Box<dyn Meas> = if kani::any() { Box::new(M) } else { Box::new(N) };
    assert!(m.measure(meta, 1) == 4);
}
#[kani::proof]
fn e2_size_unrelated_overflow_bug() {
    let k: u8 = kani::any();
    let s: &dyn Shape = &Sq(3);
    let meta = std::ptr::metadata(s as *const dyn Shape);
    let m: Box<dyn Meas> = if kani::any() { Box::new(M) } else { Box::new(N) };
    sink(m.measure(meta, k));
}
// The deallocator, reached through a function pointer the walker resolves to
// one target (no SwitchInt arm, so the free is not a branch-arm effect).
fn free_it(p: *mut u8, size: usize) -> u8 {
    unsafe { dealloc(p, Layout::from_size_align_unchecked(size, 4)); }
    2
}
#[kani::proof]
fn e5_fnptr_dealloc_safe() {
    let p = unsafe { alloc(Layout::new::<u32>()) };
    kani::assume(!p.is_null());
    let f: fn(*mut u8, usize) -> u8 = free_it;
    sink(f(p, 4));
}
#[kani::proof]
fn e5_fnptr_double_free_bug() {
    let p = unsafe { alloc(Layout::new::<u32>()) };
    kani::assume(!p.is_null());
    let f: fn(*mut u8, usize) -> u8 = free_it;
    sink(f(p, 4));
    sink(f(p, 4));
}
#[kani::proof]
fn e5_fnptr_size_mismatch_bug() {
    let p = unsafe { alloc(Layout::new::<u32>()) };
    kani::assume(!p.is_null());
    let f: fn(*mut u8, usize) -> u8 = free_it;
    sink(f(p, 8));
}
