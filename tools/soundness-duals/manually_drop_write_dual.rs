// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (both directions) -- collection writes through
//! `<ManuallyDrop<Vec<T>> as DerefMut>::deref_mut`, read back through
//! `Deref` or `ManuallyDrop::into_inner` (fix/chc-walker-fail-closed, repair
//! round 2, walker fail-closed review 6 round 2 finding 4; the review's
//! probes `rp7_md.rs`, `rp8_cap_growth.rs` and `rp10_more.rs`, promoted).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, measured 2026-09-28):
//!   m4_cap_after_growth_bug       -> VERIFICATION:- FAILED  ('assertion failed: md.capacity() == 1')
//!   m4_cap_after_growth_safe      -> VERIFICATION:- SUCCESSFUL
//!   m13_new_push_cap_bug          -> VERIFICATION:- FAILED  ('assertion failed: md.capacity() == 0')
//!   m14_extend_cap_bug            -> VERIFICATION:- FAILED  ('assertion failed: md.capacity() == 2')
//!   m15_push_cap_sym_bug          -> VERIFICATION:- FAILED  ('assertion failed: md.capacity() == 1')
//!   m3_into_inner_len_bug         -> VERIFICATION:- FAILED  ('assertion failed: v.len() == 2')
//!   m3_into_inner_len_safe        -> VERIFICATION:- SUCCESSFUL
//!   m6_scalar_deref_bug           -> VERIFICATION:- FAILED  ('assertion failed: *md != x')
//!   m6_scalar_deref_safe          -> VERIFICATION:- SUCCESSFUL
//!   v1_plain_cap_after_growth_bug -> VERIFICATION:- FAILED  ('assertion failed: v.capacity() == 1')
//!   v1_plain_cap_after_growth_safe-> VERIFICATION:- SUCCESSFUL
//!
//! MECHANISM UNDER TEST. Repair round 1 made `ManuallyDrop::deref` /
//! `deref_mut` the address identity in the CHC call spine. A write through
//! `deref_mut` into a `Vec` reaches the wrapper's memory but not the
//! per-local capacity side state (`ManuallyDrop<Vec<T>>` has none of its
//! own), so a capacity read after `push` / `extend_from_slice` returned the
//! `with_capacity` value: the m4 / m13 / m14 / m15 bug rows verified clean on
//! the repair-round-1 bundle 8626027c. On main the `GlobalAllocImpl` stub
//! lost the write to a havocked reference instead, and `m4_cap_after_growth_safe`
//! and `m3_into_inner_len_safe` were certified Genuine on programs Kani
//! proves. A collection write through `ManuallyDrop::deref_mut` now fails
//! closed (`codegen_call_spine_helpers.rs`,
//! `manually_drop_collection_write_unmodelled`); a `deref_mut` whose result
//! only feeds `as_mut_ptr` / `len` / `capacity`, and every scalar or array
//! `ManuallyDrop` (m6), keeps the exact identity.
//!
//! Lane scope: CHC only.
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options --harness-timeout=30s manually_drop_write_dual.rs

use std::mem::ManuallyDrop;

#[kani::proof]
fn m4_cap_after_growth_bug() {
    let mut md = ManuallyDrop::new(Vec::<u8>::with_capacity(1));
    md.push(1);
    md.push(2);
    assert!(md.capacity() == 1);
}
#[kani::proof]
fn m4_cap_after_growth_safe() {
    let mut md = ManuallyDrop::new(Vec::<u8>::with_capacity(1));
    md.push(1);
    md.push(2);
    assert!(md.capacity() >= 2);
}
#[kani::proof]
fn m13_new_push_cap_bug() {
    let mut md = ManuallyDrop::new(Vec::<u8>::new());
    md.push(1);
    assert!(md.capacity() == 0);
}
#[kani::proof]
fn m14_extend_cap_bug() {
    let mut md = ManuallyDrop::new(Vec::<u8>::with_capacity(2));
    md.extend_from_slice(&[1, 2, 3]);
    assert!(md.capacity() == 2);
}
#[kani::proof]
#[kani::unwind(5)]
fn m15_push_cap_sym_bug() {
    let n: u8 = kani::any();
    kani::assume(n >= 1 && n <= 3);
    let mut md = ManuallyDrop::new(Vec::<u8>::with_capacity(1));
    for i in 0..n {
        md.push(i);
    }
    assert!(md.capacity() == 1);
}
#[kani::proof]
fn m3_into_inner_len_bug() {
    let mut md = ManuallyDrop::new(vec![1u8, 2]);
    md.push(3);
    let v = ManuallyDrop::into_inner(md);
    assert!(v.len() == 2);
}
#[kani::proof]
fn m3_into_inner_len_safe() {
    let mut md = ManuallyDrop::new(vec![1u8, 2]);
    md.push(3);
    let v = ManuallyDrop::into_inner(md);
    assert!(v.len() == 3);
}
#[kani::proof]
fn m6_scalar_deref_bug() {
    let x: u32 = kani::any();
    let md = ManuallyDrop::new(x);
    assert!(*md != x);
}
#[kani::proof]
fn m6_scalar_deref_safe() {
    let x: u32 = kani::any();
    let md = ManuallyDrop::new(x);
    assert!(*md == x);
}
#[kani::proof]
fn v1_plain_cap_after_growth_bug() {
    let mut v = Vec::<u8>::with_capacity(1);
    v.push(1);
    v.push(2);
    assert!(v.capacity() == 1);
}
#[kani::proof]
fn v1_plain_cap_after_growth_safe() {
    let mut v = Vec::<u8>::with_capacity(1);
    v.push(1);
    v.push(2);
    assert!(v.capacity() >= 2);
}
