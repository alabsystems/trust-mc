// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Exact address models reconcile complete call inventories, never a callee name.
#![allow(dead_code, unused_variables)]
use std::sync::atomic::{AtomicI32, Ordering::SeqCst};
static SIGNED: [AtomicI32; 3] = [AtomicI32::new(-29), AtomicI32::new(-37), AtomicI32::new(-61)];
#[kani::proof]
fn p05_signed_rmw_safe() {
    let c: bool = kani::any();
    let i: usize = kani::any();
    let s: &[AtomicI32] = &SIGNED;
    s[2].store(-47, SeqCst);
    let old = s[2].fetch_add(-6, SeqCst);
    assert!(SIGNED[2].load(SeqCst) == -53, "p05 negative later value");
    assert!(unsafe { *SIGNED[2].as_ptr() } == -53, "p05 signed raw view");
    assert!(
        SIGNED[0].load(SeqCst) == -29 && SIGNED[1].load(SeqCst) == -37,
        "p05 negative neighbors"
    );
    assert!(old == -47, "p05_signed_rmw_safe user assertion");
}
#[kani::proof]
fn p05_signed_rmw_bug() {
    let c: bool = kani::any();
    let i: usize = kani::any();
    let s: &[AtomicI32] = &SIGNED;
    s[2].store(-47, SeqCst);
    let old = s[2].fetch_add(-6, SeqCst);
    assert!(SIGNED[2].load(SeqCst) == -53, "p05 negative later value");
    assert!(unsafe { *SIGNED[2].as_ptr() } == -53, "p05 signed raw view");
    assert!(
        SIGNED[0].load(SeqCst) == -29 && SIGNED[1].load(SeqCst) == -37,
        "p05 negative neighbors"
    );
    assert!(old == -61, "p05_signed_rmw_bug user assertion");
}

#[kani::proof]
fn mixed_exact_opaque_safe() {
    let local = AtomicI32::new(17);
    let exact = SIGNED[1].as_ptr();
    let opaque = local.as_ptr();
    assert!(unsafe { *exact } == -37, "mixed exact value");
    assert!(unsafe { *opaque } == 17, "mixed opaque value");
}
#[kani::proof]
fn mixed_exact_opaque_bug() {
    let local = AtomicI32::new(17);
    let exact = SIGNED[1].as_ptr();
    let opaque = local.as_ptr();
    assert!(unsafe { *exact } == -37, "mixed exact value");
    assert!(unsafe { *opaque } == 19, "mixed stale value");
}
#[inline(never)]
fn nested_address() -> *mut i32 {
    SIGNED[1].as_ptr()
}
#[kani::proof]
fn nested_caller_safe() {
    assert!(unsafe { *nested_address() } == -37, "nested correct");
}
#[kani::proof]
fn nested_caller_bug() {
    assert!(unsafe { *nested_address() } == 0, "nested wrong");
}
#[kani::proof]
fn genuinely_unstubbed_safe() {
    let m = std::sync::Mutex::new(7u32);
    let g = m.lock().unwrap();
    let v = *g;
    let a = [11i32; 4];
    let q = unsafe { (&a[1] as *const i32).offset(1) };
    assert!(v == 7 && unsafe { *q } == 11, "unstubbed correct");
}
#[kani::proof]
fn genuinely_unstubbed_bug() {
    let m = std::sync::Mutex::new(7u32);
    let g = m.lock().unwrap();
    let v = *g;
    let a = [11i32; 4];
    let q = unsafe { (&a[1] as *const i32).offset(1) };
    assert!(unsafe { *q } == 11 && v.wrapping_add(1) != v.wrapping_add(1), "unstubbed false");
}
