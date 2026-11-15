// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// NEGATIVE PACK: a call that MOVES a POINTER value out of one storage and
// another in. The bindings the model keeps for a pointer — which object it
// points at, a sub-slice offset, a collection index — must travel with the
// value, or the statement must fail closed.
//
// `mem::swap` has an exact handler. Its siblings are INLINED and had none:
// `let mut a = &mut x; let old = mem::replace(&mut a, &mut y); *old = 7;
// *a = 9; assert!(y == 2)` verified SUCCESSFUL in CHC and its safe twin was
// FAILED [AY:CTREX_CAT:Genuine]; `mem::swap` of two SLICE VIEWS did not
// exchange the views either, with both views starting at index 0 so no
// sub-slice offset was involved. Found by the third adversarial review
// (2026-09-14); red on origin/main too. Ground truth compiled and run natively
// on the frozen nightly-2025-12-03 rustc.
//
// Oracle (per harness):
//   *_must_fail   -> VERIFICATION:- FAILED; never SUCCESSFUL
//   *_safe        -> never a Genuine counterexample

use std::mem;

#[kani::proof]
fn mem_replace_ref_store_must_fail() {
    let mut x = 1u8;
    let mut y = 2u8;
    {
        let mut a: &mut u8 = &mut x;
        let old = mem::replace(&mut a, &mut y);
        *old = 7;
        *a = 9;
    }
    assert!(y == 2); // truth: 9
}

#[kani::proof]
fn mem_replace_ref_store_safe() {
    let mut x = 1u8;
    let mut y = 2u8;
    {
        let mut a: &mut u8 = &mut x;
        let old = mem::replace(&mut a, &mut y);
        *old = 7;
        *a = 9;
    }
    assert!(x == 7 && y == 9);
}

#[kani::proof]
fn option_replace_ref_store_must_fail() {
    let mut x = 1u8;
    let mut y = 2u8;
    {
        let mut o: Option<&mut u8> = Some(&mut x);
        let old = o.replace(&mut y);
        *old.unwrap() = 7;
        *o.unwrap() = 9;
    }
    assert!(y == 2); // truth: 9
}

#[kani::proof]
fn option_replace_ref_store_safe() {
    let mut x = 1u8;
    let mut y = 2u8;
    {
        let mut o: Option<&mut u8> = Some(&mut x);
        let old = o.replace(&mut y);
        *old.unwrap() = 7;
        *o.unwrap() = 9;
    }
    assert!(x == 7 && y == 9);
}

#[kani::proof]
fn option_take_ref_store_must_fail() {
    let mut y = 2u8;
    {
        let a: &mut u8 = &mut y;
        let mut holder: Option<&mut u8> = Some(a);
        let taken = holder.take();
        *taken.unwrap() = 9;
    }
    assert!(y == 2); // truth: 9
}

#[kani::proof]
fn ptr_replace_ref_store_must_fail() {
    let mut x = 1u8;
    let mut y = 2u8;
    unsafe {
        let mut a: *mut u8 = &mut x;
        let old = std::ptr::replace(&mut a, &mut y as *mut u8);
        *old = 7;
        *a = 9;
    }
    assert!(y == 2); // truth: 9
}

#[kani::proof]
fn swap_views_read_must_fail() {
    let a = [1u8, 2];
    let b = [3u8, 4];
    let mut s: &[u8] = &a[..];
    let mut t: &[u8] = &b[..];
    mem::swap(&mut s, &mut t);
    assert!(s[0] == 1); // truth: 3
}

#[kani::proof]
fn swap_views_read_safe() {
    let a = [1u8, 2];
    let b = [3u8, 4];
    let mut s: &[u8] = &a[..];
    let mut t: &[u8] = &b[..];
    mem::swap(&mut s, &mut t);
    assert!(s[0] == 3 && t[0] == 1);
}

#[kani::proof]
fn swap_boxes_store_safe() {
    let mut b1: Box<u8> = Box::new(1);
    let mut b2: Box<u8> = Box::new(2);
    mem::swap(&mut b1, &mut b2);
    *b1 = 9;
    assert!(*b1 == 9 && *b2 == 1);
}

/// The read twin of `swap_boxes_store_safe`: after the swap `*b1` is 2. The
/// baseline a15de6272 PROVED `*b1 == 1` (a missed bug, review of
/// fix/chc-false-certificates, 2026-09-27, probe w1_box_swap.rs); the swap's
/// fail-closed booking fails it now.
#[kani::proof]
fn swap_boxes_read_must_fail() {
    let mut b1: Box<u8> = Box::new(1);
    let mut b2: Box<u8> = Box::new(2);
    mem::swap(&mut b1, &mut b2);
    assert!(*b1 == 1);
}

/// A real bug unrelated to the swap: `x + *b1` overflows for `x == 255`. The
/// harness-wide Box-swap booking of 49f33e5d8 cost it the Genuine label main
/// gave it (review of fix/chc-false-certificates, 2026-09-27, probe
/// w1_box_swap.rs `swap_then_overflow_bug`); the swap now exchanges the boxes'
/// allocation facts.
#[kani::proof]
fn swap_then_overflow_must_fail() {
    let mut b1: Box<u8> = Box::new(1);
    let mut b2: Box<u8> = Box::new(2);
    mem::swap(&mut b1, &mut b2);
    let x: u8 = kani::any();
    let y = x + *b1;
    assert!(y >= 2);
}

#[kani::proof]
fn swap_boxes_read_safe() {
    let mut b1: Box<u8> = Box::new(1);
    let mut b2: Box<u8> = Box::new(2);
    mem::swap(&mut b1, &mut b2);
    assert!(*b1 == 2 && *b2 == 1);
}

/// A swap on ONE arm of a branch: after the join `b1` points at either
/// allocation, so the per-local facts cannot be exchanged; this keeps the
/// fail-closed booking.
#[kani::proof]
fn swap_boxes_cond_read_safe() {
    let mut b1: Box<u8> = Box::new(1);
    let mut b2: Box<u8> = Box::new(2);
    let c: bool = kani::any();
    if c {
        mem::swap(&mut b1, &mut b2);
    }
    assert!(*b1 == if c { 2 } else { 1 });
}

#[kani::proof]
fn swap_boxes_cond_read_must_fail() {
    let mut b1: Box<u8> = Box::new(1);
    let mut b2: Box<u8> = Box::new(2);
    let c: bool = kani::any();
    if c {
        mem::swap(&mut b1, &mut b2);
    }
    assert!(*b1 == 1);
}

// --- over-correction guards: a NON-pointer move must stay exact ------------

#[kani::proof]
fn mem_replace_plain_value_exact_safe() {
    let mut x = 1u8;
    let old = mem::replace(&mut x, 5u8);
    assert!(old == 1 && x == 5);
}

#[kani::proof]
fn mem_replace_plain_value_must_fail() {
    let mut x = 1u8;
    let old = mem::replace(&mut x, 5u8);
    assert!(old == 5 && x == 1);
}

#[kani::proof]
fn option_take_plain_value_exact_safe() {
    let mut o: Option<u8> = Some(3);
    let taken = o.take();
    assert!(taken == Some(3) && o.is_none());
}
