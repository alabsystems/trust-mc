// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// NEGATIVE PACK: a pointer that travels through MEMORY — swapped inside a
// carrier, or stored into an aggregate slot — and is then written through.
//
// Both lanes keep their points-at edges from the BORROWS in the body, so a
// pointer that moves without a borrow leaves them stale. Two families, both
// measured on m3/soundness-fixes-2 at 547f714bb (fourth adversarial review,
// 2026-09-14, defects M2/D3 and M3/D4):
//
//   * `let mut a: Option<*mut u8> = Some(&mut x); let mut b = Some(&mut y);
//      mem::swap(&mut a, &mut b); *a.unwrap() = 9; assert!(y == 2)` was
//     SUCCESSFUL with `[AY:PROOF_QUALIFIERS:clean]` in BOTH lanes and its safe
//     twin FAILED [AY:CTREX_CAT:Genuine]. `is_pointer_like_ty` answered `false`
//     for the CARRIER, so nothing was exchanged and nothing was recorded.
//   * `struct H { p: *mut u8 } let mut h = H { p: &mut x }; h.p = &mut y;
//      *h.p = 9; assert!(y == 2)` verified SUCCESSFUL in CHC with ZERO recorded
//     drop reasons — the rebind guard covered a store THROUGH a dereference
//     only, and a store INTO an aggregate slot is a different handler.
//
// Ground truth for every harness here was compiled and run natively on the
// frozen nightly-2025-12-03 rustc.
//
// Oracle (per harness):
//   *_must_fail   -> VERIFICATION:- FAILED; never SUCCESSFUL
//   *_safe        -> never a Genuine counterexample

use std::mem;

struct H {
    p: *mut u8,
}

struct Pair {
    a: *mut u8,
    b: *mut u8,
}

#[kani::proof]
fn swap_options_of_ptrs_must_fail() {
    let mut x = 1u8;
    let mut y = 2u8;
    let mut a: Option<*mut u8> = Some(&mut x);
    let mut b: Option<*mut u8> = Some(&mut y);
    mem::swap(&mut a, &mut b);
    unsafe {
        *a.unwrap() = 9;
    }
    assert!(y == 2); // truth: 9
}

#[kani::proof]
fn swap_options_of_ptrs_safe() {
    let mut x = 1u8;
    let mut y = 2u8;
    let mut a: Option<*mut u8> = Some(&mut x);
    let mut b: Option<*mut u8> = Some(&mut y);
    mem::swap(&mut a, &mut b);
    unsafe {
        *a.unwrap() = 9;
    }
    assert!(x == 1 && y == 9);
}

#[kani::proof]
fn swap_tuples_of_ptrs_must_fail() {
    let mut x = 1u8;
    let mut y = 2u8;
    let mut a: (*mut u8, u8) = (&mut x, 0);
    let mut b: (*mut u8, u8) = (&mut y, 0);
    mem::swap(&mut a, &mut b);
    unsafe {
        *a.0 = 9;
    }
    assert!(y == 2); // truth: 9
}

#[kani::proof]
fn swap_tuples_of_ptrs_safe() {
    let mut x = 1u8;
    let mut y = 2u8;
    let mut a: (*mut u8, u8) = (&mut x, 0);
    let mut b: (*mut u8, u8) = (&mut y, 0);
    mem::swap(&mut a, &mut b);
    unsafe {
        *a.0 = 9;
    }
    assert!(x == 1 && y == 9);
}

#[kani::proof]
fn swap_arrays_of_ptrs_must_fail() {
    let mut x = 1u8;
    let mut y = 2u8;
    let mut a: [*mut u8; 1] = [&mut x];
    let mut b: [*mut u8; 1] = [&mut y];
    mem::swap(&mut a, &mut b);
    unsafe {
        *a[0] = 9;
    }
    assert!(y == 2); // truth: 9
}

#[kani::proof]
fn swap_arrays_of_ptrs_safe() {
    let mut x = 1u8;
    let mut y = 2u8;
    let mut a: [*mut u8; 1] = [&mut x];
    let mut b: [*mut u8; 1] = [&mut y];
    mem::swap(&mut a, &mut b);
    unsafe {
        *a[0] = 9;
    }
    assert!(x == 1 && y == 9);
}

#[kani::proof]
fn swap_struct_fields_of_ptrs_must_fail() {
    let mut x = 1u8;
    let mut y = 2u8;
    let mut h = Pair { a: &mut x, b: &mut y };
    mem::swap(&mut h.a, &mut h.b);
    unsafe {
        *h.a = 9;
    }
    assert!(y == 2); // truth: 9
}

#[kani::proof]
fn swap_struct_fields_of_ptrs_safe() {
    let mut x = 1u8;
    let mut y = 2u8;
    let mut h = Pair { a: &mut x, b: &mut y };
    mem::swap(&mut h.a, &mut h.b);
    unsafe {
        *h.a = 9;
    }
    assert!(x == 1 && y == 9);
}

#[kani::proof]
fn ptr_through_struct_field_must_fail() {
    let mut x = 1u8;
    let mut y = 2u8;
    let mut h = H { p: &mut x };
    h.p = &mut y;
    unsafe {
        *h.p = 9;
    }
    assert!(y == 2); // truth: 9
}

#[kani::proof]
fn ptr_through_struct_field_safe() {
    let mut x = 1u8;
    let mut y = 2u8;
    let mut h = H { p: &mut x };
    h.p = &mut y;
    unsafe {
        *h.p = 9;
    }
    assert!(x == 1 && y == 9);
}

#[kani::proof]
fn ptr_through_tuple_must_fail() {
    let mut x = 1u8;
    let mut y = 2u8;
    let mut t: (*mut u8, u8) = (&mut x, 0);
    t.0 = &mut y;
    unsafe {
        *t.0 = 9;
    }
    assert!(y == 2); // truth: 9
}

#[kani::proof]
fn ptr_through_tuple_safe() {
    let mut x = 1u8;
    let mut y = 2u8;
    let mut t: (*mut u8, u8) = (&mut x, 0);
    t.0 = &mut y;
    unsafe {
        *t.0 = 9;
    }
    assert!(x == 1 && y == 9);
}

#[kani::proof]
fn ptr_through_deref_field_must_fail() {
    let mut x = 1u8;
    let mut y = 2u8;
    let mut h = H { p: &mut x };
    {
        let r = &mut h;
        (*r).p = &mut y;
    }
    unsafe {
        *h.p = 9;
    }
    assert!(y == 2); // truth: 9
}

#[kani::proof]
fn ptr_through_deref_field_safe() {
    let mut x = 1u8;
    let mut y = 2u8;
    let mut h = H { p: &mut x };
    {
        let r = &mut h;
        (*r).p = &mut y;
    }
    unsafe {
        *h.p = 9;
    }
    assert!(x == 1 && y == 9);
}

// --- controls --------------------------------------------------------------

#[kani::proof]
fn swap_values_safe() {
    let mut x = 1u8;
    let mut y = 2u8;
    mem::swap(&mut x, &mut y);
    assert!(x == 2 && y == 1);
}

#[kani::proof]
fn ptr_in_field_no_rebind_safe() {
    let mut x = 1u8;
    let h = H { p: &mut x };
    unsafe {
        *h.p = 9;
    }
    assert!(x == 9);
}
