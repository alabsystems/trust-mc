// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// What `#[kani::should_panic]` accepts as a panic — one rule, both lanes, both
// routes.
//
// Every `_holds` body below REALLY panics when the program runs (checked
// natively on the frozen nightly with debug assertions on): an explicit
// `panic!`, a failing `assert!`, `Option::unwrap` on `None`, an out-of-bounds
// array index, an out-of-bounds slice index, an arithmetic overflow, a division
// by zero. Kani lowers all seven to `PropertyClass::Assertion`, so all seven
// pass there.
//
// Measured before `ay_parse::violation::class_is_rust_panic` existed (parity-1
// third review, finding 8.4): the BMC lane refused the last four —
// `VERIFICATION:- FAILED (encountered failures other than panics, which were
// unexpected)`, because `determine_failed_from_properties` counted only the
// `assertion`, `panic` and `unreachable` classes — while the CHC lane, which
// reaches the same panics through the panic ARM of the check, accepted all
// four. Two lanes, one source program, opposite verdicts, and the BMC column a
// counted Kani-parity loss.
//
// The `_refuted` twins cannot panic (an in-bounds index, a non-overflowing
// product, a non-zero divisor, an in-bounds slice) and must never be
// SUCCESSFUL: the gate must not have been widened into accepting anything.
#![allow(unused)]

#[kani::proof]
#[kani::should_panic]
fn spk_explicit_panic_holds() {
    panic!("boom");
}

#[kani::proof]
#[kani::should_panic]
fn spk_assert_holds() {
    let x: u8 = kani::any();
    kani::assume(x == 7);
    assert!(x != 7);
}

#[kani::proof]
#[kani::should_panic]
fn spk_unwrap_none_holds() {
    let o: Option<u8> = None;
    let _ = o.unwrap();
}

#[kani::proof]
#[kani::should_panic]
fn spk_array_index_holds() {
    let a = [1u8, 2, 3];
    let i: usize = kani::any();
    kani::assume(i >= 3 && i < 5);
    let _ = a[i];
}

#[kani::proof]
#[kani::should_panic]
fn spk_slice_index_holds() {
    let v: &[u8] = &[1u8, 2, 3];
    let i: usize = kani::any();
    kani::assume(i == 5);
    let _ = v[i];
}

#[kani::proof]
#[kani::should_panic]
fn spk_overflow_holds() {
    let x: u32 = kani::any();
    kani::assume(x > 70000);
    let _ = x * x;
}

#[kani::proof]
#[kani::should_panic]
fn spk_div_zero_holds() {
    let x: u32 = kani::any();
    let y: u32 = kani::any();
    kani::assume(y == 0);
    let _ = x / y;
}

#[kani::proof]
#[kani::should_panic]
fn spk_array_index_inbounds_refuted() {
    let a = [1u8, 2, 3];
    let i: usize = kani::any();
    kani::assume(i < 3);
    let _ = a[i];
}

#[kani::proof]
#[kani::should_panic]
fn spk_slice_index_inbounds_refuted() {
    let v: &[u8] = &[1u8, 2, 3];
    let i: usize = kani::any();
    kani::assume(i < 3);
    let _ = v[i];
}

#[kani::proof]
#[kani::should_panic]
fn spk_no_overflow_refuted() {
    let x: u32 = kani::any();
    kani::assume(x < 1000);
    let _ = x * x;
}

#[kani::proof]
#[kani::should_panic]
fn spk_div_nonzero_refuted() {
    let x: u32 = kani::any();
    let y: u32 = kani::any();
    kani::assume(y > 0);
    let _ = x / y;
}

// Not a should_panic harness: the same in-bounds index really is in bounds, so
// the ordinary proof still verifies. The widened rule must not disturb it.
#[kani::proof]
fn spk_nosp_array_index_holds() {
    let a = [1u8, 2, 3];
    let i: usize = kani::any();
    kani::assume(i < 3);
    assert!(a[i] >= 1);
}
