// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// NEGATIVE PACK: a 128-bit value boxed with Box::new is a payload, not a Layout.
//
// Found while adding negative/branch_memory_stores.rs (2026-09-12). The CHC
// allocation model decodes a 128-bit operand as a packed `Layout` before it
// checks for `Box::new`, whose operand is the boxed value. `Box::new(0u128)`
// therefore allocated an object of size 0 and alignment 0, and the allocator's
// `size != 0` and `align != 0` preconditions failed on every path: even
// `drop(Box::new(0u128))` FAILED with CTREX_CAT:Genuine in the CHC lane on
// main 31793ccc3 and on the re-land bundle. Boxed u64 values and (u64, u64)
// pairs were not affected. In BMC a read of such a payload through
// `Box::into_raw` was size-checked against the 8-byte pointer local inside
// `into_raw` (an unresolved `_deref` alias), so `box_i128_read_safe` and
// `box_wide_u128_read_safe` failed with CTREX_CAT:Genuine there too.
//
// Oracle (per harness):
//   *_must_fail   -> VERIFICATION:- FAILED (assertion); never SUCCESSFUL
//   *_safe        -> never a Genuine counterexample

#[kani::proof]
fn box_u128_drop_safe() {
    let b = Box::new(0u128);
    drop(b);
}

#[kani::proof]
fn box_u128_read_safe() {
    let b = Box::new(5u128);
    assert!(*b == 5);
}

#[kani::proof]
fn box_u128_read_must_fail() {
    let b = Box::new(5u128);
    assert!(*b == 6);
}

#[kani::proof]
fn box_wide_u128_read_safe() {
    let p = Box::into_raw(Box::new(1u128 << 100));
    unsafe { assert!(*p == 1 << 100) }
}

#[kani::proof]
fn box_wide_u128_read_must_fail() {
    let p = Box::into_raw(Box::new(1u128 << 100));
    unsafe { assert!(*p == 1 << 99) }
}

#[kani::proof]
fn box_i128_read_safe() {
    let p = Box::into_raw(Box::new(-3i128));
    unsafe { assert!(*p == -3) }
}

#[kani::proof]
fn box_i128_read_must_fail() {
    let p = Box::into_raw(Box::new(-3i128));
    unsafe { assert!(*p == 3) }
}

#[kani::proof]
fn box_u128_store_safe() {
    let p = Box::into_raw(Box::new(0u128));
    unsafe {
        *p = 1 << 70;
        assert!(*p == 1 << 70);
    }
}

#[kani::proof]
fn box_u128_store_must_fail() {
    let p = Box::into_raw(Box::new(0u128));
    unsafe {
        *p = 1 << 70;
        assert!(*p == 0);
    }
}

#[kani::proof]
fn box_u128_field_safe() {
    let b = Box::new((7u8, 1u128 << 90));
    assert!(b.0 == 7 && b.1 == 1 << 90);
}

#[kani::proof]
fn box_u128_field_must_fail() {
    let b = Box::new((7u8, 1u128 << 90));
    assert!(b.1 == 1 << 89);
}

#[kani::proof]
fn box_nondet_u128_roundtrip_safe() {
    let v: u128 = kani::any();
    let b = Box::new(v);
    assert!(*b == v);
}

#[kani::proof]
fn box_nondet_u128_roundtrip_must_fail() {
    let v: u128 = kani::any();
    let b = Box::new(v);
    assert!(*b != v);
}

#[kani::proof]
fn rc_u128_read_safe() {
    let r = std::rc::Rc::new(1u128 << 80);
    assert!(*r == 1 << 80);
}

#[kani::proof]
fn rc_u128_read_must_fail() {
    let r = std::rc::Rc::new(1u128 << 80);
    assert!(*r == 1 << 81);
}
