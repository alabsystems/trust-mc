// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

#[repr(align(32))]
struct Mutex(u8);

#[kani::proof]
pub fn empty_u8_address_safe() {
    let values = Vec::<u8>::new();
    assert!(values.as_ptr().addr() == 1);
}

#[kani::proof]
pub fn empty_u8_address_bug() {
    let values = Vec::<u8>::new();
    assert!(values.as_ptr().addr() == 2);
}

#[kani::proof]
pub fn empty_u64_address_safe() {
    let values = Vec::<u64>::new();
    assert!(values.as_ptr().addr() == 8);
}

#[kani::proof]
pub fn empty_u64_address_bug() {
    let values = Vec::<u64>::new();
    assert!(values.as_ptr().addr() == 1);
}

#[kani::proof]
pub fn empty_actual_layout_safe() {
    let values = Vec::<Mutex>::new();
    assert!(values.as_ptr().addr() == 32);
}

#[kani::proof]
pub fn empty_actual_layout_bug() {
    let values = Vec::<Mutex>::new();
    assert!(values.as_ptr().addr() == 1);
}

#[kani::proof]
pub fn zero_capacity_address_safe() {
    let values = Vec::<u64>::with_capacity(0);
    assert!(values.as_ptr().addr() == 8);
}

#[kani::proof]
pub fn zero_capacity_dereference_bug() {
    let values = Vec::<u64>::with_capacity(0);
    assert!(unsafe { *values.as_ptr() } == 0);
}

#[kani::proof]
pub fn empty_dereference_bug() {
    let values = Vec::<u64>::new();
    assert!(unsafe { *values.as_ptr() } == 0);
}
