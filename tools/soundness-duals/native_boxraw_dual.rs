// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Box heap read/write controls for the native BoxRaw carrier. Expectations
//! state Rust semantics; no frozen Kani oracle execution is claimed.

#[kani::proof]
fn boxed_scalar_read_safe() {
    let value = Box::new(7u32);
    assert!(*value == 7);
}

#[kani::proof]
fn boxed_scalar_wrong_value_bug() {
    let value = Box::new(7u32);
    assert!(*value == 0);
}

#[kani::proof]
fn boxed_array_element_read_safe() {
    let value = Box::new([11u32, 22, 33, 44]);
    assert!(value[2] == 33);
}

#[kani::proof]
fn boxed_array_wrong_element_bug() {
    let value = Box::new([11u32, 22, 33, 44]);
    assert!(value[2] == 34);
}

#[kani::proof]
fn boxed_symbolic_element_write_safe() {
    let index: usize = kani::any();
    kani::assume(index < 4);
    let mut value = Box::new([11u32, 22, 33, 44]);
    value[index] = 87;
    assert!(value[index] == 87);
}

#[kani::proof]
fn boxed_symbolic_element_wrong_value_bug() {
    let index: usize = kani::any();
    kani::assume(index < 4);
    let mut value = Box::new([11u32, 22, 33, 44]);
    value[index] = 87;
    assert!(value[index] == 88);
}

#[repr(transparent)]
struct BoxRaw<T> {
    pointer: u64,
    marker: core::marker::PhantomData<T>,
}

#[kani::proof]
fn user_boxraw_keeps_its_actual_fields_safe() {
    let value = BoxRaw::<u8> { pointer: 42, marker: core::marker::PhantomData };
    assert!(value.pointer == 42);
}

#[kani::proof]
fn user_boxraw_wrong_field_bug() {
    let value = BoxRaw::<u8> { pointer: 42, marker: core::marker::PhantomData };
    assert!(value.pointer == 0);
}
