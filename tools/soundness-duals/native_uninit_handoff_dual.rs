// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

#![feature(liballoc_internals)]

// These bodies are defined: dropping MaybeUninit never reads/drops its T.
#[repr(align(64))]
struct Aligned(u8);

#[kani::proof]
fn native_array_rewrite_into_vec_safe() {
    let mut boxed = Box::<[u32; 3]>::new_uninit();
    boxed.write([1, 2, 3]);
    boxed.write([7, 9, 8]);
    let values = std::boxed::box_assume_init_into_vec_unsafe::<u32, 3>(boxed);
    assert!(values[1] == 9);
}
#[kani::proof]
fn native_array_rewrite_into_vec_bug() {
    let mut boxed = Box::<[u32; 3]>::new_uninit();
    boxed.write([1, 2, 3]);
    boxed.write([7, 9, 8]);
    let values = std::boxed::box_assume_init_into_vec_unsafe::<u32, 3>(boxed);
    assert!(values[1] == 2);
}

#[kani::proof]
fn native_scalar_write_then_assume_init_safe() {
    let mut boxed = Box::<u32>::new_uninit();
    boxed.write(17);
    let initialized = unsafe { boxed.assume_init() };
    assert!(*initialized == 17);
}
#[kani::proof]
fn native_scalar_write_then_assume_init_bug() {
    let mut boxed = Box::<u32>::new_uninit();
    boxed.write(17);
    let initialized = unsafe { boxed.assume_init() };
    assert!(*initialized == 18);
}
#[kani::proof]
fn native_array_write_then_assume_init_safe() {
    let mut boxed = Box::<[u32; 3]>::new_uninit();
    boxed.write([1, 2, 3]);
    let initialized = unsafe { boxed.assume_init() };
    assert!(initialized[1] == 2);
}
#[kani::proof]
fn native_array_write_then_assume_init_bug() {
    let mut boxed = Box::<[u32; 3]>::new_uninit();
    boxed.write([1, 2, 3]);
    let initialized = unsafe { boxed.assume_init() };
    assert!(initialized[1] == 9);
}

#[kani::proof]
fn uninit_scalar_drop_successor_safe() {
    let value = Box::<u128>::new_uninit();
    let mut marker = 5u32;
    drop(value);
    marker += 2;
    assert!(marker == 7);
}
#[kani::proof]
fn uninit_scalar_drop_successor_bug() {
    let value = Box::<u128>::new_uninit();
    let mut marker = 5u32;
    drop(value);
    marker += 2;
    assert!(marker == 8);
}
#[kani::proof]
fn uninit_array_drop_successor_safe() {
    let value = Box::<[bool; 3]>::new_uninit();
    let mut marker = 5u32;
    drop(value);
    marker += 2;
    assert!(marker == 7);
}
#[kani::proof]
fn uninit_array_drop_successor_bug() {
    let value = Box::<[bool; 3]>::new_uninit();
    let mut marker = 5u32;
    drop(value);
    marker += 2;
    assert!(marker == 8);
}
#[kani::proof]
fn uninit_overaligned_drop_successor_safe() {
    let value = Box::<Aligned>::new_uninit();
    let mut marker = 5u32;
    drop(value);
    marker += 2;
    assert!(marker == 7);
}
#[kani::proof]
fn uninit_overaligned_drop_successor_bug() {
    let value = Box::<Aligned>::new_uninit();
    let mut marker = 5u32;
    drop(value);
    marker += 2;
    assert!(marker == 8);
}
#[kani::proof]
fn vec_initialization_observes_store_time_source_safe() {
    let mut source = 1u32;
    let first = vec![source, 2, 3];
    source = 9;
    let later = vec![source, 4, 5];
    assert!(first[0] == 1 && later[0] == 9);
}
#[kani::proof]
fn vec_initialization_observes_store_time_source_bug() {
    let mut source = 1u32;
    let first = vec![source, 2, 3];
    source = 9;
    let later = vec![source, 4, 5];
    assert!(first[0] == 9 && later[0] == 9);
}
#[kani::proof]
fn uninit_drop_before_typed_box_safe() {
    let uninit = Box::<[u8; 2]>::new_uninit();
    drop(uninit);
    let typed = Box::new(9u32);
    assert!(*typed == 9);
}
#[kani::proof]
fn uninit_drop_before_typed_box_bug() {
    let uninit = Box::<[u8; 2]>::new_uninit();
    drop(uninit);
    let typed = Box::new(9u32);
    assert!(*typed == 8);
}

#[kani::proof]
fn native_bool_write_then_assume_init_safe() {
    let mut boxed = Box::<bool>::new_uninit();
    boxed.write(true);
    let value = unsafe { boxed.assume_init() };
    assert!(*value);
}
#[kani::proof]
fn native_bool_write_then_assume_init_bug() {
    let mut boxed = Box::<bool>::new_uninit();
    boxed.write(true);
    let value = unsafe { boxed.assume_init() };
    assert!(!*value);
}
#[kani::proof]
fn native_bool_array_into_vec_safe() {
    let mut boxed = Box::<[bool; 3]>::new_uninit();
    boxed.write([false, true, false]);
    let values = std::boxed::box_assume_init_into_vec_unsafe::<bool, 3>(boxed);
    assert!(!values[0] && values[1] && !values[2]);
}
#[kani::proof]
fn native_bool_array_into_vec_bug() {
    let mut boxed = Box::<[bool; 3]>::new_uninit();
    boxed.write([false, true, false]);
    let values = std::boxed::box_assume_init_into_vec_unsafe::<bool, 3>(boxed);
    assert!(values[0]);
}
