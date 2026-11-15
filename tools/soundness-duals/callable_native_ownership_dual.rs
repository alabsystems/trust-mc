// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

fn increment(value: &mut i32) {
    *value = value.wrapping_add(1);
}
fn twice(mut function: Box<dyn FnMut(&mut i32)>, value: &mut i32) {
    function(value);
    function(value);
}
fn looped(mut function: Box<dyn FnMut(&mut i32)>, value: &mut i32) {
    let mut remaining = 2u8;
    while remaining != 0 {
        function(value);
        remaining = remaining.wrapping_sub(1);
    }
}
// This is a user body, despite its name and a real Box receiver argument.
fn call_mut(mut function: Box<dyn FnMut(&mut i32)>, value: &mut i32) {
    *value = 7;
    function(value);
}

#[kani::proof]
fn native_fn_owner_borrow_safe() {
    let mut value = 1;
    let function: Box<dyn Fn(&mut i32)> = Box::new(&increment);
    function(&mut value);
    assert!(value == 2);
}
#[kani::proof]
fn native_fn_owner_borrow_bug() {
    let mut value = 1;
    let function: Box<dyn Fn(&mut i32)> = Box::new(&increment);
    function(&mut value);
    assert!(value == 3);
}
#[kani::proof]
fn repeated_native_fnmut_borrow_safe() {
    let mut value = 1;
    twice(Box::new(&increment), &mut value);
    assert!(value == 3);
}
#[kani::proof]
fn repeated_native_fnmut_borrow_bug() {
    let mut value = 1;
    twice(Box::new(&increment), &mut value);
    assert!(value == 2);
}
#[kani::proof]
fn loop_native_fnmut_borrow_safe() {
    let mut value = 1;
    looped(Box::new(&increment), &mut value);
    assert!(value == 3);
}
#[kani::proof]
fn loop_native_fnmut_borrow_bug() {
    let mut value = 1;
    looped(Box::new(&increment), &mut value);
    assert!(value == 2);
}
#[kani::proof]
fn user_named_call_mut_effect_safe() {
    let mut value = 1;
    call_mut(Box::new(&increment), &mut value);
    assert!(value == 8);
}
#[kani::proof]
fn user_named_call_mut_effect_bug() {
    let mut value = 1;
    call_mut(Box::new(&increment), &mut value);
    assert!(value == 2);
}

fn decrement(value: &mut i32) {
    *value = value.wrapping_sub(1);
}
#[kani::proof]
fn second_native_fnmut_origin_safe() {
    let decoy: Box<dyn FnMut(&mut i32)> = Box::new(&increment);
    core::mem::forget(decoy);
    let mut value = 1;
    twice(Box::new(&decrement), &mut value);
    assert!(value == -1);
}
#[kani::proof]
fn second_native_fnmut_origin_bug() {
    let decoy: Box<dyn FnMut(&mut i32)> = Box::new(&increment);
    core::mem::forget(decoy);
    let mut value = 1;
    twice(Box::new(&decrement), &mut value);
    assert!(value == 3);
}
