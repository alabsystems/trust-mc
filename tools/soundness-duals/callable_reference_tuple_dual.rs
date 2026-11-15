// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! RustCall reference carriers must preserve explicitly resolved referent values.
//! Expectations state Rust semantics; no frozen Kani execution is claimed.

fn call(mut function: Box<dyn FnMut(&mut i32)>, value: &mut i32) {
    function(value);
}

fn increment(value: &mut i32) {
    *value = value.wrapping_add(1);
}

#[kani::proof]
fn boxed_callable_reference_writeback_safe() {
    let mut value = 1;
    call(Box::new(&increment), &mut value);
    assert!(value == 2);
}

#[kani::proof]
fn boxed_callable_wrong_writeback_bug() {
    let mut value = 1;
    call(Box::new(&increment), &mut value);
    assert!(value == 3);
}

#[kani::proof]
fn captured_reference_predicate_safe() {
    let bound = 5u32;
    let value: u32 = kani::any_where(|value: &u32| *value < bound);
    assert!(value < bound);
}

#[kani::proof]
fn captured_reference_predicate_wrong_bound_bug() {
    let bound = 5u32;
    let value: u32 = kani::any_where(|value: &u32| *value < bound);
    assert!(value >= bound);
}
