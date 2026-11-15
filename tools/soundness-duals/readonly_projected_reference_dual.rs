// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

#![allow(dead_code)]
struct Holder<'a> {
    value: &'a u64,
}
fn apply<F: FnOnce(&u64) -> bool>(value: &u64, predicate: F) -> bool {
    predicate(value)
}
fn by_value(value: Holder<'_>) -> bool {
    let reference = &*value.value;
    apply(reference, |v| *v == 11)
}
fn by_borrow(value: &Holder<'_>) -> bool {
    let reference = &*value.value;
    apply(reference, |v| *v == 11)
}
fn by_tuple(value: (&u64,)) -> bool {
    let reference = &*value.0;
    apply(reference, |v| *v == 11)
}
fn by_capture(value: &u64) -> bool {
    let closure = move || {
        let reference = &*value;
        apply(reference, |v| *v == 11)
    };
    closure()
}
#[kani::proof]
pub fn value_safe() {
    let value = 11u64;
    assert!(by_value(Holder { value: &value }));
}
#[kani::proof]
pub fn value_bug() {
    let value = 11u64;
    assert!(!by_value(Holder { value: &value }));
}
#[kani::proof]
pub fn borrow_safe() {
    let value = 11u64;
    assert!(by_borrow(&Holder { value: &value }));
}
#[kani::proof]
pub fn borrow_bug() {
    let value = 11u64;
    assert!(!by_borrow(&Holder { value: &value }));
}
#[kani::proof]
pub fn tuple_safe() {
    let value = 11u64;
    assert!(by_tuple((&value,)));
}
#[kani::proof]
pub fn tuple_bug() {
    let value = 11u64;
    assert!(!by_tuple((&value,)));
}
#[kani::proof]
pub fn capture_safe() {
    let value = 11u64;
    assert!(by_capture(&value));
}
#[kani::proof]
pub fn capture_bug() {
    let value = 11u64;
    assert!(!by_capture(&value));
}
