// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Execute custom equality and adapter/comparator bodies, including captures.
//! Expectations state Rust behavior, without claiming a frozen-Kani run.

#![feature(iter_order_by)]

#[derive(Clone, Copy)]
struct Reject;
impl PartialEq for Reject {
    fn eq(&self, _: &Self) -> bool {
        false
    }
}

#[kani::proof]
fn custom_equality_rejects_same_storage_bug() {
    let values = [Reject];
    assert!(values.iter().eq(values.iter()));
}

#[kani::proof]
fn mapped_capture_equal_safe() {
    let values = [1u8, 2];
    let increment = 3u8;
    assert!(values.iter().map(|x| x.wrapping_add(increment)).eq([4u8, 5]));
}

#[kani::proof]
fn mapped_capture_different_bug() {
    let values = [1u8, 2];
    let increment = 3u8;
    assert!(values.iter().map(|x| x.wrapping_add(increment)).eq([4u8, 6]));
}

#[kani::proof]
fn zero_take_is_empty_safe() {
    let values = [1u8, 2];
    assert!(values.iter().take(0).eq([].iter()));
}

#[kani::proof]
fn comparator_controls_order_safe() {
    let left = [1u8];
    let right = [9u8];
    assert!(left.iter().cmp_by(right.iter(), |_, _| core::cmp::Ordering::Equal).is_eq());
}

#[kani::proof]
fn captured_comparator_rejects_same_storage_bug() {
    let values = [1u8];
    let order = core::cmp::Ordering::Less;
    assert!(values.iter().cmp_by(values.iter(), |_, _| order).is_eq());
}
