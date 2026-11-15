// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

#[kani::proof]
fn native_vec_literal_len_safe() {
    let values = vec![1u32, 2, 3];
    assert!(values.len() == 3);
}

#[kani::proof]
fn native_vec_literal_len_bug() {
    let values = vec![1u32, 2, 3];
    assert!(values.len() == 4);
}

#[kani::proof]
fn native_vec_literal_element_safe() {
    let values = vec![1u32, 2, 3];
    assert!(values[1] == 2);
}

#[kani::proof]
fn native_vec_literal_element_bug() {
    let values = vec![1u32, 2, 3];
    assert!(values[1] == 3);
}

#[kani::proof]
fn native_vec_literal_updated_element_safe() {
    let mut values = vec![1u32, 2, 3];
    values[1] = 9;
    assert!(values[1] == 9);
}

#[kani::proof]
fn native_vec_literal_updated_element_bug() {
    let mut values = vec![1u32, 2, 3];
    values[1] = 9;
    assert!(values[1] == 2);
}
