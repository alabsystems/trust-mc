// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z valid-value-checks -Z mem-predicates

#[kani::proof]
fn valid_bool_bytes_safe() {
    let value = [0u8, 1u8];
    assert!(kani::mem::can_dereference(&value as *const _ as *const [bool; 2]));
}

#[kani::proof]
fn invalid_bool_bytes_bug() {
    let value = [0u8, 2u8];
    assert!(kani::mem::can_dereference(&value as *const _ as *const [bool; 2]));
}

#[kani::proof]
fn wide_bool_bytes_safe() {
    let value = [0x0200u16];
    assert!(!kani::mem::can_dereference(&value as *const _ as *const [bool; 2]));
}

#[kani::proof]
fn wide_bool_bytes_bug() {
    let value = [0x0100u16];
    assert!(!kani::mem::can_dereference(&value as *const _ as *const [bool; 2]));
}

#[repr(u8)]
enum CompactByte {
    Invalid = 2,
}

#[kani::proof]
fn compact_bool_byte_refusal() {
    let value = CompactByte::Invalid;
    assert!(!kani::mem::can_dereference(&value as *const _ as *const bool));
}

// A name-based logical wrapper model must not authenticate physical bytes.
#[repr(C)]
struct Mutex<T> {
    tag: u8,
    value: T,
}

#[kani::proof]
fn bool_wrapper_invalid_safe() {
    let values = [Mutex { tag: 2u8, value: 0u8 }];
    assert!(!kani::mem::can_dereference(&values as *const _ as *const bool));
}
#[kani::proof]
fn bool_wrapper_invalid_bug() {
    let values = [Mutex { tag: 2u8, value: 0u8 }];
    assert!(kani::mem::can_dereference(&values as *const _ as *const bool));
}
#[kani::proof]
fn bool_wrapper_valid_safe() {
    let values = [Mutex { tag: 0u8, value: 2u8 }];
    assert!(kani::mem::can_dereference(&values as *const _ as *const bool));
}
#[kani::proof]
fn bool_wrapper_valid_bug() {
    let values = [Mutex { tag: 0u8, value: 2u8 }];
    assert!(!kani::mem::can_dereference(&values as *const _ as *const bool));
}

// Authenticating the library type preserves its logical model. It does not
// prove that the synchronization state has the payload's byte representation.
#[kani::proof]
fn native_wrapper_true_refusal() {
    let values = [std::sync::Mutex::new(2u8)];
    assert!(kani::mem::can_dereference(&values as *const _ as *const bool));
}

#[kani::proof]
fn native_wrapper_false_refusal() {
    let values = [std::sync::Mutex::new(2u8)];
    assert!(!kani::mem::can_dereference(&values as *const _ as *const bool));
}
