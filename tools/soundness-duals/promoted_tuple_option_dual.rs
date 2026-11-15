// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Promoted tuple/Option values must use actual Rust layouts and complete typed cells.
//! Expectations state Rust semantics; no frozen-Kani execution is claimed.

#[kani::proof]
fn tuple_some_payload_safe() {
    let value: usize = kani::any();
    kani::assume(value == 3);
    assert!((1usize, Some(value)) == (1usize, Some(3usize)));
}

#[kani::proof]
fn tuple_some_wrong_payload_bug() {
    let value: usize = kani::any();
    kani::assume(value == 3);
    assert!((1usize, Some(value)) == (1usize, Some(4usize)));
}

#[kani::proof]
fn tuple_none_safe() {
    let present: bool = kani::any();
    kani::assume(!present);
    let value = if present { Some(3usize) } else { None };
    assert!((7usize, value) == (7usize, None::<usize>));
}

#[kani::proof]
fn tuple_none_is_not_some_bug() {
    let present: bool = kani::any();
    kani::assume(!present);
    let value = if present { Some(3usize) } else { None };
    assert!((7usize, value) == (7usize, Some(0usize)));
}

#[kani::proof]
fn nested_tuple_option_safe() {
    let value: u16 = kani::any();
    kani::assume(value == 257);
    assert!((true, (5u8, Some((value, false)))) == (true, (5u8, Some((257u16, false)))));
}

#[kani::proof]
fn nested_tuple_option_wrong_payload_bug() {
    let value: u16 = kani::any();
    kani::assume(value == 257);
    assert!((true, (5u8, Some((value, false)))) == (true, (5u8, Some((258u16, false)))));
}

#[kani::proof]
fn joined_tuple_references_keep_complete_memory_values_safe() {
    let choose: bool = kani::any();
    let value = if choose { &(1usize, Some(3usize)) } else { &(1usize, Some(4usize)) };
    assert!(value.0 == 1);
    assert!(value.1 == Some(if choose { 3 } else { 4 }));
}

#[kani::proof]
fn joined_tuple_references_do_not_invent_payload_bug() {
    let choose: bool = kani::any();
    let value = if choose { &(1usize, Some(3usize)) } else { &(1usize, Some(4usize)) };
    assert!(value.1 == Some(5));
}

// This byte is evaluated by the admitted compiler. The raw read must observe
// its native niche value, independently of the Option typed-memory encoding.
const NATIVE_NONE_BOOL_BYTE: u8 = unsafe { core::mem::transmute(None::<bool>) };
const RAW_NONE_BOOL: *const u8 = &None::<bool> as *const Option<bool> as *const u8;

#[kani::proof]
fn compound_none_raw_byte_uses_native_niche_safe() {
    let value = &(9u8, None::<bool>);
    assert!(value.1.is_none());
    let byte = unsafe { core::ptr::addr_of!(value.1).cast::<u8>().read() };
    assert!(byte == NATIVE_NONE_BOOL_BYTE);
}

#[kani::proof]
fn compound_none_raw_byte_is_not_typed_zero_bug() {
    let value = &(9u8, None::<bool>);
    assert!(value.1.is_none());
    let byte = unsafe { core::ptr::addr_of!(value.1).cast::<u8>().read() };
    assert!(byte == 0);
}

#[kani::proof]
fn nested_compound_none_raw_byte_uses_native_niche_safe() {
    let value = &(123u64, (9u8, None::<bool>));
    assert!(matches!(value.1.1, None));
    let byte = unsafe { core::ptr::addr_of!(value.1.1).cast::<u8>().read() };
    assert!(byte == NATIVE_NONE_BOOL_BYTE);
}

#[kani::proof]
fn nested_compound_none_raw_byte_is_not_typed_zero_bug() {
    let value = &(123u64, (9u8, None::<bool>));
    assert!(matches!(value.1.1, None));
    let byte = unsafe { core::ptr::addr_of!(value.1.1).cast::<u8>().read() };
    assert!(byte == 0);
}

#[kani::proof]
fn direct_none_raw_constant_uses_native_niche_safe() {
    let byte = unsafe { RAW_NONE_BOOL.read() };
    assert!(byte == NATIVE_NONE_BOOL_BYTE);
}

#[kani::proof]
fn direct_none_raw_constant_is_not_typed_zero_bug() {
    let byte = unsafe { RAW_NONE_BOOL.read() };
    assert!(byte == 0);
}
