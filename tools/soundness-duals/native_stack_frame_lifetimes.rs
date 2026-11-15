// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z mem-predicates
// Model-check only: the deliberately dangling pointers are never run natively.

extern crate kani;

#[inline(never)]
fn local_pointer() -> *const u32 {
    let value = 17u32;
    &value as *const u32
}

#[inline(never)]
fn caller_reference(value: &u32) -> &u32 {
    value
}

#[inline(never)]
fn read_value(value: &u32) -> u32 {
    *value
}

#[kani::proof]
pub fn returned_local_storage_is_dead() {
    let pointer = local_pointer();
    assert!(!kani::mem::can_dereference(pointer));
}

#[kani::proof]
pub fn returned_local_storage_cannot_be_read() {
    let pointer = local_pointer();
    assert!(kani::mem::can_dereference(pointer));
}

#[kani::proof]
pub fn returned_caller_reference_stays_live() {
    let value = 17u32;
    let reference = caller_reference(&value);
    assert!(kani::mem::can_dereference(reference));
    assert_eq!(*reference, 17);
}

#[kani::proof]
pub fn projected_return_preserves_value() {
    let mut pair = (0u32, 17u32);
    pair.0 = read_value(&pair.1);
    assert_eq!(pair.0, 17);
}

#[inline(never)]
fn repeated_frame(previous: *const u32, incorrectly_accept_live: bool) -> *const u32 {
    let value = 17u32;
    let current = &value as *const u32;
    if !previous.is_null() {
        if incorrectly_accept_live {
            assert!(kani::mem::can_dereference(previous));
        } else {
            assert!(!kani::mem::can_dereference(previous));
        }
    }
    current
}

#[kani::proof]
pub fn repeated_frame_old_pointer_stays_dead() {
    let mut previous = core::ptr::null();
    for _ in 0..2 {
        previous = repeated_frame(previous, false);
    }
}

#[kani::proof]
pub fn repeated_frame_old_pointer_cannot_be_revived() {
    let mut previous = core::ptr::null();
    for _ in 0..2 {
        previous = repeated_frame(previous, true);
    }
}

#[kani::proof]
pub fn expired_frame_has_no_live_allocation() {
    let pointer = local_pointer();
    assert!(!kani::mem::same_allocation(pointer, pointer));
}

#[kani::proof]
pub fn returned_local_raw_dereference_fails() {
    let pointer = local_pointer();
    assert_eq!(unsafe { *pointer }, 17);
}
