// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z mem-predicates
// Model-check only: the negative assertions are deliberate soundness controls.

extern crate kani;

#[inline(never)]
fn heap_pointer() -> *mut u32 {
    let owner = Box::new(17u32);
    Box::into_raw(owner)
}

#[kani::proof]
pub fn heap_pointer_remains_readable_after_holder_exit() {
    let pointer = heap_pointer();
    assert!(kani::mem::can_dereference(pointer));
}

#[kani::proof]
pub fn heap_pointer_cannot_be_declared_dead_after_holder_exit() {
    let pointer = heap_pointer();
    assert!(!kani::mem::can_dereference(pointer));
}

#[kani::proof]
pub fn heap_pointer_retains_its_allocation_after_holder_exit() {
    let pointer = heap_pointer();
    assert!(kani::mem::same_allocation(pointer, pointer));
}

#[kani::proof]
pub fn heap_pointer_cannot_lose_its_allocation_with_holder_exit() {
    let pointer = heap_pointer();
    assert!(!kani::mem::same_allocation(pointer, pointer));
}

#[kani::proof]
pub fn heap_value_survives_pointer_holder_exit() {
    let pointer = heap_pointer();
    assert_eq!(unsafe { *pointer }, 17);
}

#[kani::proof]
pub fn heap_value_is_not_replaced_on_pointer_holder_exit() {
    let pointer = heap_pointer();
    assert_eq!(unsafe { *pointer }, 18);
}
