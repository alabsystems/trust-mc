// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// COMPILER INPUT ONLY. Includes undefined behavior; NEVER execute natively.

#![feature(liballoc_internals, maybe_uninit_array_assume_init, maybe_uninit_as_bytes)]
pub fn missing_initialization() {
    let boxed = Box::<[bool; 2]>::new_uninit();
    let values = std::boxed::box_assume_init_into_vec_unsafe::<bool, 2>(boxed);
    assert!(values.len() == 2);
}
pub fn direct_missing_initialization() {
    let boxed = Box::<bool>::new_uninit();
    let value = unsafe { boxed.assume_init() };
    assert!(*value);
}
pub fn poison_rhs_initialization() {
    let invalid = unsafe { core::mem::MaybeUninit::<bool>::uninit().assume_init() };
    let values = vec![invalid, true];
    assert!(values.len() == 2);
}
pub fn poisoned_native_write() {
    let invalid = unsafe { core::mem::MaybeUninit::<bool>::uninit().assume_init() };
    let mut boxed = Box::<bool>::new_uninit();
    boxed.write(invalid);
    let value = unsafe { boxed.assume_init() };
    assert!(*value);
}
pub fn byte_clobber_after_native_write() {
    let mut boxed = Box::<bool>::new_uninit();
    let value = boxed.write(true);
    unsafe {
        *(value as *mut bool as *mut u8) = 2;
    }
    let value = unsafe { boxed.assume_init() };
    assert!(*value);
}
pub fn rebound_native_owner() {
    let mut boxed = Box::<bool>::new_uninit();
    boxed.write(true);
    boxed = Box::<bool>::new_uninit();
    let value = unsafe { boxed.assume_init() };
    assert!(*value);
}
pub fn initialized_other_object() {
    let mut first = Box::<bool>::new_uninit();
    first.write(true);
    let second = Box::<bool>::new_uninit();
    let value = unsafe { second.assume_init() };
    assert!(*value);
}
pub fn conditional_initialization(branch: bool) {
    let mut boxed = Box::<bool>::new_uninit();
    if branch {
        boxed.write(true);
    }
    let value = unsafe { boxed.assume_init() };
    assert!(*value);
}
pub fn zst_without_native_address_authority() {
    let boxed = Box::<()>::new_uninit();
    let value = unsafe { boxed.assume_init() };
    assert!(*value == ());
}
pub fn missing_slice_initialization() {
    let boxed = Box::<[bool]>::new_uninit_slice(2);
    let value = unsafe { boxed.assume_init() };
    assert!(value.len() == 2);
}
pub fn repeated_allocation_generations() {
    for _ in 0..2 {
        let mut boxed = Box::<bool>::new_uninit();
        boxed.write(true);
        let value = unsafe { boxed.assume_init() };
        assert!(*value);
    }
}
pub fn borrowed_box_storage_is_not_payload() {
    let mut boxed = Box::<bool>::new_uninit();
    let owner = &mut boxed;
    owner.write(true);
    let value = unsafe { boxed.assume_init() };
    assert!(*value);
}
pub fn boxed_uninit_assume_init_read() {
    let boxed = Box::<bool>::new_uninit();
    let value = unsafe { boxed.assume_init_read() };
    assert!(value || !value);
}
pub fn boxed_uninit_assume_init_ref() {
    let boxed = Box::<bool>::new_uninit();
    let value = unsafe { boxed.assume_init_ref() };
    assert!(*value || !*value);
}
pub fn boxed_uninit_assume_init_mut() {
    let mut boxed = Box::<bool>::new_uninit();
    let value = unsafe { boxed.assume_init_mut() };
    assert!(*value || !*value);
}
pub fn boxed_uninit_assume_init_drop() {
    let mut boxed = Box::<bool>::new_uninit();
    unsafe { boxed.assume_init_drop() };
    assert!(true);
}
pub fn stack_uninit_assume_init() {
    let value = unsafe { core::mem::MaybeUninit::<bool>::uninit().assume_init() };
    assert!(value || !value);
}
pub fn array_uninit_assume_init() {
    let array = [core::mem::MaybeUninit::<bool>::uninit(); 2];
    let value = unsafe { core::mem::MaybeUninit::array_assume_init(array) };
    assert!(value[0] || !value[0]);
}
pub fn slice_uninit_assume_init_ref() {
    let array = [core::mem::MaybeUninit::<bool>::uninit(); 2];
    let value = unsafe { array[..].assume_init_ref() };
    assert!(value.len() == 2);
}
pub fn slice_uninit_assume_init_mut() {
    let mut array = [core::mem::MaybeUninit::<bool>::uninit(); 2];
    let value = unsafe { array[..].assume_init_mut() };
    assert!(value.len() == 2);
}
pub fn slice_uninit_assume_init_drop() {
    let mut array = [core::mem::MaybeUninit::<bool>::uninit(); 2];
    unsafe { array[..].assume_init_drop() };
    assert!(true);
}
#[inline(never)]
unsafe fn accessor_wrapper(value: &core::mem::MaybeUninit<bool>) -> bool {
    unsafe { value.assume_init_read() }
}
pub fn nested_uninit_accessor() {
    let value = unsafe { accessor_wrapper(&core::mem::MaybeUninit::<bool>::uninit()) };
    assert!(value || !value);
}
pub fn payload_alias_after_transfer() {
    let mut boxed = Box::<[u32; 2]>::new_uninit();
    let pointer = boxed.write([1, 2]) as *mut [u32; 2];
    let values = std::boxed::box_assume_init_into_vec_unsafe::<u32, 2>(boxed);
    unsafe {
        (*pointer)[0] = 9;
    }
    assert!(values[0] == 1);
}
pub fn raw_uninitialized_payload_read() {
    let boxed = Box::<bool>::new_uninit();
    let value = unsafe { boxed.as_ptr().read() };
    assert!(value || !value);
}
pub fn raw_partially_initialized_payload_read() {
    let mut boxed = Box::<[bool; 2]>::new_uninit();
    let pointer = boxed.as_mut_ptr() as *mut bool;
    unsafe {
        pointer.write(true);
        let value = pointer.add(1).read();
        assert!(value || !value);
    }
}
pub fn raw_uninitialized_payload_reference() {
    let boxed = Box::<bool>::new_uninit();
    let value = unsafe { &*boxed.as_ptr() };
    assert!(*value || !*value);
}
pub fn raw_stack_poison_rhs_initialization() {
    let invalid = unsafe { core::mem::MaybeUninit::<bool>::uninit().as_ptr().read() };
    let values = vec![invalid, true];
    assert!(values.len() == 2);
}
pub fn discarded_raw_stack_read_before_initialization() {
    let invalid = unsafe { core::mem::MaybeUninit::<bool>::uninit().as_ptr().read() };
    let _ = invalid;
    let values = vec![true, true];
    assert!(values.len() == 2);
}
pub fn partial_initialization() {
    let mut boxed = Box::<[bool; 2]>::new_uninit();
    unsafe {
        (boxed.as_mut_ptr() as *mut bool).write(true);
    }
    let values = std::boxed::box_assume_init_into_vec_unsafe::<bool, 2>(boxed);
    assert!(values.len() == 2);
}

pub fn discarded_address_of_stack_maybe_read() {
    let slot = core::mem::MaybeUninit::<bool>::uninit();
    let pointer = &slot as *const core::mem::MaybeUninit<bool> as *const bool;
    let _ = unsafe { pointer.read() };
    let values = vec![true, true];
    assert!(values.len() == 2);
}
static UNINITIALIZED: core::mem::MaybeUninit<bool> = core::mem::MaybeUninit::uninit();
pub fn discarded_constant_maybe_read() {
    let pointer = &UNINITIALIZED as *const core::mem::MaybeUninit<bool> as *const bool;
    let _ = unsafe { pointer.read() };
    let values = vec![true, true];
    assert!(values.len() == 2);
}
pub fn discarded_maybe_byte_view_read() {
    let slot = core::mem::MaybeUninit::<bool>::uninit();
    let bytes = slot.as_bytes();
    let _ = unsafe { bytes.as_ptr().cast::<u8>().read() };
    let values = vec![true, true];
    assert!(values.len() == 2);
}
#[inline(never)]
fn stack_read_wrapper() -> bool {
    unsafe { core::mem::MaybeUninit::<bool>::uninit().as_ptr().read() }
}
pub fn discarded_nested_stack_read() {
    let _ = stack_read_wrapper();
    let values = vec![true, true];
    assert!(values.len() == 2);
}
#[inline(never)]
fn stack_read_outer_wrapper() {
    let _ = stack_read_wrapper();
}
pub fn discarded_twice_nested_stack_read() {
    stack_read_outer_wrapper();
    let values = vec![true, true];
    assert!(values.len() == 2);
}
pub fn discarded_array_maybe_read() {
    let slots = [core::mem::MaybeUninit::<bool>::uninit(); 2];
    let _ = unsafe { slots.as_ptr().cast::<bool>().read() };
    let values = vec![true, true];
    assert!(values.len() == 2);
}
struct Wrapped {
    slot: core::mem::MaybeUninit<bool>,
}
pub fn discarded_wrapped_maybe_read() {
    let wrapped = Wrapped { slot: core::mem::MaybeUninit::uninit() };
    let _ = unsafe { wrapped.slot.as_ptr().read() };
    let values = vec![true, true];
    assert!(values.len() == 2);
}
// Defined but unsupported: an initialized stack value has no native
// Box custody or initializedness sidecar in this bounded model.
pub fn initialized_stack_maybe_without_frame_certificate() {
    let slot = core::mem::MaybeUninit::new(true);
    let value = unsafe { slot.as_ptr().read() };
    assert!(value);
}
pub fn native_address_word_is_not_a_logical_object_number() {
    let mut boxed = Box::<u32>::new_uninit();
    let address = (&mut *boxed as *mut core::mem::MaybeUninit<u32>) as usize;
    assert!(address & u32::MAX as usize == 0);
    boxed.write(17);
    let value = unsafe { boxed.assume_init() };
    assert!(*value == 17);
}
