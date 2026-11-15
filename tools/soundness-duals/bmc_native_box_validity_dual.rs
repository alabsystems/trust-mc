// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Native BMC Box validity. Expectations are Rust semantics, including strict
//! controls for metadata/provenance boundaries that are not yet modeled.

#[kani::proof]
fn scalar_read_safe() {
    let value = Box::new(7u32);
    assert!(*value == 7);
}
#[kani::proof]
fn scalar_wrong_value_bug() {
    let value = Box::new(7u32);
    assert!(*value == 0);
}
#[kani::proof]
fn array_element_safe() {
    let value = Box::new([7u32, 9]);
    assert!(value[1] == 9);
}
#[kani::proof]
fn array_wrong_element_bug() {
    let value = Box::new([7u32, 9]);
    assert!(value[1] == 10);
}
#[kani::proof]
fn pointer_identity_safe() {
    let value = Box::new(7u32);
    let first = core::ptr::addr_of!(*value);
    let second = core::ptr::addr_of!(*value);
    assert!(first == second);
}
#[kani::proof]
fn pointer_identity_wrong_bug() {
    let value = Box::new(7u32);
    let first = core::ptr::addr_of!(*value);
    let second = core::ptr::addr_of!(*value);
    assert!(first != second);
}
#[repr(align(32))]
struct AlignedZst;
#[kani::proof]
fn aligned_dangling_zst_safe() {
    let value = Box::new(AlignedZst);
    let pointer = core::ptr::addr_of!(*value);
    assert!(!pointer.is_null());
}
#[kani::proof]
fn aligned_dangling_zst_is_not_null_bug() {
    let value = Box::new(AlignedZst);
    let pointer = core::ptr::addr_of!(*value);
    assert!(pointer.is_null());
}
#[kani::proof]
fn raw_pointer_rewrap_safe() {
    let pointer = Box::into_raw(Box::new(7u32));
    let value = unsafe { Box::from_raw(pointer) };
    assert!(*value == 7);
}
#[kani::proof]
fn raw_pointer_rewrap_wrong_value_bug() {
    let pointer = Box::into_raw(Box::new(7u32));
    let value = unsafe { Box::from_raw(pointer) };
    assert!(*value == 0);
}
#[kani::proof]
fn null_box_cast_bug() {
    let value = unsafe { Box::from_raw(core::ptr::null_mut::<u32>()) };
    let _ = core::ptr::addr_of!(*value);
    core::mem::forget(value);
}
#[kani::proof]
fn misaligned_box_cast_bug() {
    let pointer = Box::into_raw(Box::new([7u32, 9]));
    let shifted = unsafe { pointer.cast::<u8>().add(1).cast::<u32>() };
    let value = unsafe { Box::from_raw(shifted) };
    let _ = core::ptr::addr_of!(*value);
    core::mem::forget(value);
}
#[kani::proof]
fn one_past_box_cast_bug() {
    let pointer = Box::into_raw(Box::new([7u32, 9]));
    let past = unsafe { pointer.cast::<u32>().add(2) };
    let value = unsafe { Box::from_raw(past) };
    let _ = core::ptr::addr_of!(*value);
    core::mem::forget(value);
}
#[kani::proof]
fn freed_box_cast_bug() {
    let pointer = Box::into_raw(Box::new(7u32));
    unsafe { std::alloc::dealloc(pointer.cast::<u8>(), core::alloc::Layout::new::<u32>()) };
    let value = unsafe { Box::from_raw(pointer) };
    let _ = core::ptr::addr_of!(*value);
    core::mem::forget(value);
}
enum Empty {}
#[kani::proof]
fn pointer_sized_impossible_pointee_bug() {
    let pointer = Box::into_raw(Box::new(0usize)).cast::<&'static Empty>();
    let value = unsafe { Box::from_raw(pointer) };
    let _ = core::ptr::addr_of!(*value);
    core::mem::forget(value);
}
#[kani::proof]
fn pointer_payload_load_safe() {
    let pointer = Box::into_raw(Box::new(7u32));
    let holder = Box::new(pointer);
    let returned = *holder;
    let value = unsafe { Box::from_raw(returned) };
    assert!(*value == 7);
}
#[kani::proof]
fn pointer_payload_load_wrong_value_bug() {
    let pointer = Box::into_raw(Box::new(7u32));
    let holder = Box::new(pointer);
    let returned = *holder;
    let value = unsafe { Box::from_raw(returned) };
    assert!(*value == 0);
}
#[kani::proof]
fn slice_metadata_safe() {
    let value: Box<[u32]> = Box::new([7u32, 9]);
    assert!(value[1] == 9);
}
trait ReadValue {
    fn read(&self) -> u32;
}
struct Value(u32);
impl ReadValue for Value {
    fn read(&self) -> u32 {
        self.0
    }
}
#[kani::proof]
fn dyn_metadata_safe() {
    let value: Box<dyn ReadValue> = Box::new(Value(7));
    assert!(value.read() == 7);
}
#[kani::proof]
fn untracked_actual_box_cast_bug() {
    let bits: usize = kani::any();
    let value: Box<u32> = unsafe { core::mem::transmute(bits) };
    let _ = core::ptr::addr_of!(*value);
    core::mem::forget(value);
}

#[kani::proof]
fn scalar_store_then_read_safe() {
    let mut value = Box::new(7u32);
    *value = 9;
    assert!(*value == 9);
}
#[kani::proof]
fn scalar_store_then_read_wrong_value_bug() {
    let mut value = Box::new(7u32);
    *value = 9;
    assert!(*value == 7);
}
#[kani::proof]
fn dropped_box_cast_bug() {
    let pointer = Box::into_raw(Box::new(7u32));
    unsafe {
        drop(Box::from_raw(pointer));
    }
    let value = unsafe { Box::from_raw(pointer) };
    let _ = core::ptr::addr_of!(*value);
    core::mem::forget(value);
}

#[repr(align(32))]
struct AlignedStorage([u8; 32]);
#[kani::proof]
fn aligned_zst_from_freed_address_safe() {
    let storage = Box::into_raw(Box::new(AlignedStorage([0; 32])));
    unsafe { std::alloc::dealloc(storage.cast(), core::alloc::Layout::new::<AlignedStorage>()) };
    let value = unsafe { Box::from_raw(storage.cast::<AlignedZst>()) };
    let pointer = core::ptr::addr_of!(*value);
    assert!(pointer != core::ptr::null());
}
#[kani::proof]
fn aligned_zst_from_freed_address_is_not_null_bug() {
    let storage = Box::into_raw(Box::new(AlignedStorage([0; 32])));
    unsafe { std::alloc::dealloc(storage.cast(), core::alloc::Layout::new::<AlignedStorage>()) };
    let value = unsafe { Box::from_raw(storage.cast::<AlignedZst>()) };
    let pointer = core::ptr::addr_of!(*value);
    assert!(pointer == core::ptr::null());
}

#[kani::proof]
fn address_api_roundtrip_safe() {
    let pointer = Box::into_raw(Box::new(7u32));
    let address = pointer.addr();
    let restored = pointer.with_addr(address);
    let value = unsafe { Box::from_raw(restored) };
    assert!(*value == 7);
}
#[kani::proof]
fn address_api_roundtrip_wrong_value_bug() {
    let pointer = Box::into_raw(Box::new(7u32));
    let address = pointer.addr();
    let restored = pointer.with_addr(address);
    let value = unsafe { Box::from_raw(restored) };
    assert!(*value == 0);
}
