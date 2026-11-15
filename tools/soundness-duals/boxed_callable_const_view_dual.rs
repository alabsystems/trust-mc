// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Pointer identities cannot be used as physical bytes of a reference payload.
//! Both reads cover the first initialized byte of a live Box<&FnDef>. No raw
//! write, padding read, dangling pointer, or function-pointer reinterpretation
//! occurs. The same-byte assertions are ordinary Rust truth; unsupported byte
//! views must remain explicitly incomplete, including after address escape.

// Defined native reference bytes: both reads are within a live Box<&FnDef>.
// There is no padding in this held compiler's scalar shared-reference layout.
fn increment(value: &mut i32) {
    *value = value.wrapping_add(1);
}
#[inline(never)]
fn escaped_read(p: *const u8) -> u8 {
    unsafe { p.read() }
}
#[kani::proof]
fn physical_byte_safe() {
    let payload = Box::new(&increment);
    let bytes = std::ptr::addr_of!(*payload).cast::<u8>();
    let before = unsafe { bytes.read() };
    let mut function: Box<dyn FnMut(&mut i32)> = payload;
    let mut value = 1;
    function(&mut value);
    let after = unsafe { bytes.read() };
    assert!(before == after);
}

#[kani::proof]
fn physical_byte_bug() {
    let payload = Box::new(&increment);
    let bytes = std::ptr::addr_of!(*payload).cast::<u8>();
    let before = unsafe { bytes.read() };
    let mut function: Box<dyn FnMut(&mut i32)> = payload;
    let mut value = 1;
    function(&mut value);
    let after = unsafe { bytes.read() };
    assert!(before != after);
}

#[kani::proof]
fn escaped_byte_safe() {
    let payload = Box::new(&increment);
    let bytes = std::ptr::addr_of!(*payload).cast::<u8>();
    let before = escaped_read(bytes);
    let mut function: Box<dyn FnMut(&mut i32)> = payload;
    let mut value = 1;
    function(&mut value);
    let after = escaped_read(bytes);
    assert!(before == after);
}

#[kani::proof]
fn escaped_byte_bug() {
    let payload = Box::new(&increment);
    let bytes = std::ptr::addr_of!(*payload).cast::<u8>();
    let before = escaped_read(bytes);
    let mut function: Box<dyn FnMut(&mut i32)> = payload;
    let mut value = 1;
    function(&mut value);
    let after = escaped_read(bytes);
    assert!(before != after);
}
#[kani::proof]
fn symbolic_byte_safe() {
    let payload = Box::new(&increment);
    let bytes = std::ptr::addr_of!(*payload).cast::<u8>();
    let index = if kani::any::<bool>() { 0usize } else { 1usize };
    let before = unsafe { bytes.add(index).read() };
    let mut function: Box<dyn FnMut(&mut i32)> = payload;
    let mut value = 1;
    function(&mut value);
    let after = unsafe { bytes.add(index).read() };
    assert!(before == after);
}

#[kani::proof]
fn symbolic_byte_bug() {
    let payload = Box::new(&increment);
    let bytes = std::ptr::addr_of!(*payload).cast::<u8>();
    let index = if kani::any::<bool>() { 0usize } else { 1usize };
    let before = unsafe { bytes.add(index).read() };
    let mut function: Box<dyn FnMut(&mut i32)> = payload;
    let mut value = 1;
    function(&mut value);
    let after = unsafe { bytes.add(index).read() };
    assert!(before != after);
}
