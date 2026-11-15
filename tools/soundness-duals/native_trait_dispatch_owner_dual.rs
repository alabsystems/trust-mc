// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

#![allow(dead_code)]

trait Tv {
    fn get(&self) -> u8;
}
struct Value {
    a: u8,
    b: u8,
}
impl Tv for Value {
    fn get(&self) -> u8 {
        self.a
    }
}
struct Pointer {
    p: *const u8,
}
impl Tv for Pointer {
    fn get(&self) -> u8 {
        unsafe { *self.p }
    }
}

fn keep_pointer_impl_alive(byte: &u8) -> u8 {
    let owner: Box<dyn Tv> = Box::new(Pointer { p: byte });
    owner.get()
}

#[kani::proof]
fn native_trait_dispatch_safe() {
    let a: u8 = kani::any();
    let owner: Box<dyn Tv> = Box::new(Value { a, b: 1 });
    assert!(owner.get() == a);
}

#[kani::proof]
fn native_trait_dispatch_bug() {
    let a: u8 = kani::any();
    let owner: Box<dyn Tv> = Box::new(Value { a, b: 1 });
    assert!(owner.get() != a);
}

#[kani::proof]
fn native_trait_copied_owner_safe() {
    let a: u8 = kani::any();
    let first: Box<dyn Tv> = Box::new(Value { a, b: 1 });
    let second = first;
    assert!(second.get() == a);
}

#[kani::proof]
fn native_trait_copied_owner_bug() {
    let a: u8 = kani::any();
    let first: Box<dyn Tv> = Box::new(Value { a, b: 1 });
    let second = first;
    assert!(second.get() != a);
}

// Compile/model-check only. The native oracle never invokes this UB body.
#[kani::proof]
fn native_trait_pointer_oob_bug() {
    let bytes = [1u8, 2];
    let owner: Box<dyn Tv> = Box::new(Pointer { p: bytes.as_ptr().wrapping_add(2) });
    let _ = owner.get();
}
