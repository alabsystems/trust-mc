// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A user smart pointer over `NonNull` with its own `CoerceUnsized` impl, coerced to a trait
//! object and to a slice, as pass/fail duals. The coercion walks MyPtr -> NonNull -> (on
//! Trust) the pattern-typed pointer -> the raw pointer.

#![feature(coerce_unsized, unsize)]

use std::marker::Unsize;
use std::ops::CoerceUnsized;
use std::ptr::NonNull;

trait Shape {
    fn area(&self) -> u32;
}

struct Square(u32);

impl Shape for Square {
    fn area(&self) -> u32 {
        self.0 * self.0
    }
}

struct MyPtr<T: ?Sized> {
    ptr: NonNull<T>,
}

impl<T: ?Sized + Unsize<U>, U: ?Sized> CoerceUnsized<MyPtr<U>> for MyPtr<T> {}

impl<T: ?Sized> MyPtr<T> {
    fn get(&self) -> &T {
        // SAFETY: every MyPtr below points at a local that outlives it.
        unsafe { self.ptr.as_ref() }
    }
}

#[kani::proof]
fn custom_dyn_holds() {
    let mut square = Square(5);
    let concrete: MyPtr<Square> = MyPtr { ptr: NonNull::from(&mut square) };
    let object: MyPtr<dyn Shape> = concrete;
    assert!(object.get().area() == 25, "custom area");
}

#[kani::proof]
fn custom_dyn_refuted() {
    let mut square = Square(5);
    let concrete: MyPtr<Square> = MyPtr { ptr: NonNull::from(&mut square) };
    let object: MyPtr<dyn Shape> = concrete;
    assert!(object.get().area() == 24, "custom area");
}

#[kani::proof]
fn custom_slice_holds() {
    let mut bytes = [7u8, 8, 9];
    let concrete: MyPtr<[u8; 3]> = MyPtr { ptr: NonNull::from(&mut bytes) };
    let slice: MyPtr<[u8]> = concrete;
    assert!(slice.get().len() == 3, "custom slice length");
}

#[kani::proof]
fn custom_slice_refuted() {
    let mut bytes = [7u8, 8, 9];
    let concrete: MyPtr<[u8; 3]> = MyPtr { ptr: NonNull::from(&mut bytes) };
    let slice: MyPtr<[u8]> = concrete;
    assert!(slice.get().len() == 2, "custom slice length");
}
