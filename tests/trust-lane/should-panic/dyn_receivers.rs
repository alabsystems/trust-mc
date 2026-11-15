// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! `should_panic` over trait-object receivers, as route duals. None of the `_refuted` harnesses
//! panics when run, so none may be SUCCESSFUL; `_holds` really panics. The CHC `Rc<dyn>` and
//! `Arc<dyn>` receivers read a cell nothing wrote (an allocation id minted for the `Rc` local's
//! own slot), the overflow on it was certified Genuine, and `should_panic` turned that into
//! `SUCCESSFUL (encountered one or more panics as expected)`.

#![feature(coerce_unsized, unsize)]
use std::marker::Unsize;
use std::ops::CoerceUnsized;
use std::ptr::NonNull;
use std::rc::Rc;
use std::sync::Arc;

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
        unsafe { self.ptr.as_ref() }
    }
}

#[kani::proof]
#[kani::should_panic]
fn rc_area_should_panic_refuted() {
    let r: Rc<dyn Shape> = Rc::new(Square(4));
    let _ = r.area();
}

#[kani::proof]
#[kani::should_panic]
fn arc_area_should_panic_refuted() {
    let a: Arc<dyn Shape> = Arc::new(Square(2));
    let _ = a.area();
}

#[kani::proof]
#[kani::should_panic]
fn box_area_should_panic_refuted() {
    let b: Box<dyn Shape> = Box::new(Square(3));
    let _ = b.area();
}

#[kani::proof]
#[kani::should_panic]
fn custom_area_should_panic_refuted() {
    let mut square = Square(5);
    let concrete: MyPtr<Square> = MyPtr { ptr: NonNull::from(&mut square) };
    let object: MyPtr<dyn Shape> = concrete;
    let _ = object.get().area();
}

#[kani::proof]
#[kani::should_panic]
fn box_slice_index_should_panic_refuted() {
    let b: Box<[u8]> = Box::new([1u8, 2, 3]);
    let _ = b[2];
}

#[kani::proof]
#[kani::should_panic]
fn rc_slice_index_should_panic_refuted() {
    let r: Rc<[u8]> = Rc::new([1u8, 2, 3]);
    let _ = r[2];
}

#[kani::proof]
#[kani::should_panic]
fn nonnull_len_should_panic_refuted() {
    let mut a = [1u8, 2, 3, 4];
    let p: NonNull<[u8]> = NonNull::from(&mut a);
    assert!(p.len() == 4, "nonnull slice length");
}

#[kani::proof]
#[kani::should_panic]
fn rc_area_overflow_should_panic_holds() {
    let r: Rc<dyn Shape> = Rc::new(Square(70000));
    let _ = r.area();
}
