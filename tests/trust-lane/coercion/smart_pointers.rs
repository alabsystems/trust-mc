// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Unsized coercions through `Box`, `Rc`, `Arc`, `NonNull` and `&mut`, each as a pass/fail
//! dual. On Trust, `NonNull<T>` holds `pattern_type!(*const T is !null)`, so every coercion
//! here except `&mut dyn` walks through a pattern type; before the fix the engine panicked
//! in `kani_middle/coercion.rs` on all of them. Each `_holds` harness must be SUCCESSFUL and
//! each `_refuted` harness FAILED, in both lanes and on both compiler routes.

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

trait Bump {
    fn bump(&mut self);
}

struct Counter(u32);

impl Bump for Counter {
    fn bump(&mut self) {
        self.0 += 1;
    }
}

#[kani::proof]
fn box_dyn_holds() {
    let b: Box<dyn Shape> = Box::new(Square(3));
    assert!(b.area() == 9, "box area");
}

#[kani::proof]
fn box_dyn_refuted() {
    let b: Box<dyn Shape> = Box::new(Square(3));
    assert!(b.area() == 10, "box area");
}

#[kani::proof]
fn rc_dyn_holds() {
    let r: Rc<dyn Shape> = Rc::new(Square(4));
    assert!(r.area() == 16, "rc area");
}

#[kani::proof]
fn rc_dyn_refuted() {
    let r: Rc<dyn Shape> = Rc::new(Square(4));
    assert!(r.area() == 15, "rc area");
}

#[kani::proof]
fn arc_dyn_holds() {
    let a: Arc<dyn Shape> = Arc::new(Square(2));
    assert!(a.area() == 4, "arc area");
}

#[kani::proof]
fn arc_dyn_refuted() {
    let a: Arc<dyn Shape> = Arc::new(Square(2));
    assert!(a.area() == 5, "arc area");
}

#[kani::proof]
fn nonnull_slice_holds() {
    let mut bytes = [1u8, 2, 3, 4];
    let whole: NonNull<[u8; 4]> = NonNull::from(&mut bytes);
    let slice: NonNull<[u8]> = whole;
    assert!(slice.len() == 4, "nonnull slice length");
}

#[kani::proof]
fn nonnull_slice_refuted() {
    let mut bytes = [1u8, 2, 3, 4];
    let whole: NonNull<[u8; 4]> = NonNull::from(&mut bytes);
    let slice: NonNull<[u8]> = whole;
    assert!(slice.len() == 5, "nonnull slice length");
}

#[kani::proof]
fn mut_dyn_holds() {
    let mut counter = Counter(0);
    {
        let d: &mut dyn Bump = &mut counter;
        d.bump();
    }
    assert!(counter.0 == 1, "bumped once");
}

#[kani::proof]
fn mut_dyn_refuted() {
    let mut counter = Counter(0);
    {
        let d: &mut dyn Bump = &mut counter;
        d.bump();
    }
    assert!(counter.0 == 2, "bumped once");
}
