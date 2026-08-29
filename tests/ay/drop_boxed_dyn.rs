// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-expect: UNKNOWN
//
// Ported from kani/tests/kani/Drop/drop_boxed_dyn.rs
// Part of #4268: Drop encoding completeness.
//
// Check drop implementation for a boxed dynamic trait object.
// Tests D2 multi-impl vtable dispatch for drop.

static mut CELL: i32 = 0;

trait T {
    fn t(&self) {}
}

struct Concrete1;

impl T for Concrete1 {}

impl Drop for Concrete1 {
    fn drop(&mut self) {
        unsafe {
            CELL = 1;
        }
    }
}

struct Concrete2;

impl T for Concrete2 {}

impl Drop for Concrete2 {
    fn drop(&mut self) {
        unsafe {
            CELL = 2;
        }
    }
}

#[kani::proof]
fn main() {
    {
        let x: Box<dyn T>;
        if kani::any() {
            x = Box::new(Concrete1 {});
        } else {
            x = Box::new(Concrete2 {});
        }
    }
    unsafe {
        assert!(CELL == 1 || CELL == 2);
    }
}
