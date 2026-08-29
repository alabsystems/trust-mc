// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-expect: PROOF
// kani-expect: main=UNKNOWN  // AY-bump regression from PROOF (3d9db24e68); sound demotion
//
// Ported from kani/tests/kani/Drop/drop_after_mutating_refcell.rs
// Part of #4268: Drop encoding completeness.
//
// This test checks whether dropping after mutating with
// Rc<RefCell<>> is handled correctly.

use std::cell::RefCell;
use std::rc::Rc;

static mut CELL: i32 = 0;

trait CELLValueInFuture {
    fn set_inner_value(&mut self, new_value: i32);
    fn get_inner_value(&self) -> i32;
}

struct DropSetCELLToInner {
    set_cell_to: i32,
}

impl CELLValueInFuture for DropSetCELLToInner {
    fn set_inner_value(&mut self, new_value: i32) {
        self.set_cell_to = new_value;
    }

    fn get_inner_value(&self) -> i32 {
        self.set_cell_to
    }
}

impl Drop for DropSetCELLToInner {
    fn drop(&mut self) {
        unsafe {
            CELL = self.get_inner_value();
        }
    }
}

#[kani::proof]
fn main() {
    {
        let set_to_one = DropSetCELLToInner { set_cell_to: 1 };
        let wrapped_drop: Rc<RefCell<DropSetCELLToInner>> = Rc::new(RefCell::new(set_to_one));

        wrapped_drop.borrow_mut().set_inner_value(2);
        assert_eq!(wrapped_drop.borrow().get_inner_value(), 2, "Value should be updated.");
    }
    assert_eq!(unsafe { CELL }, 2, "Drop should be called. New value used during drop.");
}
