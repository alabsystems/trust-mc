// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-expect: UNKNOWN
// AY pin regression: was CTREX at dd45481b, UNKNOWN at 9c1160ea
//
// Part of #4097: Verify Rc<T> inner Drop::drop() is inlined by D1.
// Rc wrapping a concrete non-ZST type with a custom Drop impl
// that writes to a static mut. No RefCell, no dyn, no nested Box.
//
// D1 inline succeeds (confirmed: translate_inline_body returns
// 1 pending_update + 10 pending_checks). CTREX is genuine from
// kani_mem safety checks on allocation addresses — same pattern as
// rc_dyn.rs. Expected to flip PROOF once allocation address model
// is constrained.

use std::rc::Rc;

static mut CELL: i32 = 0;

struct Droppable {
    value: i32,
}

impl Drop for Droppable {
    fn drop(&mut self) {
        unsafe {
            CELL = self.value;
        }
    }
}

#[kani::proof]
fn test_rc_inner_drop() {
    {
        let _rc: Rc<Droppable> = Rc::new(Droppable { value: 42 });
    }
    // After Rc is dropped, the inner Droppable::drop should have run.
    assert!(unsafe { CELL } == 42);
}
