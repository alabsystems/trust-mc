// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// kani-expect: UNKNOWN
// AY pin regression: was CTREX at dd45481b, UNKNOWN at 9c1160ea
//! Probe: Rc<u8> concrete value + deref + assert.

use std::rc::Rc;

#[kani::proof]
fn test_rc_concrete_assert() {
    let rc: Rc<u8> = Rc::new(42u8);
    assert!(*rc == 42);
}
