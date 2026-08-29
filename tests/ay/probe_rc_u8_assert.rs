// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// kani-expect: UNKNOWN
// AY pin regression: was CTREX at dd45481b, UNKNOWN at 9c1160ea
//! Probe: Rc<u8> with assertion (matches unsized_rc_cast pattern).

use std::rc::Rc;

#[kani::proof]
fn test_rc_u8_assert() {
    let val: u8 = kani::any();
    kani::assume(val != 0);
    let rc: Rc<u8> = Rc::new(val);
    assert!(*rc != 0);
}
