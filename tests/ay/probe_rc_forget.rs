// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// kani-expect: PROOF
//! Probe: Rc<u8> with forget (no drop).

use std::rc::Rc;

#[kani::proof]
fn test_rc_forget() {
    let s: Rc<u8> = Rc::new(42u8);
    std::mem::forget(s);
}
