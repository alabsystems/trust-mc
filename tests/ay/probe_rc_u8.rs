// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// kani-expect: PROOF
// NOTE: All harnesses demoted PROOF→UNKNOWN by false proof defense (ay#8578).
//! Probe: Rc<u8> — scalar inner type.

use std::rc::Rc;

#[kani::proof]
fn test_rc_u8() {
    let _s: Rc<u8> = Rc::new(42u8);
}
