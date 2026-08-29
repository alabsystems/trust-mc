// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// kani-expect: PROOF
// NOTE: All harnesses demoted PROOF→UNKNOWN by false proof defense (ay#8578).
//! Probe: Rc<ConcreteType> — no unsized coercion.

use std::rc::Rc;

struct DummySubscriber;

#[kani::proof]
fn test_rc_concrete() {
    let _s: Rc<DummySubscriber> = Rc::new(DummySubscriber);
}
