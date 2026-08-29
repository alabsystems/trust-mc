// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// kani-expect: PROOF
// NOTE: All harnesses demoted PROOF→UNKNOWN by false proof defense (ay#8578).
//! Probe: Arc<dyn Trait> without Mutex wrapper.
//! If this is PROOF, the gap is Mutex-specific.
//! If this is CTREX, the gap is Arc+dyn unsized coercion.

use std::sync::Arc;

pub trait Subscriber {
    fn process(&mut self);
}

struct DummySubscriber;

impl Subscriber for DummySubscriber {
    fn process(&mut self) {}
}

#[kani::proof]
fn test_arc_dyn() {
    let _s: Arc<dyn Subscriber> = Arc::new(DummySubscriber);
}
