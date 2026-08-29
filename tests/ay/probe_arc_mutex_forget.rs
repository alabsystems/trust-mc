// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// kani-expect: PROOF
//! Probe: Arc<Mutex<dyn Subscriber>> with forget (no drop).
//! Isolates Arc+Mutex construction path from drop path.

use std::sync::{Arc, Mutex};

pub trait Subscriber {
    fn process(&mut self);
}

struct DummySubscriber;

impl Subscriber for DummySubscriber {
    fn process(&mut self) {}
}

#[kani::proof]
fn test_arc_mutex_forget() {
    let s: Arc<Mutex<dyn Subscriber>> = Arc::new(Mutex::new(DummySubscriber));
    std::mem::forget(s);
}
