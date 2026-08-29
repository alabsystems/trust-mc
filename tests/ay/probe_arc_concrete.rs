// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// kani-expect: PROOF
// NOTE: All harnesses demoted PROOF→UNKNOWN by false proof defense (ay#8578).
//! Probe: Arc<ConcreteType> — no unsized coercion.

use std::sync::Arc;

struct DummySubscriber;

#[kani::proof]
fn test_arc_concrete() {
    let _s: Arc<DummySubscriber> = Arc::new(DummySubscriber);
}
