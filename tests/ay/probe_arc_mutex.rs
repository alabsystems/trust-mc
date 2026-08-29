// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// kani-expect: PROOF
// NOTE: All harnesses demoted PROOF→UNKNOWN by false proof defense (ay#8578).
//! Probe: test Arc<Mutex<T>> construction (Part of #4067).
//! Progression: probe_mutex_new (PROOF) → this → SizeAndAlignOfDst/main.rs

use std::sync::Arc;
use std::sync::Mutex;

#[kani::proof]
fn test_arc_mutex_u32() {
    let _s: Arc<Mutex<u32>> = Arc::new(Mutex::new(42u32));
}
