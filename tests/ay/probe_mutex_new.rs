// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// kani-expect: PROOF
//! Part of #4067: Probe Mutex::new identity stub.
//! Verifies that Mutex::new(value) is transparent in single-threaded
//! verification and the inner value is preserved.

use std::sync::Mutex;

#[kani::proof]
fn test_mutex_new_identity() {
    let m = Mutex::new(42u32);
    let val = m.into_inner().unwrap();
    assert_eq!(val, 42);
}
