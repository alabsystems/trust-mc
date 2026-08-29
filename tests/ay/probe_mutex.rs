// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: PROOF

use std::sync::Mutex;

#[kani::proof]
fn test_mutex_new_only() {
    let m = Mutex::new(42u32);
    let _ = m;
}
