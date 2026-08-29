// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: PROOF

use std::sync::atomic::{AtomicBool, Ordering};

#[kani::proof]
fn main() {
    let a = AtomicBool::new(true);
    let result = a.compare_exchange(true, false, Ordering::SeqCst, Ordering::SeqCst);
    assert!(result == Ok(true));
}
