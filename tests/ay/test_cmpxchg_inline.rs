// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: PROOF
// NOTE: All harnesses demoted PROOF→UNKNOWN by false proof defense (ay#8578).

use std::sync::atomic::{AtomicBool, Ordering};

#[kani::proof]
fn main() {
    let a = AtomicBool::new(true);
    let result = a.compare_exchange(true, false, Ordering::SeqCst, Ordering::SeqCst);
    // Check discriminant and payload separately instead of == Ok(true)
    match result {
        Ok(val) => assert!(val == true),
        Err(_) => panic!("expected Ok"),
    }
}
