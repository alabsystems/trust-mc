// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// kani-expect: PROOF
// Test compare_exchange FAILURE path: expected != current returns Err(current).
// Part of #3502: compare_exchange Err variant has zero test coverage.
//
// All existing compare_exchange tests use expected == current (guaranteed Ok).
// This harness exercises the Err codegen path where the swap does NOT happen.

use std::sync::atomic::{AtomicBool, Ordering};

/// compare_exchange where expected != current: must return Err(current_value).
#[kani::proof]
fn test_cmpxchg_failure_path() {
    let a = AtomicBool::new(true);
    // expected=false, but current=true => mismatch => Err(true)
    let result = a.compare_exchange(false, true, Ordering::SeqCst, Ordering::SeqCst);
    assert!(result.is_err());
    assert!(result.unwrap_err() == true);
    // Value must remain unchanged after failed CAS.
    assert!(a.load(Ordering::SeqCst) == true);
}
