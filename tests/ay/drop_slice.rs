// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-expect: PROOF
//
// Ported from kani/tests/kani/Drop/drop_slice.rs
// Part of #4268: Drop encoding completeness.
//
// Ensure that we can handle cast and drop of the mutex to a slice.
// Arc<Mutex<[u8]>> involves unsized coercion and Mutex drop handling.

use std::sync::Arc;
use std::sync::Mutex;

#[kani::proof]
fn check_drop_slice() {
    let _: Arc<Mutex<[u8]>> = Arc::new(Mutex::new([10, 0]));
}
