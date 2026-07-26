// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// compile-flags: --edition 2018

use kani::shadow::{MAX_TRACKED_BYTES_PER_OBJECT, MAX_TRACKED_OBJECTS};

#[kani::proof]
fn main() {
    let _ = MAX_TRACKED_OBJECTS;
    let _ = MAX_TRACKED_BYTES_PER_OBJECT;
}
