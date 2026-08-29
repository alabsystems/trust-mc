// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-expect: PROOF
//
// Minimal test for Cow<str>::to_string() stub matching.
// Part of #1738.

use std::borrow::Cow;

#[kani::proof]
fn test_cow_tostring() {
    let cow: Cow<str> = Cow::Borrowed("hello");
    let s = cow.to_string();
    assert!(s.len() >= 0);  // Should always be true
}
