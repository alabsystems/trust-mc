// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: PROOF
//! Minimal any_where test — no Vec::len, just a constant bound.

#[kani::proof]
fn any_where_minimal() {
    let x: u32 = kani::any_where(|v: &u32| *v < 10);
    assert!(x < 10);
}
