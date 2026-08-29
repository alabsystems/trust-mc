// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: UNKNOWN
//! any_where with a captured local (not Vec) — isolate capture interaction.

#[kani::proof]
fn any_where_capture() {
    let bound: u32 = 5;
    let x: u32 = kani::any_where(|v: &u32| *v < bound);
    assert!(x < 5);
}
