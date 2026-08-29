// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: UNKNOWN
//! any_where with Vec::len() in the closure — isolate the Vec::len interaction.

#[kani::proof]
fn any_where_vec_len() {
    let v = vec![1u32, 2, 3];
    let idx: usize = kani::any_where(|i: &usize| *i < v.len());
    assert!(idx < 3);
}
