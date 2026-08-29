// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: UNKNOWN
//! Diagnostic: any_where captures Vec, asserts only the bound.

#[kani::proof]
fn offset_vec_steps() {
    let v = vec![0u64, 2u64];
    let offset: usize = kani::any_where(|o: &usize| *o <= v.len());
    assert!(offset <= 2);
}
