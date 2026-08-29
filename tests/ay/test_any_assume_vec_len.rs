// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: PROOF
//! kani::any + kani::assume with Vec::len — equivalent to any_where without closure.

#[kani::proof]
fn any_assume_vec_len() {
    let v = vec![1u32, 2, 3];
    let idx: usize = kani::any();
    kani::assume(idx < v.len());
    assert!(idx < 3);
}
