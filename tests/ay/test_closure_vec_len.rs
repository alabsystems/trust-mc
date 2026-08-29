// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: PROOF
//! Closure capturing Vec + calling len — isolates closure capture of Vec::len.

#[kani::proof]
fn closure_vec_len() {
    let v = vec![1u32, 2, 3];
    let check = |idx: &usize| *idx < v.len();
    let idx: usize = kani::any();
    kani::assume(check(&idx));
    assert!(idx < 3);
}
