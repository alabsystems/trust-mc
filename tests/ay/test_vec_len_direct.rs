// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: PROOF
//! Direct Vec::len test — no any_where, no closure. Isolates Vec::len encoding.

#[kani::proof]
fn vec_len_direct() {
    let v = vec![1u32, 2, 3];
    let len = v.len();
    assert!(len == 3);
}
