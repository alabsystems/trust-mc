// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: PROOF
// NOTE: 1 harness(es) ERROR→UNKNOWN (error resolved).

struct Simple {
    data: Vec<u32>,
    flag: bool,
}

impl Simple {
    fn new() -> Self {
        Self {
            data: Vec::new(),
            flag: true,
        }
    }
}

#[kani::proof]
fn probe_simple_struct_vec_len_inline() {
    let s = Simple::new();
    assert_eq!(s.data.len(), 0);
}
