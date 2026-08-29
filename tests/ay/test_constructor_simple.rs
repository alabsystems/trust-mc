// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// kani-expect: PROOF

#[derive(Clone, Copy)]
struct Row {
    vars: [u32; 4],
    len: usize,
}

impl Row {
    fn new_1(v0: u32) -> Self {
        let mut r = Self { vars: [0; 4], len: 0 };
        r.vars[0] = v0;
        r.len = 1;
        r
    }
}

#[kani::proof]
fn proof_simple_constructor() {
    let row = Row::new_1(42);
    assert!(row.vars[0] == 42, "vars[0] is 42");
    assert!(row.len == 1, "len is 1");
}
