// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// kani-expect: PROOF

struct Row {
    vars: [u32; 4],
    len: usize,
}

#[kani::proof]
fn proof_array_field_direct() {
    let mut row = Row { vars: [0; 4], len: 0 };
    row.vars[0] = 42;
    row.len = 1;
    assert!(row.vars[0] == 42, "vars[0] is 42");
    assert!(row.len == 1, "len is 1");
}
