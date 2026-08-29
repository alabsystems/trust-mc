// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// kani-expect: PROOF

#[derive(Clone, Copy)]
struct Row {
    basic_var: u32,
    vars: [u32; 4],
    coeffs: [i64; 4],
    len: usize,
}

/// Same logic as Row::coeff but written inline (no method call)
#[kani::proof]
fn proof_row_inline_coeff_missing() {
    let row = Row {
        basic_var: 0,
        vars: [1, 0, 0, 0],
        coeffs: [3, 0, 0, 0],
        len: 1,
    };

    // Inline equivalent of row.coeff(2)
    let var: u32 = 2;
    let mut i = 0;
    let mut result: i64 = 0;
    let mut found = false;
    while i < row.len {
        if row.vars[i] == var {
            result = row.coeffs[i];
            found = true;
        }
        i += 1;
    }
    // coeff returns 0 when not found
    if !found {
        result = 0;
    }
    assert!(result == 0, "Missing var returns 0");
}
