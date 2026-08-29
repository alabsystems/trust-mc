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

impl Row {
    fn coeff(&self, var: u32) -> i64 {
        let mut i = 0;
        while i < self.len {
            if self.vars[i] == var {
                return self.coeffs[i];
            }
            i += 1;
        }
        0
    }
}

/// Construct with mutation like new_1 but inline
#[kani::proof]
fn proof_mutated_coeff_missing() {
    let mut row = Row {
        basic_var: 0,
        vars: [0; 4],
        coeffs: [0; 4],
        len: 0,
    };
    row.vars[0] = 1;
    row.coeffs[0] = 3;
    row.len = 1;
    let c = row.coeff(2);
    assert!(c == 0, "Missing var returns 0");
}
