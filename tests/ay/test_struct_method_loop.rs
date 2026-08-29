// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// kani-expect: PROOF

/// Match the TableauRow pattern exactly
#[derive(Clone, Copy)]
struct Row {
    basic_var: u32,
    vars: [u32; 4],
    coeffs: [i64; 4],
    len: usize,
}

impl Row {
    fn new_1(basic_var: u32, v0: u32, c0: i64) -> Self {
        let mut r = Self { basic_var, vars: [0; 4], coeffs: [0; 4], len: 0 };
        r.vars[0] = v0;
        r.coeffs[0] = c0;
        r.len = 1;
        r
    }

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

#[kani::proof]
fn proof_row_coeff_missing() {
    let row = Row::new_1(0, 1, 3);
    let c = row.coeff(2);
    assert!(c == 0, "Missing var returns 0");
}

#[kani::proof]
fn proof_row_coeff_found() {
    let row = Row::new_1(0, 1, 3);
    let c = row.coeff(1);
    assert!(c == 3, "Found var returns 3");
}
