// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: UNKNOWN
// kani-expect: probe_new_len_zero=PROOF
// kani-expect: probe_new_pop_len=PROOF
// NOTE: probe_new_pop_len was PROOF at ay 417854b7, regressed to UNKNOWN at ay 8a4a9bcc2 (false proof caught by defense).

type TermId = u32;

#[derive(Debug)]
struct ArraySolver {
    assign_terms: Vec<TermId>,
    assign_values: Vec<bool>,
    trail_terms: Vec<TermId>,
    trail_prev_present: Vec<bool>,
    trail_prev_values: Vec<bool>,
    scopes: Vec<usize>,
    dirty: bool,
}

impl ArraySolver {
    #[inline(never)]
    fn new() -> Self {
        Self {
            assign_terms: Vec::new(),
            assign_values: Vec::new(),
            trail_terms: Vec::new(),
            trail_prev_present: Vec::new(),
            trail_prev_values: Vec::new(),
            scopes: Vec::new(),
            dirty: true,
        }
    }

    #[inline(never)]
    fn pop(&mut self) {
        let Some(_marker) = self.scopes.pop() else {
            return;
        };
    }
}

/// Minimal: new() then read one len, assert it's 0.
#[kani::proof]
fn probe_new_len_zero() {
    let solver = ArraySolver::new();
    assert_eq!(solver.trail_terms.len(), 0);
}

/// Minimal: new() then pop() then read one len.
#[kani::proof]
fn probe_new_pop_len() {
    let mut solver = ArraySolver::new();
    let before = solver.trail_terms.len();
    solver.pop();
    assert_eq!(solver.trail_terms.len(), before);
}
