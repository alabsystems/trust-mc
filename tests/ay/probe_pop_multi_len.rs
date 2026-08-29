// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: UNKNOWN
// kani-expect: probe_multi_len_simple_pop=PROOF
// NOTE: probe_multi_len_simple_pop gained PROOF at ay 8a4a9bcc2.

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

/// Multiple len reads with simplified pop
#[kani::proof]
fn probe_multi_len_simple_pop() {
    let mut solver = ArraySolver::new();
    let trail_len_before = solver.trail_terms.len();
    let assigns_len_before = solver.assign_terms.len();
    solver.pop();
    assert_eq!(solver.trail_terms.len(), trail_len_before);
    assert_eq!(solver.trail_prev_present.len(), trail_len_before);
    assert_eq!(solver.trail_prev_values.len(), trail_len_before);
    assert_eq!(solver.assign_terms.len(), assigns_len_before);
    assert_eq!(solver.assign_values.len(), assigns_len_before);
    assert!(solver.scopes.is_empty());
}
