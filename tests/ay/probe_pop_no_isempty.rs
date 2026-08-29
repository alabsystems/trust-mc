// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: UNKNOWN
// kani-expect: probe_two_len_assigns=PROOF
// kani-expect: probe_two_len_trail=PROOF
// NOTE: probe_multi_len_no_isempty, probe_two_len_trail were PROOF at ay 417854b7, regressed to UNKNOWN at ay 8a4a9bcc2 (false proofs caught by defense).

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

/// Multiple len reads, no is_empty
#[kani::proof]
fn probe_multi_len_no_isempty() {
    let mut solver = ArraySolver::new();
    let trail_len_before = solver.trail_terms.len();
    let assigns_len_before = solver.assign_terms.len();
    solver.pop();
    assert_eq!(solver.trail_terms.len(), trail_len_before);
    assert_eq!(solver.assign_terms.len(), assigns_len_before);
}

/// Two len reads, single field
#[kani::proof]
fn probe_two_len_trail() {
    let mut solver = ArraySolver::new();
    let before = solver.trail_terms.len();
    solver.pop();
    assert_eq!(solver.trail_terms.len(), before);
}

/// Two len reads, single field: assign_terms
#[kani::proof]
fn probe_two_len_assigns() {
    let mut solver = ArraySolver::new();
    let before = solver.assign_terms.len();
    solver.pop();
    assert_eq!(solver.assign_terms.len(), before);
}
