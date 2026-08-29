// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: UNKNOWN
// kani-expect: probe_pop_full=PROOF
// kani-expect: probe_pop_two_len=PROOF
// NOTE: probe_pop_two_len was PROOF at ay 417854b7, regressed to UNKNOWN at ay 8a4a9bcc2 (false proof caught by defense).
// NOTE: probe_pop_five_len was PROOF at ay 417854b7, regressed to UNKNOWN at ay 8a4a9bcc2 (false proof caught by defense).

type TermId = u32;

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

/// Two len assertions.
#[kani::proof]
fn probe_pop_two_len() {
    let mut solver = ArraySolver::new();
    let trail_before = solver.trail_terms.len();
    let assign_before = solver.assign_terms.len();
    solver.pop();
    assert_eq!(solver.trail_terms.len(), trail_before);
    assert_eq!(solver.assign_terms.len(), assign_before);
}

/// Five len assertions (no is_empty).
#[kani::proof]
fn probe_pop_five_len() {
    let mut solver = ArraySolver::new();
    let trail_before = solver.trail_terms.len();
    let assign_before = solver.assign_terms.len();
    solver.pop();
    assert_eq!(solver.trail_terms.len(), trail_before);
    assert_eq!(solver.trail_prev_present.len(), trail_before);
    assert_eq!(solver.trail_prev_values.len(), trail_before);
    assert_eq!(solver.assign_terms.len(), assign_before);
    assert_eq!(solver.assign_values.len(), assign_before);
}

/// Five len + is_empty (full pop_empty_is_safe).
#[kani::proof]
fn probe_pop_full() {
    let mut solver = ArraySolver::new();
    let trail_before = solver.trail_terms.len();
    let assign_before = solver.assign_terms.len();
    solver.pop();
    assert_eq!(solver.trail_terms.len(), trail_before);
    assert_eq!(solver.trail_prev_present.len(), trail_before);
    assert_eq!(solver.trail_prev_values.len(), trail_before);
    assert_eq!(solver.assign_terms.len(), assign_before);
    assert_eq!(solver.assign_values.len(), assign_before);
    assert!(solver.scopes.is_empty());
}
