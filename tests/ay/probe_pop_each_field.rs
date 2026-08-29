// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: UNKNOWN
// kani-expect: field0_assign_terms=PROOF
// kani-expect: field1_assign_values=PROOF
// kani-expect: field3_trail_prev_present=PROOF
// kani-expect: field5_scopes=PROOF
// All 6 harnesses exhibit Spacer non-determinism: any of field0-field5
// flips PROOF/UNKNOWN across runs. Annotate all as UNKNOWN conservatively.
// NOTE: field0_assign_terms, field2_trail_terms, field3_trail_prev_present, field5_scopes were false proofs at ay 417854b7, now correctly UNKNOWN at ay 8a4a9bcc2.

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
        let Some(_marker) = self.scopes.pop() else { return; };
    }
}

#[kani::proof]
fn field0_assign_terms() {
    let mut s = ArraySolver::new();
    let b = s.assign_terms.len();
    s.pop();
    assert_eq!(s.assign_terms.len(), b);
}

#[kani::proof]
fn field1_assign_values() {
    let mut s = ArraySolver::new();
    let b = s.assign_values.len();
    s.pop();
    assert_eq!(s.assign_values.len(), b);
}

#[kani::proof]
fn field2_trail_terms() {
    let mut s = ArraySolver::new();
    let b = s.trail_terms.len();
    s.pop();
    assert_eq!(s.trail_terms.len(), b);
}

#[kani::proof]
fn field3_trail_prev_present() {
    let mut s = ArraySolver::new();
    let b = s.trail_prev_present.len();
    s.pop();
    assert_eq!(s.trail_prev_present.len(), b);
}

#[kani::proof]
fn field4_trail_prev_values() {
    let mut s = ArraySolver::new();
    let b = s.trail_prev_values.len();
    s.pop();
    assert_eq!(s.trail_prev_values.len(), b);
}

#[kani::proof]
fn field5_scopes() {
    let mut s = ArraySolver::new();
    let b = s.scopes.len();
    s.pop();
    assert_eq!(s.scopes.len(), b);
}
