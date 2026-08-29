// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: UNKNOWN
// kani-expect: probe_pop_assert_len=UNKNOWN
// NOTE: current CHC output leaves the compared Vec lengths unconstrained; keep
// this UNKNOWN until the encoder makes Vec::new() length facts explicit.
// kani-expect: probe_pop_dirty=PROOF
// kani-expect: probe_pop_noop=PROOF
// kani-expect: probe_pop_read_len=PROOF

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

/// Minimal: new() + pop(), no assertions at all — just check no crash.
#[kani::proof]
fn probe_pop_noop() {
    let mut solver = ArraySolver::new();
    solver.pop();
}

/// new() + pop() + assert dirty is true.
#[kani::proof]
fn probe_pop_dirty() {
    let mut solver = ArraySolver::new();
    solver.pop();
    assert!(solver.dirty);
}

/// new() + read one len + pop() + read same len + no comparison.
#[kani::proof]
fn probe_pop_read_len() {
    let mut solver = ArraySolver::new();
    let _before = solver.trail_terms.len();
    solver.pop();
    let _after = solver.trail_terms.len();
}

/// new() + read len + pop() + assert len unchanged.
#[kani::proof]
fn probe_pop_assert_len() {
    let mut solver = ArraySolver::new();
    let before = solver.trail_terms.len();
    solver.pop();
    let after = solver.trail_terms.len();
    assert_eq!(before, after);
}
