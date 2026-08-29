// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: UNKNOWN
// kani-expect: probe_push_pop_still_none=PROOF
// kani-expect: probe_record_then_get=PROOF

//! Diagnostic probe: isolate ArraySolver shadow push/pop/get_assignment cycle.
//! Part of #4050: narrow which shadow method is producing the CTREX.

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
    fn get_assignment(&self, term: TermId) -> Option<bool> {
        let mut i = 0;
        while i < self.assign_terms.len() {
            if self.assign_terms[i] == term {
                return Some(self.assign_values[i]);
            }
            i += 1;
        }
        None
    }

    #[inline(never)]
    fn set_assignment(&mut self, term: TermId, value: bool) {
        let mut i = 0;
        while i < self.assign_terms.len() {
            if self.assign_terms[i] == term {
                self.assign_values[i] = value;
                return;
            }
            i += 1;
        }
        self.assign_terms.push(term);
        self.assign_values.push(value);
    }

    #[inline(never)]
    fn remove_assignment(&mut self, term: TermId) {
        let mut i = 0;
        while i < self.assign_terms.len() {
            if self.assign_terms[i] == term {
                let mut j = i;
                while j + 1 < self.assign_terms.len() {
                    self.assign_terms[j] = self.assign_terms[j + 1];
                    self.assign_values[j] = self.assign_values[j + 1];
                    j += 1;
                }
                self.assign_terms.pop();
                self.assign_values.pop();
                return;
            }
            i += 1;
        }
    }

    #[inline(never)]
    fn push(&mut self) {
        self.scopes.push(self.trail_terms.len());
    }

    #[inline(never)]
    fn pop(&mut self) {
        let Some(marker) = self.scopes.pop() else {
            return;
        };

        while self.trail_terms.len() > marker {
            let term = self.trail_terms.pop().unwrap();
            let previous_present = self.trail_prev_present.pop().unwrap();
            let previous_value = self.trail_prev_values.pop().unwrap();
            if previous_present {
                self.set_assignment(term, previous_value);
            } else {
                self.remove_assignment(term);
            }
        }
        self.dirty = true;
    }

    #[inline(never)]
    fn record_assignment(&mut self, term: TermId, value: bool) {
        let previous = self.get_assignment(term);
        if previous == Some(value) {
            return;
        }

        self.trail_terms.push(term);
        self.trail_prev_present.push(previous.is_some());
        self.trail_prev_values.push(previous.unwrap_or(false));
        self.set_assignment(term, value);
    }

    #[inline(never)]
    fn populate_caches(&mut self) {
        self.dirty = false;
    }
}

/// Probe A: get_assignment on fresh solver returns None.
#[kani::proof]
fn probe_get_fresh_returns_none() {
    let solver = ArraySolver::new();
    let term: u32 = kani::any();
    kani::assume(term < 100);
    assert!(solver.get_assignment(term).is_none());
}

/// Probe B: push then pop, get_assignment still None.
#[kani::proof]
fn probe_push_pop_still_none() {
    let mut solver = ArraySolver::new();
    let term: u32 = kani::any();
    kani::assume(term < 100);
    solver.push();
    solver.pop();
    assert!(solver.get_assignment(term).is_none());
}

/// Probe C: record_assignment then get_assignment returns Some.
#[kani::proof]
fn probe_record_then_get() {
    let mut solver = ArraySolver::new();
    let term: u32 = kani::any();
    kani::assume(term < 100);
    let value: bool = kani::any();
    solver.record_assignment(term, value);
    assert_eq!(solver.get_assignment(term), Some(value));
}

/// Probe D: push, record, pop restores None (the core property).
#[kani::proof]
#[kani::unwind(5)]
fn probe_push_record_pop_restores() {
    let mut solver = ArraySolver::new();
    let term: u32 = kani::any();
    kani::assume(term < 100);
    solver.push();
    let initial = solver.get_assignment(term);
    let new_value: bool = kani::any();
    solver.record_assignment(term, new_value);
    solver.pop();
    assert_eq!(solver.get_assignment(term), initial);
}
