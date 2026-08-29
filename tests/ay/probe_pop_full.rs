// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: PROOF
// Spacer non-determinism: flips PROOF/UNKNOWN across runs.

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
}

/// Exactly mirrors ay_arrays_pop_empty_is_safe
#[kani::proof]
fn probe_pop_empty_full() {
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
