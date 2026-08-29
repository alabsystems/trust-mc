// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: PROOF

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
}

#[kani::proof]
fn new_f0() { let s = ArraySolver::new(); assert_eq!(s.assign_terms.len(), 0); }
#[kani::proof]
fn new_f1() { let s = ArraySolver::new(); assert_eq!(s.assign_values.len(), 0); }
#[kani::proof]
fn new_f2() { let s = ArraySolver::new(); assert_eq!(s.trail_terms.len(), 0); }
#[kani::proof]
fn new_f3() { let s = ArraySolver::new(); assert_eq!(s.trail_prev_present.len(), 0); }
#[kani::proof]
fn new_f4() { let s = ArraySolver::new(); assert_eq!(s.trail_prev_values.len(), 0); }
#[kani::proof]
fn new_f5() { let s = ArraySolver::new(); assert_eq!(s.scopes.len(), 0); }
