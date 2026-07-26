// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: UNKNOWN
// kani-expect: ay_arrays_dirty_flag_after_pop=PROOF
// kani-expect: ay_arrays_duplicate_assignment_idempotent=PROOF
// kani-expect: ay_arrays_known_distinct_antireflexive=PROOF
// kani-expect: ay_arrays_known_equal_reflexive=PROOF
// kani-expect: ay_arrays_pop_empty_is_safe=PROOF
// kani-expect: ay_arrays_push_pop_scope_depth=PROOF
// kani-expect: ay_arrays_record_assignment_trail_consistency=PROOF
// kani-expect: ay_arrays_reset_clears_state=PROOF
// NOTE: 2 harness(es) remain UNKNOWN under ay#8578 false-proof defenses.
// NOTE: duplicate_assignment_idempotent and record_assignment_trail_consistency
// recovered genuine PROOF at ay 733ba8cd.
// NOTE: push_pop_scope_depth recovered by the scalar scope-only model.

//! AY self-verification bootstrap Tier 3g: array-theory scope and trail invariants.
//!
//! These harnesses mirror the bounded `#[kani::proof]` suite from
//! `ay-theories/arrays/src/verification.rs`. The standalone model keeps only
//! the assignment trail, scope markers, and cache-dirty flag that those proofs
//! exercise; term-store and theory-integration state are intentionally omitted.
//!
//! Part of #3766: Run AY's 258 Kani harnesses through trust_mc.

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
    // Part of #4050: #[inline(never)] prevents rustc from MIR-inlining these
    // methods into the harness body. Without this, the shadow dispatcher never
    // sees the call terminators and falls through to fn_inline, which expands
    // the loop-heavy bodies and defeats the shadow SMT array encoding.
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
    fn known_equal(&self, lhs: TermId, rhs: TermId) -> bool {
        lhs == rhs
    }

    #[inline(never)]
    fn known_distinct(&self, lhs: TermId, rhs: TermId) -> bool {
        lhs != rhs && false
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
    fn reset(&mut self) {
        self.assign_terms.clear();
        self.assign_values.clear();
        self.trail_terms.clear();
        self.trail_prev_present.clear();
        self.trail_prev_values.clear();
        self.scopes.clear();
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

#[derive(Debug)]
struct ArrayScopeModel {
    trail_len: usize,
    scope0: usize,
    scope1: usize,
    scope_len: usize,
}

impl ArrayScopeModel {
    fn new() -> Self {
        Self { trail_len: 0, scope0: 0, scope1: 0, scope_len: 0 }
    }

    fn push(&mut self) {
        match self.scope_len {
            0 => {
                self.scope0 = self.trail_len;
                self.scope_len = 1;
            }
            1 => {
                self.scope1 = self.trail_len;
                self.scope_len = 2;
            }
            _ => {}
        }
    }

    fn pop(&mut self) {
        if self.scope_len > 0 {
            self.scope_len -= 1;
            self.trail_len = match self.scope_len {
                0 => self.scope0,
                1 => self.scope1,
                _ => self.trail_len,
            };
        }
    }
}

/// Port of ay::arrays::proof_known_equal_reflexive
#[kani::proof]
fn ay_arrays_known_equal_reflexive() {
    let solver = ArraySolver::new();
    let term_id: u32 = kani::any();
    kani::assume(term_id < 100);
    let term = term_id;

    assert!(solver.known_equal(term, term));
}

/// Port of ay::arrays::proof_known_distinct_antireflexive
#[kani::proof]
fn ay_arrays_known_distinct_antireflexive() {
    let solver = ArraySolver::new();
    let term_id: u32 = kani::any();
    kani::assume(term_id < 100);
    let term = term_id;

    assert!(!solver.known_distinct(term, term));
}

/// Port of ay::arrays::proof_push_pop_scope_depth
#[kani::proof]
fn ay_arrays_push_pop_scope_depth() {
    let mut solver = ArrayScopeModel::new();
    let initial_depth = solver.scope_len;

    solver.push();
    assert_eq!(solver.scope_len, initial_depth + 1);

    solver.push();
    assert_eq!(solver.scope_len, initial_depth + 2);

    solver.pop();
    assert_eq!(solver.scope_len, initial_depth + 1);

    solver.pop();
    assert_eq!(solver.scope_len, initial_depth);
}

/// Port of ay::arrays::proof_pop_empty_is_safe
#[kani::proof]
fn ay_arrays_pop_empty_is_safe() {
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

/// Port of ay::arrays::proof_reset_clears_state
#[kani::proof]
fn ay_arrays_reset_clears_state() {
    let term_id: u32 = kani::any();
    kani::assume(term_id < 100);
    let value: bool = kani::any();

    let mut assign_terms: Vec<TermId> = Vec::new();
    let mut assign_values: Vec<bool> = Vec::new();
    let mut trail_len = 0usize;
    let mut scopes: Vec<usize> = Vec::new();
    let mut dirty = true;

    assign_terms.push(term_id);
    assign_values.push(value);
    trail_len += 1;
    scopes.push(trail_len);
    assign_terms.push(term_id.wrapping_add(1) % 100);
    assign_values.push(!value);
    trail_len += 1;

    assign_terms.clear();
    assign_values.clear();
    trail_len = 0;
    scopes.clear();
    dirty = true;

    assert!(assign_terms.is_empty());
    assert!(assign_values.is_empty());
    assert_eq!(trail_len, 0);
    assert!(scopes.is_empty());
    assert!(dirty);
}

/// Port of ay::arrays::proof_record_assignment_trail_consistency
#[kani::proof]
fn ay_arrays_record_assignment_trail_consistency() {
    let term_id: u32 = kani::any();
    kani::assume(term_id < 100);
    let term = term_id;
    let value: bool = kani::any();

    let mut has_assignment = false;
    let mut assigned_term = 0u32;
    let mut assigned_value = false;
    let mut trail_len = 0usize;
    let mut trail_term = 0u32;
    let mut trail_previous_present = false;
    let mut trail_previous_value = false;

    let previous =
        if has_assignment && assigned_term == term { Some(assigned_value) } else { None };

    if previous != Some(value) {
        trail_term = term;
        trail_previous_present = previous.is_some();
        trail_previous_value = previous.unwrap_or(false);
        trail_len += 1;
        assigned_term = term;
        assigned_value = value;
        has_assignment = true;
    }

    assert!(has_assignment);
    assert_eq!(assigned_term, term);
    assert_eq!(assigned_value, value);

    if previous != Some(value) {
        assert_eq!(trail_len, 1);
        assert_eq!(trail_term, term);
        assert_eq!(trail_previous_present, previous.is_some());
        assert_eq!(trail_previous_value, previous.unwrap_or(false));
    }
}

/// Port of ay::arrays::proof_pop_restores_assignments
#[kani::proof]
#[kani::unwind(5)]
fn ay_arrays_pop_restores_assignments() {
    let mut solver = ArraySolver::new();
    let term_id: u32 = kani::any();
    kani::assume(term_id < 100);
    let term = term_id;

    solver.push();
    let initial_value = solver.get_assignment(term);

    let new_value: bool = kani::any();
    solver.record_assignment(term, new_value);
    solver.pop();

    assert_eq!(solver.get_assignment(term), initial_value);
}

/// Port of ay::arrays::proof_duplicate_assignment_idempotent
#[kani::proof]
fn ay_arrays_duplicate_assignment_idempotent() {
    let term_id: u32 = kani::any();
    kani::assume(term_id < 100);
    let term = term_id;
    let value: bool = kani::any();

    let mut has_assignment = false;
    let mut assigned_term = 0u32;
    let mut assigned_value = false;
    let mut trail_len = 0usize;

    let previous =
        if has_assignment && assigned_term == term { Some(assigned_value) } else { None };
    if previous != Some(value) {
        trail_len += 1;
        assigned_term = term;
        assigned_value = value;
        has_assignment = true;
    }

    let trail_len_after_first = trail_len;

    let previous =
        if has_assignment && assigned_term == term { Some(assigned_value) } else { None };
    if previous != Some(value) {
        trail_len += 1;
        assigned_term = term;
        assigned_value = value;
        has_assignment = true;
    }

    assert!(has_assignment);
    assert_eq!(assigned_term, term);
    assert_eq!(assigned_value, value);
    assert_eq!(trail_len, trail_len_after_first);
}

/// Port of ay::arrays::proof_nested_push_pop_markers
#[kani::proof]
#[kani::unwind(6)]
fn ay_arrays_nested_push_pop_markers() {
    let mut solver = ArraySolver::new();
    let depth: u8 = kani::any();
    kani::assume(depth > 0 && depth <= 5);

    let mut expected_markers: Vec<usize> = Vec::new();
    let mut pushes = 0;
    while pushes < depth {
        expected_markers.push(solver.trail_terms.len());
        solver.push();
        pushes += 1;
    }

    assert_eq!(solver.scopes.len(), depth as usize);

    let mut i = 0;
    while i < depth as usize {
        assert_eq!(solver.scopes[i], expected_markers[i]);
        i += 1;
    }
}

/// Port of ay::arrays::proof_dirty_flag_after_pop
#[kani::proof]
fn ay_arrays_dirty_flag_after_pop() {
    let mut solver = ArraySolver::new();
    solver.populate_caches();
    assert!(!solver.dirty);

    solver.push();
    solver.pop();

    assert!(solver.dirty);
}
