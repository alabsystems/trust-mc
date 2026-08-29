// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: UNKNOWN

//! AY self-verification: conflict analysis harnesses that achieve PROOF.
//!
//! 6 harnesses:
//! - oob_mark_safe: OOB marks are no-ops, only checks len() and count
//! - count_consistent: checks to_clear.len() (Vec::push count), not marks[]
//! - mark_then_check: mark(var) then is_marked(var) — SMT Array store/select
//! - mark_idempotent: mark(var) twice doesn't double-count — store guard
//! - mark_isolation: mark(v1) doesn't affect is_marked(v2) — Array theory
//! - grow_preserves_marks: resize preserves existing data — reserve passthrough
//!
//! The last 4 harnesses were moved from ay_self_verify_conflict_analysis.rs
//! after encoding improvements (struct-embedded Vec store/select via SMT Array
//! theory, Part of #3348) made them provable. Part of #3647.
//!
//! See ay_self_verify_conflict_analysis.rs for the 2 remaining CTREX harnesses
//! that require for-loop iteration encoding (clear_all, clear_then_remark).

/// Sparse-clear marking structure (from ay-sat conflict analyzer)
struct SeenMarks {
    /// Boolean marks indexed by variable
    marks: Vec<bool>,
    /// Indices of currently-set marks (for O(k) clearing)
    to_clear: Vec<usize>,
}

impl SeenMarks {
    fn new(num_vars: usize) -> Self {
        Self { marks: vec![false; num_vars], to_clear: Vec::new() }
    }

    fn num_vars(&self) -> usize {
        self.marks.len()
    }

    /// Mark a variable as seen
    fn mark(&mut self, var: usize) {
        if var < self.marks.len() && !self.marks[var] {
            self.marks[var] = true;
            self.to_clear.push(var);
        }
    }

    /// Check if a variable is marked
    fn is_marked(&self, var: usize) -> bool {
        var < self.marks.len() && self.marks[var]
    }

    /// Count of currently marked variables
    fn count_marked(&self) -> usize {
        self.to_clear.len()
    }

    /// Grow to accommodate more variables
    fn ensure_num_vars(&mut self, num_vars: usize) {
        if self.marks.len() < num_vars {
            self.marks.resize(num_vars, false);
        }
    }
}

// --- PROOF Harnesses ---

/// Out-of-bounds mark is safe (no-op)
/// PROOF: OOB guard (var < marks.len()) makes mark a no-op,
/// so count stays 0 and is_marked returns false. No store/load needed.
#[kani::proof]
fn conflict_oob_mark_safe() {
    let num_vars: usize = kani::any();
    kani::assume(num_vars > 0 && num_vars <= 10);

    let mut marks = SeenMarks::new(num_vars);
    marks.mark(num_vars); // out of bounds
    marks.mark(num_vars + 1); // out of bounds

    assert_eq!(marks.count_marked(), 0);
    assert!(!marks.is_marked(num_vars));
}

/// Count is consistent with actual marks
/// PROOF: count_marked() returns to_clear.len(), and mark() pushes
/// to to_clear for each distinct variable. Doesn't read back marks[].
#[kani::proof]
fn conflict_count_consistent() {
    let num_vars: usize = kani::any();
    kani::assume(num_vars >= 3 && num_vars <= 10);

    let v1: usize = kani::any();
    let v2: usize = kani::any();
    let v3: usize = kani::any();
    kani::assume(v1 < num_vars && v2 < num_vars && v3 < num_vars);
    // All distinct
    kani::assume(v1 != v2 && v1 != v3 && v2 != v3);

    let mut marks = SeenMarks::new(num_vars);
    marks.mark(v1);
    marks.mark(v2);
    marks.mark(v3);

    assert_eq!(marks.count_marked(), 3);
}

// --- PROOF Harnesses: Vec store/load (SMT Array theory) ---
// Moved from ay_self_verify_conflict_analysis.rs — Part of #3647.
// These achieve PROOF because struct-embedded Vec<bool> store→load
// is correctly modeled via SMT Array store/select axioms.

/// Mark-then-check: marking a variable makes it seen
/// PROOF: SMT Array store(data, var, true) followed by select(data', var) = true.
#[kani::proof]
fn conflict_mark_then_check() {
    let num_vars: usize = kani::any();
    kani::assume(num_vars > 0 && num_vars <= 20);
    let var: usize = kani::any();
    kani::assume(var < num_vars);

    let mut marks = SeenMarks::new(num_vars);
    assert!(!marks.is_marked(var));

    marks.mark(var);
    assert!(marks.is_marked(var));
}

/// Mark idempotence: marking twice doesn't double-count
/// PROOF: The !marks[var] guard in mark() prevents the second push.
/// SMT Array select(store(data, var, true), var) = true makes guard false.
#[kani::proof]
fn conflict_mark_idempotent() {
    let num_vars: usize = kani::any();
    kani::assume(num_vars > 0 && num_vars <= 20);
    let var: usize = kani::any();
    kani::assume(var < num_vars);

    let mut marks = SeenMarks::new(num_vars);
    marks.mark(var);
    let count_after_first = marks.count_marked();

    marks.mark(var); // duplicate
    assert_eq!(marks.count_marked(), count_after_first, "Duplicate mark must not increase count");
}

/// Mark isolation: marking one variable doesn't affect others
/// PROOF: SMT Array axiom select(store(a, i, v), j) = select(a, j) when i ≠ j.
#[kani::proof]
fn conflict_mark_isolation() {
    let num_vars: usize = kani::any();
    kani::assume(num_vars >= 2 && num_vars <= 20);
    let v1: usize = kani::any();
    let v2: usize = kani::any();
    kani::assume(v1 < num_vars && v2 < num_vars);
    kani::assume(v1 != v2);

    let mut marks = SeenMarks::new(num_vars);
    marks.mark(v1);

    assert!(marks.is_marked(v1));
    assert!(!marks.is_marked(v2), "Marking v1 must not affect v2");
}

/// Ensure_num_vars: growing preserves existing marks
/// PROOF: Vec::resize is inlined as reserve (preserves data array) + fill writes
/// at indices old_len..new_size (which doesn't include var since var < initial).
/// The SMT Array data expression is preserved through reserve, so
/// select(data', var) = select(store(data, var, true), var) = true.
#[kani::proof]
fn conflict_grow_preserves_marks() {
    let initial: usize = kani::any();
    kani::assume(initial >= 2 && initial <= 10);
    let var: usize = kani::any();
    kani::assume(var < initial);

    let mut marks = SeenMarks::new(initial);
    marks.mark(var);

    let new_size: usize = kani::any();
    kani::assume(new_size > initial && new_size <= 20);

    marks.ensure_num_vars(new_size);

    // Original mark should still be set
    assert!(marks.is_marked(var));
    assert_eq!(marks.num_vars(), new_size);
}
