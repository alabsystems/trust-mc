// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: conflict_clear_all_resets=UNKNOWN
// kani-expect: conflict_clear_then_remark=UNKNOWN
// NOTE: current AY fails closed here instead of emitting the historical
// spurious ERROR for the Vec-iteration encoding gap. Part of ay#9227.

//! AY self-verification: conflict analysis harnesses that CTREX.
//!
//! 2 harnesses that require for-loop iteration encoding:
//! - clear_all_resets: clear_all() iterates to_clear with a for-loop
//! - clear_then_remark: clear_all() + re-mark cycle
//!
//! These remain UNKNOWN because the CHC encoding doesn't model for-loop
//! iteration over Vec elements (the `for &idx in &self.to_clear` loop in
//! clear_all).
//!
//! See ay_self_verify_conflict_analysis_pass.rs for the 6 PROOF harnesses
//! (oob_mark_safe, count_consistent, mark_then_check, mark_idempotent,
//! mark_isolation, grow_preserves_marks).

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

    /// Clear all marks using sparse-clear (O(k) where k = marked count)
    fn clear_all(&mut self) {
        for &idx in &self.to_clear {
            self.marks[idx] = false;
        }
        self.to_clear.clear();
    }
}

// --- UNKNOWN Harnesses: Vec iteration (for-loop encoding gap) ---

/// Sparse-clear correctness: clear_all resets all marks
/// UNKNOWN: requires Vec iteration encoding (for-loop over to_clear)
#[kani::proof]
fn conflict_clear_all_resets() {
    let num_vars: usize = kani::any();
    kani::assume(num_vars > 0 && num_vars <= 10);

    let mut marks = SeenMarks::new(num_vars);

    // Mark some variables
    let v1: usize = kani::any();
    let v2: usize = kani::any();
    kani::assume(v1 < num_vars && v2 < num_vars);

    marks.mark(v1);
    marks.mark(v2);

    marks.clear_all();

    // All marks must be cleared
    assert!(!marks.is_marked(v1));
    assert!(!marks.is_marked(v2));
    assert_eq!(marks.count_marked(), 0);
}

/// Clear-then-mark cycle: marks work correctly after clearing
/// UNKNOWN: requires Vec iteration encoding (clear_all) + mark-after-clear
#[kani::proof]
fn conflict_clear_then_remark() {
    let num_vars: usize = kani::any();
    kani::assume(num_vars >= 2 && num_vars <= 10);
    let v1: usize = kani::any();
    let v2: usize = kani::any();
    kani::assume(v1 < num_vars && v2 < num_vars);
    kani::assume(v1 != v2);

    let mut marks = SeenMarks::new(num_vars);

    // Cycle 1: mark v1
    marks.mark(v1);
    assert!(marks.is_marked(v1));
    marks.clear_all();
    assert!(!marks.is_marked(v1));

    // Cycle 2: mark v2 (v1 should still be clear)
    marks.mark(v2);
    assert!(marks.is_marked(v2));
    assert!(!marks.is_marked(v1), "Stale mark from cycle 1 must not persist");
}
