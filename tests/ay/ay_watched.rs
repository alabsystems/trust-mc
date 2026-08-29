// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-expect: UNKNOWN
// kani-flags: --ay-chc-track=mem
//
//! AY dogfooding: watched.rs verification (partial)
//!
//! This test mirrors SOME Kani proofs from ay-sat/src/watched.rs.
//! Only struct-level proofs work; WatchedLists proofs fail due to
//! missing Vec allocation support.
//!
//! Part of #915 - AY dogfooding execution
//!
//! ## Limitation
//!
//! Proofs requiring WatchedLists (Vec<Vec<Watcher>>) cannot be tested yet:
//! - `watch_add_increases_count` - uses WatchedLists::new (Vec)
//! - `watch_clear_resets_counts` - uses WatchedLists (Vec)
//!
//! These will become testable when heap allocation support is implemented.

/// A variable identifier (mirrors ay-sat Variable)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Variable(u32);

/// A literal (variable with polarity)
///
/// Encoded as: positive literal = 2*var, negative literal = 2*var + 1
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Literal(u32);

impl Literal {
    /// Create a positive literal
    #[inline]
    fn positive(var: Variable) -> Self {
        Literal(var.0 << 1)
    }

    /// Create a negative literal
    #[inline]
    fn negative(var: Variable) -> Self {
        Literal((var.0 << 1) | 1)
    }

    /// Get the index for watched literal arrays
    #[inline]
    fn index(self) -> usize {
        self.0 as usize
    }
}

/// Index of a clause in the clause database
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ClauseRef(u32);

/// A watcher entry (8 bytes)
///
/// For binary clauses: `blocker` stores the other literal (not just a hint)
/// For longer clauses: `blocker` is a hint for early satisfaction check
///
/// The high bit of `clause` indicates whether this is a binary clause.
#[derive(Debug, Clone, Copy)]
struct Watcher {
    /// The clause being watched. High bit set if this is a binary clause.
    clause: ClauseRef,
    /// For binary clauses: the other literal in the clause
    /// For non-binary clauses: blocker literal for faster filtering
    blocker: Literal,
}

impl Watcher {
    /// High bit flag for binary clauses
    const BINARY_FLAG: u32 = 0x8000_0000;

    /// Create a watcher for a binary clause
    #[inline]
    fn binary(clause: ClauseRef, other_lit: Literal) -> Self {
        Watcher { clause: ClauseRef(clause.0 | Self::BINARY_FLAG), blocker: other_lit }
    }

    /// Create a watcher for a non-binary clause (3+ literals)
    #[inline]
    fn new(clause: ClauseRef, blocker: Literal) -> Self {
        Watcher { clause, blocker }
    }

    /// Check if this is a binary clause watcher
    #[inline]
    fn is_binary(&self) -> bool {
        self.clause.0 & Self::BINARY_FLAG != 0
    }

    /// Get the clause reference (strips binary flag)
    #[inline]
    fn clause_ref(&self) -> ClauseRef {
        ClauseRef(self.clause.0 & !Self::BINARY_FLAG)
    }

    /// Get the blocker/other literal
    #[inline]
    fn blocker(&self) -> Literal {
        self.blocker
    }

    /// Set the blocker (for updating when clause becomes satisfied)
    #[inline]
    fn set_blocker(&mut self, lit: Literal) {
        self.blocker = lit;
    }
}

// ============================================================================
// trust_mc Verification Harnesses (mirroring ay-sat/watched.rs)
// ============================================================================

/// Watcher struct preserves its fields correctly (non-binary)
#[kani::proof]
fn watcher_fields_preserved() {
    let clause_val: u32 = kani::any();
    let blocker_val: u32 = kani::any();

    // Bound to prevent overflow and avoid binary flag collision
    kani::assume(clause_val < 1000);
    kani::assume(blocker_val < 1000);

    let clause = ClauseRef(clause_val);
    let blocker = Literal(blocker_val);
    let watcher = Watcher::new(clause, blocker);

    // Fields are preserved
    assert!(watcher.clause_ref() == clause);
    assert!(watcher.blocker() == blocker);
    assert!(!watcher.is_binary());
}

/// Binary watcher preserves its fields correctly
#[kani::proof]
fn binary_watcher_fields_preserved() {
    let clause_val: u32 = kani::any();
    let other_lit_val: u32 = kani::any();

    // Bound to prevent overflow
    kani::assume(clause_val < 1000);
    kani::assume(other_lit_val < 1000);

    let clause = ClauseRef(clause_val);
    let other_lit = Literal(other_lit_val);
    let watcher = Watcher::binary(clause, other_lit);

    // Fields are preserved, binary flag is set
    assert!(watcher.clause_ref() == clause);
    assert!(watcher.blocker() == other_lit);
    assert!(watcher.is_binary());
}

/// ClauseRef is correctly identified
#[kani::proof]
fn clause_ref_equality() {
    let a_val: u32 = kani::any();
    let b_val: u32 = kani::any();

    kani::assume(a_val < 1000 && b_val < 1000);

    let a = ClauseRef(a_val);
    let b = ClauseRef(b_val);

    // Equality is based on inner value
    if a.0 == b.0 {
        assert!(a == b);
    }
    if a != b {
        assert!(a.0 != b.0);
    }
}

/// Literal index calculation is consistent for watched lists
/// This verifies the watched list indexing scheme
///
/// NOTE: Split into separate harnesses to work around #948 (multiple struct types issue)
#[kani::proof]
fn literal_index_positive_negative_distinct() {
    let var_val: u32 = kani::any();
    kani::assume(var_val < 100);

    // Create positive and negative literals directly (avoid Variable struct)
    let pos_lit = Literal(var_val << 1); // Literal::positive
    let neg_lit = Literal((var_val << 1) | 1); // Literal::negative

    // Positive and negative have different indices
    assert!(pos_lit.index() != neg_lit.index());
}

/// Positive literal index is within bounds
#[kani::proof]
fn literal_index_positive_bounded() {
    let var_val: u32 = kani::any();
    kani::assume(var_val < 100);

    let pos_lit = Literal(var_val << 1);
    let expected_max_index = (var_val as usize + 1) * 2;
    assert!(pos_lit.index() < expected_max_index);
}

/// Negative literal index is within bounds
#[kani::proof]
fn literal_index_negative_bounded() {
    let var_val: u32 = kani::any();
    kani::assume(var_val < 100);

    let neg_lit = Literal((var_val << 1) | 1);
    let expected_max_index = (var_val as usize + 1) * 2;
    assert!(neg_lit.index() < expected_max_index);
}

/// Set blocker preserves clause_ref and is_binary flag
#[kani::proof]
fn set_blocker_preserves_fields() {
    let clause_val: u32 = kani::any();
    let blocker1_val: u32 = kani::any();
    let blocker2_val: u32 = kani::any();

    kani::assume(clause_val < 1000);
    kani::assume(blocker1_val < 1000 && blocker2_val < 1000);

    let clause = ClauseRef(clause_val);
    let blocker1 = Literal(blocker1_val);
    let blocker2 = Literal(blocker2_val);

    // Test non-binary watcher
    let mut watcher = Watcher::new(clause, blocker1);
    let original_clause = watcher.clause_ref();
    let original_is_binary = watcher.is_binary();

    watcher.set_blocker(blocker2);

    // clause_ref and is_binary should be unchanged
    assert!(watcher.clause_ref() == original_clause);
    assert!(watcher.is_binary() == original_is_binary);
    // blocker should be updated
    assert!(watcher.blocker() == blocker2);
}

/// Binary watcher set_blocker also preserves fields
#[kani::proof]
fn binary_set_blocker_preserves_fields() {
    let clause_val: u32 = kani::any();
    let blocker1_val: u32 = kani::any();
    let blocker2_val: u32 = kani::any();

    kani::assume(clause_val < 1000);
    kani::assume(blocker1_val < 1000 && blocker2_val < 1000);

    let clause = ClauseRef(clause_val);
    let blocker1 = Literal(blocker1_val);
    let blocker2 = Literal(blocker2_val);

    // Test binary watcher
    let mut watcher = Watcher::binary(clause, blocker1);
    let original_clause = watcher.clause_ref();
    let original_is_binary = watcher.is_binary();

    watcher.set_blocker(blocker2);

    // clause_ref and is_binary should be unchanged
    assert!(watcher.clause_ref() == original_clause);
    assert!(watcher.is_binary() == original_is_binary);
    // blocker should be updated
    assert!(watcher.blocker() == blocker2);
}

// ============================================================================
// NOT TESTABLE: WatchedLists proofs require Vec allocation
// ============================================================================
//
// The following proofs from ay-sat/watched.rs cannot be tested yet:
// - watch_add_increases_count (uses WatchedLists::new -> Vec)
// - watch_clear_resets_counts (uses WatchedLists clear -> Vec)
//
// Tracked in: #912 (heap allocation support)
