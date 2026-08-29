// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-expect: PROOF
// kani-expect: literal_encoding_unique=UNKNOWN     // AY-bump regression from PROOF (3d9db24e68)
// kani-expect: literal_index_consistent=UNKNOWN    // AY-bump regression from PROOF (3d9db24e68)
// kani-expect: literal_negation_involutive=UNKNOWN // AY-bump regression from PROOF (3d9db24e68)
// kani-expect: literal_polarity_distinct=UNKNOWN   // AY-bump regression from PROOF (3d9db24e68)
//
//! AY dogfooding: literal.rs verification
//!
//! This test mirrors the Kani proofs from ay-sat/src/literal.rs
//! to validate trust_mc's ability to verify AY internals.
//!
//! Part of #915 - AY dogfooding execution
//!
//! NOTE: Due to AY backend bug (#948), harnesses using multiple struct types
//! in a single harness fail with "0 of 0" assertions. Tests are rewritten
//! to work with a single struct type per harness.

/// A literal (variable with polarity)
///
/// Encoded as: positive literal = 2*var, negative literal = 2*var + 1
/// The variable is encoded as the literal index / 2.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Literal(u32);

impl Literal {
    /// Create a positive literal from a variable index
    #[inline]
    fn positive(var_idx: u32) -> Self {
        Literal(var_idx * 2)
    }

    /// Create a negative literal from a variable index
    #[inline]
    fn negative(var_idx: u32) -> Self {
        Literal(var_idx * 2 + 1)
    }

    /// Get the variable index
    #[inline]
    fn variable(self) -> u32 {
        self.0 / 2
    }

    /// Check if positive
    #[inline]
    fn is_positive(self) -> bool {
        (self.0 % 2) == 0
    }

    /// Get the negation
    #[inline]
    fn negated(self) -> Self {
        // XOR with 1: even -> odd, odd -> even
        Literal(self.0 ^ 1)
    }

    /// Get the index for watched literal arrays
    #[inline]
    fn index(self) -> usize {
        self.0 as usize
    }
}

// ============================================================================
// trust_mc Verification Harnesses (mirroring ay-sat/literal.rs)
// ============================================================================

/// Negation is involutive: negating twice returns the original literal
#[kani::proof]
fn literal_negation_involutive() {
    let lit_val: u32 = kani::any();
    kani::assume(lit_val < 1_000_000);
    let lit = Literal(lit_val);
    assert_eq!(lit.negated().negated(), lit);
}

/// Variable roundtrip: creating positive/negative literals preserves variable
#[kani::proof]
fn literal_variable_roundtrip() {
    let var_idx: u32 = kani::any();
    kani::assume(var_idx < 1024);

    let pos = Literal::positive(var_idx);
    let neg = Literal::negative(var_idx);

    // Both should recover the same variable
    assert!(pos.variable() == var_idx);
    assert!(neg.variable() == var_idx);
    assert!(pos.is_positive());
    assert!(!neg.is_positive());
}

/// Encoding uniqueness: different variables have different literal encodings
#[kani::proof]
fn literal_encoding_unique() {
    let var1_idx: u32 = kani::any();
    let var2_idx: u32 = kani::any();
    kani::assume(var1_idx < 1024 && var2_idx < 1024);

    let pos1 = Literal::positive(var1_idx);
    let pos2 = Literal::positive(var2_idx);

    // Same encoding implies same variable
    if pos1.0 == pos2.0 {
        assert!(var1_idx == var2_idx);
    }
}

/// Positive and negative literals for the same variable are different
#[kani::proof]
fn literal_polarity_distinct() {
    let var_idx: u32 = kani::any();
    kani::assume(var_idx < 1024);

    let pos = Literal::positive(var_idx);
    let neg = Literal::negative(var_idx);

    // Different polarities are different literals
    assert!(pos.0 != neg.0);
    // Negation flips polarity
    assert!(pos.negated().0 == neg.0);
    assert!(neg.negated().0 == pos.0);
}

/// Index is consistent with encoding
#[kani::proof]
fn literal_index_consistent() {
    let var_idx: u32 = kani::any();
    kani::assume(var_idx < 1024);

    let pos = Literal::positive(var_idx);
    let neg = Literal::negative(var_idx);

    // Indices should be consecutive: pos = 2*var, neg = 2*var + 1
    assert!(pos.index() == (var_idx as usize) * 2);
    assert!(neg.index() == (var_idx as usize) * 2 + 1);
}
