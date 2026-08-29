// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: PROOF

//! AY self-verification: SAT literal encoding properties
//!
//! These harnesses verify the correctness of ay-sat's literal encoding.
//! Originally from ay/crates/ay-sat/src/literal.rs — ported to standalone
//! trust_mc compiletest format to demonstrate AY verifying itself through trust_mc.
//!
//! Literal encoding: positive = 2*var, negative = 2*var + 1
//! Variable: u32 newtype. Literal: u32 newtype with bit-packed polarity.

/// A variable identifier (from ay-sat)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Variable(u32);

/// A literal (variable with polarity) (from ay-sat)
///
/// Encoded as: positive literal = 2*var, negative literal = 2*var + 1
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Literal(u32);

impl Literal {
    fn positive(var: Variable) -> Self {
        Self(var.0 << 1)
    }

    fn negative(var: Variable) -> Self {
        Self((var.0 << 1) | 1)
    }

    fn variable(self) -> Variable {
        Variable(self.0 >> 1)
    }

    fn is_positive(self) -> bool {
        (self.0 & 1) == 0
    }

    fn negated(self) -> Self {
        Self(self.0 ^ 1)
    }

    fn index(self) -> usize {
        self.0 as usize
    }
}

/// Negation is involutive: negating twice returns the original literal
// PROOF
#[kani::proof]
fn literal_negation_involutive() {
    let v: u32 = kani::any();
    kani::assume(v < 500_000);
    let lit = Literal(v);
    assert_eq!(lit.negated().negated(), lit);
}

/// Variable roundtrip: creating positive/negative literals preserves variable
// PROOF
#[kani::proof]
fn literal_variable_roundtrip() {
    let v: u32 = kani::any();
    kani::assume(v < 500_000);
    let var = Variable(v);

    let pos = Literal::positive(var);
    let neg = Literal::negative(var);

    assert_eq!(pos.variable(), var);
    assert_eq!(neg.variable(), var);
    assert!(pos.is_positive());
    assert!(!neg.is_positive());
}

/// Encoding uniqueness: different variables have different literal encodings
// PROOF
#[kani::proof]
fn literal_encoding_unique() {
    let v1: u32 = kani::any();
    let v2: u32 = kani::any();
    kani::assume(v1 < 500_000 && v2 < 500_000);

    let pos1 = Literal::positive(Variable(v1));
    let pos2 = Literal::positive(Variable(v2));

    // Same encoding implies same variable
    if pos1.0 == pos2.0 {
        assert_eq!(v1, v2);
    }
}

/// Positive and negative literals for the same variable are different
// PROOF
#[kani::proof]
fn literal_polarity_distinct() {
    let v: u32 = kani::any();
    kani::assume(v < 500_000);
    let var = Variable(v);

    let pos = Literal::positive(var);
    let neg = Literal::negative(var);

    assert!(pos != neg);
    assert_eq!(pos.negated(), neg);
    assert_eq!(neg.negated(), pos);
}

/// Index is consistent with encoding
// PROOF
#[kani::proof]
fn literal_index_consistent() {
    let v: u32 = kani::any();
    kani::assume(v < 500_000);
    let var = Variable(v);

    let pos = Literal::positive(var);
    let neg = Literal::negative(var);

    // Indices should be consecutive: pos = 2*var, neg = 2*var + 1
    assert_eq!(pos.index(), (v as usize) * 2);
    assert_eq!(neg.index(), (v as usize) * 2 + 1);
}
