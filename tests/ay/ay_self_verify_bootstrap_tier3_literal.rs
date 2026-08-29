// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: UNKNOWN
// kani-expect: literal_encoding_unique=PROOF
// kani-expect: literal_index_consistent=PROOF
// kani-expect: literal_negation_involutive=PROOF
// kani-expect: literal_polarity_distinct=PROOF
// kani-expect: literal_raw_and_variable_accessors_consistent=PROOF
// kani-expect: literal_sign_i8_matches_polarity=PROOF
// kani-expect: literal_variable_roundtrip=PROOF

//! AY self-verification bootstrap Tier 3h: SAT literal encoding invariants.
//!
//! These harnesses mirror the bounded `#[kani::proof]` suite from
//! `ay-sat/src/literal.rs`. The standalone model reproduces the Variable/Literal
//! newtype encoding (var << 1 for positive, (var << 1) | 1 for negative) and
//! verifies involution, roundtrip, uniqueness, polarity, index consistency, and
//! lightweight accessor helpers.
//!
//! Part of #3766: Run AY's 258 Kani harnesses through trust_mc.

/// A variable identifier (newtype over u32)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Variable(u32);

/// A literal (variable with polarity), encoded as:
/// positive = 2*var, negative = 2*var + 1
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Literal(u32);

impl Variable {
    fn new(id: u32) -> Self {
        Self(id)
    }

    fn id(self) -> u32 {
        self.0
    }

    fn index(self) -> usize {
        self.0 as usize
    }
}

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

    fn raw(self) -> u32 {
        self.0
    }

    fn index(self) -> usize {
        self.0 as usize
    }

    fn sign_i8(self) -> i8 {
        if self.is_positive() { 1 } else { -1 }
    }
}

/// Negation is involutive: negating twice returns the original literal
#[kani::proof]
fn literal_negation_involutive() {
    let raw: u32 = kani::any();
    kani::assume(raw < 1_000_000);
    let lit = Literal(raw);
    assert!(lit.negated().negated() == lit);
}

/// Variable roundtrip: creating positive/negative literals preserves variable
#[kani::proof]
fn literal_variable_roundtrip() {
    let var_idx: u32 = kani::any();
    kani::assume(var_idx < 500_000);
    let var = Variable(var_idx);

    let pos = Literal::positive(var);
    let neg = Literal::negative(var);

    assert!(pos.variable().0 == var.0);
    assert!(neg.variable().0 == var.0);
    assert!(pos.is_positive());
    assert!(!neg.is_positive());
}

/// Encoding uniqueness: different variables have different literal encodings
#[kani::proof]
fn literal_encoding_unique() {
    let idx1: u32 = kani::any();
    let idx2: u32 = kani::any();
    kani::assume(idx1 < 500_000);
    kani::assume(idx2 < 500_000);

    let var1 = Variable(idx1);
    let var2 = Variable(idx2);

    let pos1 = Literal::positive(var1);
    let pos2 = Literal::positive(var2);

    // Same encoding implies same variable
    if pos1.0 == pos2.0 {
        assert!(var1.0 == var2.0);
    }
}

/// Positive and negative literals for the same variable are different
#[kani::proof]
fn literal_polarity_distinct() {
    let var_idx: u32 = kani::any();
    kani::assume(var_idx < 500_000);
    let var = Variable(var_idx);

    let pos = Literal::positive(var);
    let neg = Literal::negative(var);

    assert!(pos.0 != neg.0);
    assert!(pos.negated().0 == neg.0);
    assert!(neg.negated().0 == pos.0);
}

/// Index is consistent with encoding
#[kani::proof]
fn literal_index_consistent() {
    let var_idx: u32 = kani::any();
    kani::assume(var_idx < 500_000);
    let var = Variable(var_idx);

    let pos = Literal::positive(var);
    let neg = Literal::negative(var);

    // Indices should be consecutive: pos = 2*var, neg = 2*var + 1
    assert!(pos.index() == (var_idx as usize) * 2);
    assert!(neg.index() == (var_idx as usize) * 2 + 1);
}

/// Raw literal and variable accessors agree with constructor encoding
#[kani::proof]
fn literal_raw_and_variable_accessors_consistent() {
    let var_idx: u32 = kani::any();
    kani::assume(var_idx < 500_000);

    let var = Variable::new(var_idx);
    let pos = Literal::positive(var);
    let neg = Literal::negative(var);

    assert!(var.id() == var_idx);
    assert!(var.index() == var_idx as usize);
    assert!(pos.raw() == var_idx << 1);
    assert!(neg.raw() == (var_idx << 1) | 1);
}

/// Signed polarity accessor agrees with the packed polarity bit
#[kani::proof]
fn literal_sign_i8_matches_polarity() {
    let raw: u32 = kani::any();
    kani::assume(raw < 1_000_000);

    let lit = Literal(raw);

    if lit.is_positive() {
        assert!(lit.sign_i8() == 1);
    } else {
        assert!(lit.sign_i8() == -1);
    }
}
