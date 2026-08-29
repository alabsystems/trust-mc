// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: UNKNOWN
// kani-expect: proof_literal_double_negation=PROOF
// kani-expect: proof_positive_literal_negation_is_negative=PROOF

//! AY self-verification: Tseitin CNF literal properties
//!
//! These harnesses verify fundamental properties of CNF literals used in
//! ay-core's Tseitin transformation (Boolean formula to CNF conversion).
//!
//! Originally from ay/crates/ay-core/src/tseitin.rs.
//! CnfLit = i32 (DIMACS convention: positive = positive literal, negative = negated).

/// CNF literal type (from ay-core): DIMACS-style signed integer
type CnfLit = i32;

/// A CNF clause (disjunction of literals) (from ay-core)
struct CnfClause(Vec<CnfLit>);

impl CnfClause {
    fn unit(lit: CnfLit) -> Self {
        Self(vec![lit])
    }

    fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    fn literals(&self) -> &[CnfLit] {
        &self.0
    }
}

/// Double negation identity: negate(negate(lit)) == lit
///
/// DIMACS: negation is arithmetic negation (-lit).
/// This is a fundamental algebraic property of the literal encoding.
// PROOF
#[kani::proof]
fn proof_literal_double_negation() {
    let lit: CnfLit = kani::any();
    kani::assume(lit != 0); // DIMACS literals are non-zero
    kani::assume(lit != i32::MIN); // Avoid overflow on negation

    let negated = -lit;
    let double_negated = -negated;

    assert_eq!(double_negated, lit, "Double negation must return original literal");
}

/// Positive literal negation produces negative literal
// PROOF
#[kani::proof]
fn proof_positive_literal_negation_is_negative() {
    let lit: CnfLit = kani::any();
    kani::assume(lit > 0);

    let negated = -lit;

    assert!(negated < 0, "Negating positive literal must produce negative");
}

/// Unit clause is not empty
// CTREX
#[kani::proof]
fn proof_non_empty_clause_not_empty() {
    let lit: CnfLit = kani::any();
    kani::assume(lit != 0);

    let clause = CnfClause::unit(lit);

    assert!(!clause.is_empty(), "Unit clause must not be empty");
    assert_eq!(clause.literals().len(), 1, "Unit clause must have exactly one literal");
}
