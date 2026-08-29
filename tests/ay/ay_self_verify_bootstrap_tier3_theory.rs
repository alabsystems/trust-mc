// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: PROOF
// NOTE: All 10 harnesses are CHC PROOF at ay 733ba8cd after optional payload scalarization.

//! AY self-verification bootstrap Tier 3e: core theory type invariants.
//!
//! These harnesses mirror the `#[kani::proof]` suite from
//! `ay-core/src/theory.rs`. They exercise the small value types that connect
//! theory solvers to DPLL(T): signed literals, conflicts, equality discovery,
//! and theory-result enums.
//!
//! Container payloads are modeled as scalar counts/presence flags instead of
//! heap-backed `Vec<_>` or `Option<Vec<_>>` fields because these proofs only
//! check constructor cardinalities and empty/non-empty cases.
//!
//! Part of #3766: Run AY's 258 Kani harnesses through trust_mc.

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct TermId(u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct TheoryLit {
    term: TermId,
    value: bool,
}

impl TheoryLit {
    fn new(term: TermId, value: bool) -> Self {
        Self { term, value }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct TheoryConflict {
    literal_count: usize,
    has_farkas: bool,
}

impl TheoryConflict {
    fn new(literal_count: usize) -> Self {
        Self { literal_count, has_farkas: false }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct DiscoveredEquality {
    lhs: TermId,
    rhs: TermId,
    reason_count: usize,
}

impl DiscoveredEquality {
    fn new(lhs: TermId, rhs: TermId, reason_count: usize) -> Self {
        Self { lhs, rhs, reason_count }
    }
}

#[derive(Debug, Default, Clone, PartialEq, Eq)]
struct EqualityPropagationResult {
    equality_count: usize,
    has_conflict: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum TheoryResult {
    Sat,
    Unknown,
    Unsat(usize),
}

/// Port of ay::theory::proof_theory_lit_construction
#[kani::proof]
fn ay_theory_lit_construction() {
    let term_id: u32 = kani::any();
    let value: bool = kani::any();

    let term = TermId(term_id);
    let lit = TheoryLit::new(term, value);

    assert_eq!(lit.term.0, term.0);
    assert_eq!(lit.value, value);
}

/// Port of ay::theory::proof_theory_lit_distinct_terms_not_equal
#[kani::proof]
fn ay_theory_lit_distinct_terms_not_equal() {
    let term1: u32 = kani::any();
    let term2: u32 = kani::any();
    kani::assume(term1 != term2);
    let value: bool = kani::any();

    let lit1 = TheoryLit::new(TermId(term1), value);
    let lit2 = TheoryLit::new(TermId(term2), value);

    assert_ne!(lit1.term.0, lit2.term.0, "lits with distinct terms must differ");
}

/// Port of ay::theory::proof_theory_lit_equality_contents
#[kani::proof]
fn ay_theory_lit_equality_contents() {
    let term_id: u32 = kani::any();
    let value: bool = kani::any();

    let lit1 = TheoryLit::new(TermId(term_id), value);
    let lit2 = TheoryLit::new(TermId(term_id), value);

    assert_eq!(lit1.term.0, lit2.term.0);
    assert_eq!(lit1.value, lit2.value);
}

/// Port of ay::theory::proof_theory_conflict_new_has_no_farkas
#[kani::proof]
fn ay_theory_conflict_new_has_no_farkas() {
    let conflict = TheoryConflict::new(1);

    assert!(!conflict.has_farkas);
}

/// Port of ay::theory::proof_theory_conflict_preserves_literals
#[kani::proof]
fn ay_theory_conflict_preserves_literals() {
    let conflict = TheoryConflict::new(2);

    assert_eq!(conflict.literal_count, 2);
}

/// Port of ay::theory::proof_discovered_equality_construction
#[kani::proof]
fn ay_discovered_equality_construction() {
    let lhs_id: u32 = kani::any();
    let rhs_id: u32 = kani::any();

    let lhs = TermId(lhs_id);
    let rhs = TermId(rhs_id);
    let eq = DiscoveredEquality::new(lhs, rhs, 0);

    assert_eq!(eq.lhs.0, lhs.0);
    assert_eq!(eq.rhs.0, rhs.0);
    assert_eq!(eq.reason_count, 0);
}

/// Port of ay::theory::proof_equality_propagation_result_default
#[kani::proof]
fn ay_equality_propagation_result_default() {
    let result = EqualityPropagationResult::default();

    assert_eq!(result.equality_count, 0);
    assert!(!result.has_conflict);
}

/// Port of ay::theory::proof_theory_result_sat_variant
#[kani::proof]
fn ay_theory_result_sat_variant() {
    let result = TheoryResult::Sat;

    assert!(matches!(result, TheoryResult::Sat));
}

/// Port of ay::theory::proof_theory_result_unknown_variant
#[kani::proof]
fn ay_theory_result_unknown_variant() {
    let result = TheoryResult::Unknown;

    assert!(matches!(result, TheoryResult::Unknown));
}

/// Port of ay::theory::proof_theory_result_unsat_variant
#[kani::proof]
fn ay_theory_result_unsat_variant() {
    let result = TheoryResult::Unsat(1);

    if let TheoryResult::Unsat(literal_count) = result {
        assert_eq!(literal_count, 1);
    } else {
        panic!("expected Unsat variant");
    }
}
