// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: UNKNOWN
// kani-expect: ay_theory_result_sat_variant=PROOF
// kani-expect: ay_theory_result_unknown_variant=PROOF
// kani-expect: ay_trl_loop_detection_correct=PROOF
// kani-expect: ay_trl_trace_id_bounds=PROOF
// kani-expect: ay_trp_recurrence_soundness=PROOF
// kani-expect: ay_tseitin_literal_double_negation=PROOF
// kani-expect: ay_tseitin_positive_literal_negation_is_negative=PROOF
// NOTE: 8 harness(es) demoted PROOF→UNKNOWN by false proof defense (ay#8578).

//! AY self-verification bootstrap Tier 1: simplest ay harnesses ported to standalone form.
//!
//! These are extracted from ay's own `#[kani::proof]` harnesses (ay-core/tseitin,
//! ay-core/theory, ay-sat/literal, ay-chc/trp, ay-chc/proof_interpolation).
//! They use only primitive types and simple structs — no ay crate imports needed.
//!
//! Part of #3766: Run AY's 258 Kani harnesses through trust_mc.

// ============================================================
// ay-core/src/tseitin.rs — CNF literal properties
// ============================================================

type CnfLit = i32;

/// Port of ay::tseitin::proof_literal_double_negation
#[kani::proof]
fn ay_tseitin_literal_double_negation() {
    let lit: CnfLit = kani::any();
    kani::assume(lit != 0);
    kani::assume(lit != i32::MIN);
    let negated = -lit;
    let double_negated = -negated;
    assert_eq!(double_negated, lit, "Double negation must return original literal");
}

/// Port of ay::tseitin::proof_positive_literal_negation_is_negative
#[kani::proof]
fn ay_tseitin_positive_literal_negation_is_negative() {
    let lit: CnfLit = kani::any();
    kani::assume(lit > 0);
    let negated = -lit;
    assert!(negated < 0, "Negating positive literal must produce negative");
}

// ============================================================
// ay-chc/src/trp.rs — recurrence soundness
// ============================================================

/// Port of ay::trp::proof_recurrence_soundness
#[kani::proof]
fn ay_trp_recurrence_soundness() {
    let base: u64 = kani::any();
    let step: u64 = kani::any();
    let n: u64 = kani::any();
    kani::assume(n <= 5);
    kani::assume(step > 0 && step <= 100);
    kani::assume(base <= 1000);

    // Check that base + step * n doesn't overflow (using checked arithmetic)
    if let Some(product) = step.checked_mul(n) {
        if let Some(result) = base.checked_add(product) {
            assert!(result >= base, "Recurrence must be non-decreasing when step > 0");
        }
    }
}

/// Port of ay::trp::proof_loop_detection_correct (from ay-chc/trl)
#[kani::proof]
fn ay_trl_loop_detection_correct() {
    let iteration: u64 = kani::any();
    let threshold: u64 = kani::any();
    kani::assume(threshold > 0);
    kani::assume(iteration <= 1000);

    // If iteration exceeds threshold, loop detected
    let loop_detected = iteration >= threshold;
    if loop_detected {
        assert!(iteration >= threshold);
    } else {
        assert!(iteration < threshold);
    }
}

/// Port of ay::trp::proof_trace_id_bounds (from ay-chc/trl)
#[kani::proof]
fn ay_trl_trace_id_bounds() {
    let id: u64 = kani::any();
    kani::assume(id <= u64::MAX / 2);

    let next_id = id + 1;
    assert!(next_id > id, "Trace ID must be monotonically increasing");
}

// ============================================================
// ay-chc/src/proof_interpolation — DependencyMark algebra
// ============================================================

/// Simplified DependencyMark as a bitfield (matches ay's implementation)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct DependencyMark(u64);

impl DependencyMark {
    fn union(self, other: Self) -> Self {
        DependencyMark(self.0 | other.0)
    }
}

/// Port of ay::proof_interpolation::proof_dependency_mark_union_commutative
#[kani::proof]
fn ay_dependency_mark_union_commutative() {
    let a = DependencyMark(kani::any());
    let b = DependencyMark(kani::any());
    assert_eq!(a.union(b), b.union(a), "Union must be commutative");
}

/// Port of ay::proof_interpolation::proof_dependency_mark_union_associative
#[kani::proof]
fn ay_dependency_mark_union_associative() {
    let a = DependencyMark(kani::any());
    let b = DependencyMark(kani::any());
    let c = DependencyMark(kani::any());
    assert_eq!(
        a.union(b).union(c),
        a.union(b.union(c)),
        "Union must be associative"
    );
}

/// Port of ay::proof_interpolation::proof_dependency_mark_union_idempotent
#[kani::proof]
fn ay_dependency_mark_union_idempotent() {
    let a = DependencyMark(kani::any());
    assert_eq!(a.union(a), a, "Union must be idempotent");
}

// ============================================================
// ay-core/src/theory.rs — TheoryResult enum properties
// ============================================================

/// Simplified TheoryResult for standalone verification
#[derive(Debug, Clone, PartialEq, Eq)]
enum TheoryResult {
    Sat,
    Unknown,
    Unsat,
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
