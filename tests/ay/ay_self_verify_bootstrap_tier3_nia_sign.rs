// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: UNKNOWN
// kani-expect: ay_nia_asserted_truncation=PROOF
// kani-expect: ay_nia_scope_marker_tracking=PROOF
// kani-expect: ay_nia_scope_nested_lifo=PROOF
// kani-expect: ay_nia_scope_pop_empty_safe=PROOF
// kani-expect: ay_nia_scope_push_pop_restores=PROOF
// kani-expect: ay_nia_sign_contradicts_negative_constraint=PROOF
// kani-expect: ay_nia_sign_contradicts_nonnegative_constraint=PROOF
// kani-expect: ay_nia_sign_contradicts_nonpositive_constraint=PROOF
// kani-expect: ay_nia_sign_contradicts_positive_constraint=PROOF
// kani-expect: ay_nia_sign_contradicts_zero_constraint=PROOF
// kani-expect: ay_nia_sign_from_constraints_definite=PROOF
// kani-expect: ay_nia_sign_from_constraints_none=PROOF
// NOTE: All 12 sign/scope harnesses are clean CHC PROOF at ay 733ba8cd.

//! AY self-verification bootstrap Tier 3: NIA sign constraint harnesses.
//!
//! These harnesses mirror the `sign_contradicts` and `sign_from_constraints`
//! `#[kani::proof]` suites from `ay-theories/nia/src/lib.rs`. They exercise
//! the sign-reasoning logic used in nonlinear integer arithmetic.
//!
//! Uses integer-coded constraint types instead of a 5-variant enum to avoid
//! the CHC 3+-variant discriminant collapse (#3521/#3242).
//!
//! Part of #3766: Run AY's 258 Kani harnesses through trust_mc.

// SignConstraint encoded as u8:
//   0 = Positive, 1 = Negative, 2 = Zero, 3 = NonNegative, 4 = NonPositive
const POSITIVE: u8 = 0;
const NEGATIVE: u8 = 1;
const ZERO: u8 = 2;
const NONNEGATIVE: u8 = 3;
const NONPOSITIVE: u8 = 4;

/// Model of NiaSolver::sign_contradicts.
///
/// Returns true when the constraint is violated by the given sign value:
/// - sign = 1 means positive, sign = -1 means negative, sign = 0 means zero.
fn sign_contradicts(constraint: u8, sign: i8) -> bool {
    if constraint == POSITIVE {
        sign <= 0
    } else if constraint == NEGATIVE {
        sign >= 0
    } else if constraint == ZERO {
        sign != 0
    } else if constraint == NONNEGATIVE {
        sign < 0
    } else {
        // NONPOSITIVE
        sign > 0
    }
}

/// Model of NiaSolver::sign_from_constraints.
///
/// Returns the sign value for definite constraints, or -2 as sentinel for None.
fn sign_from_constraints(has_constraints: bool, constraint: u8) -> i8 {
    if !has_constraints {
        return -2; // sentinel: None
    }
    if constraint == POSITIVE {
        1
    } else if constraint == NEGATIVE {
        -1
    } else if constraint == ZERO {
        0
    } else {
        -2 // sentinel: None (NonNegative/NonPositive are indefinite)
    }
}

/// Port of ay::nia::proof_sign_contradicts_negative_constraint
#[kani::proof]
fn ay_nia_sign_contradicts_negative_constraint() {
    assert!(sign_contradicts(NEGATIVE, 0), "Negative vs 0");
    assert!(sign_contradicts(NEGATIVE, 1), "Negative vs 1");
    assert!(!sign_contradicts(NEGATIVE, -1), "Negative vs -1 (ok)");
}

/// Port of ay::nia::proof_sign_contradicts_zero_constraint
#[kani::proof]
fn ay_nia_sign_contradicts_zero_constraint() {
    assert!(sign_contradicts(ZERO, 1), "Zero vs 1");
    assert!(sign_contradicts(ZERO, -1), "Zero vs -1");
    assert!(!sign_contradicts(ZERO, 0), "Zero vs 0 (ok)");
}

/// Port of ay::nia::proof_sign_contradicts_nonnegative_constraint
#[kani::proof]
fn ay_nia_sign_contradicts_nonnegative_constraint() {
    assert!(sign_contradicts(NONNEGATIVE, -1), "NonNeg vs -1");
    assert!(!sign_contradicts(NONNEGATIVE, 0), "NonNeg vs 0 (ok)");
    assert!(!sign_contradicts(NONNEGATIVE, 1), "NonNeg vs 1 (ok)");
}

/// Port of ay::nia::proof_sign_contradicts_nonpositive_constraint
#[kani::proof]
fn ay_nia_sign_contradicts_nonpositive_constraint() {
    assert!(sign_contradicts(NONPOSITIVE, 1), "NonPos vs 1");
    assert!(!sign_contradicts(NONPOSITIVE, 0), "NonPos vs 0 (ok)");
    assert!(!sign_contradicts(NONPOSITIVE, -1), "NonPos vs -1 (ok)");
}

/// Port of ay::nia::proof_sign_contradicts_positive_constraint
#[kani::proof]
fn ay_nia_sign_contradicts_positive_constraint() {
    assert!(sign_contradicts(POSITIVE, 0), "Positive vs 0");
    assert!(sign_contradicts(POSITIVE, -1), "Positive vs -1");
    assert!(!sign_contradicts(POSITIVE, 1), "Positive vs 1 (ok)");
}

/// Port of ay::nia::proof_sign_from_constraints_definite
#[kani::proof]
fn ay_nia_sign_from_constraints_definite() {
    assert!(sign_from_constraints(true, POSITIVE) == 1, "Positive -> 1");
    assert!(sign_from_constraints(true, NEGATIVE) == -1, "Negative -> -1");
    assert!(sign_from_constraints(true, ZERO) == 0, "Zero -> 0");
    assert!(sign_from_constraints(true, NONNEGATIVE) == -2, "NonNegative -> None");
    assert!(sign_from_constraints(true, NONPOSITIVE) == -2, "NonPositive -> None");
}

/// Port of ay::nia::proof_sign_from_constraints_none
#[kani::proof]
fn ay_nia_sign_from_constraints_none() {
    assert!(sign_from_constraints(false, 0) == -2, "None -> None");
}

// ========================================================================
// NIA scope management harnesses (ay-theories/nia/src/lib.rs)
// ========================================================================

/// Standalone scope model: bounded Vec<usize> markers modeled with u8 slots.
/// Mirrors the NiaSolver scopes/asserted fields.
struct NiaScopeModel {
    scope0: u8,
    scope1: u8,
    scope2: u8,
    scope_len: u8,
    asserted_len: u8,
}

impl NiaScopeModel {
    fn new() -> Self {
        Self { scope0: 0, scope1: 0, scope2: 0, scope_len: 0, asserted_len: 0 }
    }

    fn push(&mut self) {
        match self.scope_len {
            0 => {
                self.scope0 = self.asserted_len;
                self.scope_len = 1;
            }
            1 => {
                self.scope1 = self.asserted_len;
                self.scope_len = 2;
            }
            2 => {
                self.scope2 = self.asserted_len;
                self.scope_len = 3;
            }
            _ => {}
        }
    }

    fn pop(&mut self) -> Option<u8> {
        match self.scope_len {
            3 => {
                self.scope_len = 2;
                Some(self.scope2)
            }
            2 => {
                self.scope_len = 1;
                Some(self.scope1)
            }
            1 => {
                self.scope_len = 0;
                Some(self.scope0)
            }
            _ => None,
        }
    }
}

/// Port of ay::nia::proof_scope_marker_tracking
#[kani::proof]
fn ay_nia_scope_marker_tracking() {
    let mut model = NiaScopeModel::new();
    assert!(model.scope_len == 0, "Initially no scopes");

    model.push();
    assert!(model.scope_len == 1, "Push adds scope marker");

    model.asserted_len = 3;
    model.push();
    assert!(model.scope_len == 2, "Second push adds scope marker");
    assert!(model.scope1 == 3, "Marker captures correct position");

    if let Some(mark) = model.pop() {
        assert!(mark == 3, "Pop returns correct marker");
    }
    assert!(model.scope_len == 1, "Scope depth restored");
}

/// Port of ay::nia::proof_scope_pop_empty_safe
#[kani::proof]
fn ay_nia_scope_pop_empty_safe() {
    let mut model = NiaScopeModel::new();
    let result = model.pop();
    assert!(result.is_none(), "Pop on empty returns None");
    assert!(model.scope_len == 0, "Scopes still empty");

    let result2 = model.pop();
    assert!(result2.is_none(), "Second pop also returns None");
}

/// Port of ay::nia::proof_scope_push_pop_restores
#[kani::proof]
fn ay_nia_scope_push_pop_restores() {
    let mut model = NiaScopeModel::new();
    let initial = model.scope_len;

    model.push();
    model.pop();

    assert!(model.scope_len == initial, "push/pop restores depth");
}

/// Port of ay::nia::proof_scope_nested_lifo
/// Uses if-let destructuring to avoid Option equality encoding gap.
#[kani::proof]
fn ay_nia_scope_nested_lifo() {
    let mut model = NiaScopeModel::new();

    model.asserted_len = 0;
    model.push();
    model.asserted_len = 5;
    model.push();
    model.asserted_len = 10;
    model.push();
    assert!(model.scope_len == 3, "Three pushes");

    if let Some(v) = model.pop() {
        assert!(v == 10, "First pop returns 10");
    } else {
        assert!(false, "First pop must succeed");
    }
    if let Some(v) = model.pop() {
        assert!(v == 5, "Second pop returns 5");
    } else {
        assert!(false, "Second pop must succeed");
    }
    if let Some(v) = model.pop() {
        assert!(v == 0, "Third pop returns 0");
    } else {
        assert!(false, "Third pop must succeed");
    }
    assert!(model.scope_len == 0, "All pops complete");
}

/// Port of ay::nia::proof_asserted_truncation
#[kani::proof]
fn ay_nia_asserted_truncation() {
    let mut model = NiaScopeModel::new();

    model.asserted_len = 0;
    model.push(); // marker = 0

    model.asserted_len = 2;
    model.push(); // marker = 2

    model.asserted_len = 3;
    assert!(model.asserted_len == 3, "Three assertions total");

    if let Some(mark) = model.pop() {
        assert!(mark == 2, "First pop returns second scope marker");
        model.asserted_len = mark;
    } else {
        assert!(false, "First pop must succeed");
    }
    assert!(model.asserted_len == 2, "Popped back to 2 assertions");

    if let Some(mark) = model.pop() {
        assert!(mark == 0, "Second pop returns first scope marker");
        model.asserted_len = mark;
    } else {
        assert!(false, "Second pop must succeed");
    }
    assert!(model.asserted_len == 0, "Popped back to 0 assertions");
}
