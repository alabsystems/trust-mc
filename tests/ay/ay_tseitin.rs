// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-expect: PROOF
//
//! AY dogfooding: tseitin.rs verification (partial)
//!
//! This test mirrors SOME Kani proofs from ay-core/src/tseitin.rs.
//! Only literal-only proofs work; Vec-based proofs fail due to
//! missing allocator support (#912, #948).
//!
//! Part of #915 - AY dogfooding execution
//!
//! ## Limitation
//!
//! The AY backend does not support heap allocation (Vec, Box).
//! CnfClause proofs use Vec<i32> internally and therefore fail with:
//!   "Call terminator: std::alloc::Allocator::allocate"
//!
//! These will become testable when HashMap/BigInt support (#471, #470)
//! is implemented as part of Phase 5.

/// CNF literal type (DIMACS-style signed integer)
type CnfLit = i32;

// ============================================================================
// trust_mc Verification Harnesses (literal operations only)
// ============================================================================

/// Double negation identity: -(-lit) == lit
#[kani::proof]
fn proof_literal_double_negation() {
    let lit: CnfLit = kani::any();
    kani::assume(lit != 0); // DIMACS literals are non-zero
    kani::assume(lit != i32::MIN); // Avoid overflow on negation

    let negated = -lit;
    let double_negated = -negated;

    assert!(double_negated == lit);
}

/// Positive literal negation produces negative
#[kani::proof]
fn proof_positive_literal_negation_is_negative() {
    let lit: CnfLit = kani::any();
    kani::assume(lit > 0);

    let negated = -lit;

    assert!(negated < 0);
}

// ============================================================================
// NOT TESTABLE: CnfClause proofs require Vec allocation
// ============================================================================
//
// The following proofs from ay-core/tseitin.rs cannot be tested yet:
// - proof_non_empty_clause_not_empty (uses CnfClause::unit -> vec!)
// - proof_empty_clause_is_empty (uses CnfClause::new -> Vec)
// - proof_binary_clause_has_two_literals (uses CnfClause::binary -> vec!)
// - proof_ternary_clause_has_three_literals (uses CnfClause::ternary -> vec!)
// - proof_fresh_var_monotonic (uses TseitinState with BTreeMap)
//
// Tracked in: #912 (generic type issue), #471/#470 (Phase 5 targets)
