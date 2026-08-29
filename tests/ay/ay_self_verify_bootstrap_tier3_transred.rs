// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: PROOF
// NOTE: 3/3 harnesses are clean CHC PROOF at trust_mc 691ce302c2 / AY 733ba8cd.

//! AY self-verification bootstrap Tier 3: Transred witness validation invariants.
//!
//! Standalone models from:
//! - `ay-sat/src/transred.rs`: is_valid_witness_clause predicates
//!
//! Flat-scalar encoding: Vec replaced with two-slot scalar fields.
//!
//! Source: 3 harnesses total
//! Part of #3766: Run AY's 258 Kani harnesses through trust_mc.

// ========================================================================
// Standalone models of clause DB types
// ========================================================================

const GEN: u32 = 1;

/// Validates the clause-index gates for transitivity witnesses.
fn is_original_clause_slot(clause_idx: u8, clauses_len: u8, original_clause_limit: u8) -> bool {
    clause_idx < clauses_len && clause_idx < original_clause_limit
}

/// Validates the selected clause's witness-shape gates.
fn is_irredundant_binary_not_pending(
    is_empty: bool,
    is_learned: bool,
    len: u8,
    pending_delete: u32,
    generation: u32,
) -> bool {
    !is_empty && !is_learned && len == 2 && pending_delete != generation
}

/// Validates whether one selected two-slot clause can serve as a witness.
fn is_valid_witness_slot(
    clause_idx: u8,
    clauses_len: u8,
    original_clause_limit: u8,
    is_empty: bool,
    is_learned: bool,
    len: u8,
    pending_delete: u32,
    generation: u32,
) -> bool {
    is_original_clause_slot(clause_idx, clauses_len, original_clause_limit)
        && is_irredundant_binary_not_pending(is_empty, is_learned, len, pending_delete, generation)
}

// ========================================================================
// Harnesses
// ========================================================================

/// If one duplicate is marked pending-delete, the sibling duplicate stays valid.
#[kani::proof]
fn proof_transred_run_keeps_one_duplicate_binary_clause() {
    assert!(
        !is_valid_witness_slot(0, 2, 2, false, false, 2, GEN, GEN),
        "removed C0 duplicate must not be a valid witness"
    );
    assert!(
        is_valid_witness_slot(1, 2, 2, false, false, 2, 0, GEN),
        "kept C1 duplicate must remain a valid witness"
    );

    assert!(
        !is_valid_witness_slot(1, 2, 2, false, false, 2, GEN, GEN),
        "removed C1 duplicate must not be a valid witness"
    );
    assert!(
        is_valid_witness_slot(0, 2, 2, false, false, 2, 0, GEN),
        "kept C0 duplicate must remain a valid witness"
    );

    assert!(!is_valid_witness_slot(0, 2, 2, false, false, 2, GEN, GEN));
    assert!(!is_valid_witness_slot(1, 2, 2, false, false, 2, GEN, GEN));
}

/// Pending-delete clauses and out-of-bounds indices are rejected.
#[kani::proof]
fn proof_transred_pending_delete_clause_is_not_valid_witness() {
    // Pending-delete clause must be rejected
    assert!(
        !is_valid_witness_slot(0, 2, 2, false, false, 2, GEN, GEN),
        "pending-delete clause must not be a valid witness"
    );

    // Non-pending-delete clause must be accepted
    assert!(
        is_valid_witness_slot(1, 2, 2, false, false, 2, 0, GEN),
        "non-pending irredundant binary must be a valid witness"
    );

    // Out-of-bounds index must be rejected
    assert!(
        !is_valid_witness_slot(99, 2, 2, false, false, 2, 0, GEN),
        "out-of-bounds index must not be a valid witness"
    );

    // Index beyond original_clause_limit must be rejected
    assert!(
        !is_valid_witness_slot(1, 2, 1, false, false, 2, 0, GEN),
        "clause beyond original_clause_limit must not be a valid witness"
    );
}

/// Duplicate binary clause with pending-delete preserves one witness.
#[kani::proof]
fn proof_transred_duplicate_binary_pending_delete_preserves_one_witness() {
    assert!(is_valid_witness_slot(0, 2, 2, false, false, 2, 0, GEN));
    assert!(is_valid_witness_slot(1, 2, 2, false, false, 2, 0, GEN));

    assert!(!is_valid_witness_slot(0, 2, 2, false, false, 2, GEN, GEN));
    assert!(is_valid_witness_slot(1, 2, 2, false, false, 2, 0, GEN));

    assert!(is_valid_witness_slot(0, 2, 2, false, false, 2, 0, GEN));
    assert!(!is_valid_witness_slot(1, 2, 2, false, false, 2, GEN, GEN));
}
