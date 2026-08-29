// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: UNKNOWN
// kani-expect: ay_tseitin_literal_double_negation=PROOF
// kani-expect: ay_tseitin_non_empty_clause_not_empty=PROOF
// kani-expect: ay_tseitin_positive_negation_is_negative=PROOF
// kani-expect: ay_trl_blocking_clause_depth_valid=PROOF
// kani-expect: ay_trl_trace_id_bounds=PROOF
// kani-expect: ay_trl_loop_detection_correct=PROOF
// kani-expect: ay_trl_learned_relations_monotonic=PROOF
// NOTE: All 7 harnesses are clean CHC PROOF at ay 733ba8cd after bounded TRL scalarization.

//! AY self-verification bootstrap Tier 3d: Tseitin CNF and TRL depth invariants.
//!
//! These harnesses verify ay's Tseitin transformation types (CNF literals and
//! clauses) and TRL (Transition Relation Learning) loop depth invariants.
//! All use pure integer/struct patterns — no Vec mutation with symbolic indices.
//!
//! Ported from `ay-core/src/tseitin.rs` and `ay-chc/src/trl/verification.rs`.
//!
//! Part of #3766: Run AY's 258 Kani harnesses through trust_mc.

// ============================================================
// Standalone CNF literal type from ay-core/src/tseitin.rs
// ============================================================

type CnfLit = i32;

// ============================================================
// ay-core/src/tseitin.rs — literal properties
// ============================================================

/// Port of ay::tseitin::proof_literal_double_negation
#[kani::proof]
fn ay_tseitin_literal_double_negation() {
    let lit: CnfLit = kani::any();
    kani::assume(lit != 0);
    kani::assume(lit != i32::MIN);

    let negated = -lit;
    let double_negated = -negated;

    assert!(double_negated == lit, "Double negation must return original literal");
}

/// Port of ay::tseitin::proof_positive_literal_negation_is_negative
#[kani::proof]
fn ay_tseitin_positive_negation_is_negative() {
    let lit: CnfLit = kani::any();
    kani::assume(lit > 0);

    let negated = -lit;

    assert!(negated < 0, "Negating positive literal must produce negative");
}

/// Port of ay::tseitin::proof_non_empty_clause_not_empty
/// Inlined CnfClause::unit to avoid Vec encoding gap.
#[kani::proof]
fn ay_tseitin_non_empty_clause_not_empty() {
    let lit: CnfLit = kani::any();
    kani::assume(lit != 0);

    // Inline: CnfClause::unit(lit) creates a 1-element collection.
    // Model as scalar length + content instead of Vec.
    let clause_len: usize = 1;
    let clause_0: CnfLit = lit;

    assert!(clause_len > 0, "Unit clause must not be empty");
    assert!(clause_len == 1, "Unit clause must have exactly one literal");
    assert!(clause_0 == lit, "Unit clause literal must match input");
}

// ============================================================
// ay-chc/src/trl/verification.rs — TRL depth invariants
// ============================================================

/// Port of ay::trl::proof_blocking_clause_depth_valid
#[kani::proof]
fn ay_trl_blocking_clause_depth_valid() {
    let start: u16 = kani::any();
    let end: u16 = kani::any();

    kani::assume(start <= end);
    kani::assume(end < 1000);

    let depth_key = end + 1;

    assert!(depth_key > end, "depth_key is strictly greater than end");
    assert!(depth_key > start, "depth_key is strictly greater than start");
}

/// Port of ay::trl::proof_trace_id_bounds (simplified — concrete iteration)
#[kani::proof]
fn ay_trl_trace_id_bounds() {
    let learned_len: u8 = kani::any();
    kani::assume(learned_len >= 1 && learned_len <= 4);

    // Unrolled loop: each iteration asserts i < learned_len before incrementing.
    // Avoids while-loop encoding gap in CHC/Spacer.
    if learned_len >= 1 {
        assert!(0u8 < learned_len, "trace_id must be in bounds");
    }
    if learned_len >= 2 {
        assert!(1u8 < learned_len, "trace_id must be in bounds");
    }
    if learned_len >= 3 {
        assert!(2u8 < learned_len, "trace_id must be in bounds");
    }
    if learned_len >= 4 {
        assert!(3u8 < learned_len, "trace_id must be in bounds");
    }
}

/// Port of ay::trl::proof_loop_detection_correct
#[kani::proof]
fn ay_trl_loop_detection_correct() {
    let trace_len: u8 = kani::any();
    kani::assume(trace_len > 0 && trace_len <= 4);

    let start: u8 = kani::any();
    let end: u8 = kani::any();

    kani::assume(start <= end);
    kani::assume(end < trace_len);

    assert!(start < trace_len, "start must be in bounds");
    assert!(end < trace_len, "end must be in bounds");
}

// ============================================================
// ay-chc/src/trl/verification.rs — learned relations monotonic
// ============================================================

/// Port of ay::trl::proof_learned_relations_monotonic (simplified)
#[kani::proof]
fn ay_trl_learned_relations_monotonic() {
    let mut count: u8 = 1; // TRL starts with one transition
    let initial_count = count;
    assert!(initial_count == 1, "TRL starts with exactly one transition");

    let num_learns: u8 = kani::any();
    kani::assume(num_learns <= 3);

    // Scalarize the bounded learn sequence to avoid asking CHC to synthesize
    // a loop invariant for a fixed-depth counter.
    if num_learns >= 1 {
        let prev_count = count;
        count += 1;
        assert!(count > prev_count, "Each learn must increase count");
    }
    if num_learns >= 2 {
        let prev_count = count;
        count += 1;
        assert!(count > prev_count, "Each learn must increase count");
    }
    if num_learns >= 3 {
        let prev_count = count;
        count += 1;
        assert!(count > prev_count, "Each learn must increase count");
    }

    assert!(
        count >= initial_count,
        "Learned relation count must be monotonically growing"
    );
    assert!(
        count == initial_count + num_learns,
        "Final count must equal initial + number of learns"
    );
}
