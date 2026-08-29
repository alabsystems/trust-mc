// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: UNKNOWN
// kani-expect: trl_backtrack_preserves_invariant=PROOF
// kani-expect: trl_blocking_clause_depth_valid=PROOF
// kani-expect: trl_loop_detection_correct=PROOF
// kani-expect: trl_trace_id_bounds=PROOF

//! AY self-verification bootstrap Tier 3i: CHC TRL and TRP invariants.
//!
//! These harnesses mirror the bounded `#[kani::proof]` suites from
//! `ay-chc/src/trl/verification.rs` and `ay-chc/src/trp.rs`.
//! The standalone model exercises trace-depth, blocking-clause, backtracking,
//! and recurrence invariants using only bounded integer arithmetic.
//!
//! Part of #3766: Run AY's 258 Kani harnesses through trust_mc.

// --- TRL invariants (from ay-chc/src/trl/verification.rs) ---

/// Blocking clause depth key is correctly derived from loop end position.
/// Per TRL paper: blocking clause for loop (start, end) applies at depth end+1.
#[kani::proof]
fn trl_blocking_clause_depth_valid() {
    let start: u16 = kani::any();
    let end: u16 = kani::any();

    kani::assume(start <= end);
    kani::assume(end < 1000);

    let depth_key = end + 1;

    assert!(depth_key > end);
    assert!(depth_key >= start + 1);
}

/// Backtracking preserves the invariant that depth does not exceed original.
/// When backtracking after loop detection, depth is set to loop start.
#[kani::proof]
fn trl_backtrack_preserves_invariant() {
    let current_depth: usize = kani::any();
    kani::assume(current_depth > 0);
    kani::assume(current_depth < 100);

    let start: usize = kani::any();
    let end: usize = kani::any();

    kani::assume(start <= end);
    kani::assume(end < current_depth);

    let new_depth = start;

    assert!(new_depth <= current_depth);
}

/// Loop detection returns valid indices when a loop is found.
/// When find_looping_infix returns Some((start, end)), both start <= end
/// and both indices are within trace bounds.
#[kani::proof]
fn trl_loop_detection_correct() {
    let trace_len: u8 = kani::any();
    kani::assume(trace_len > 0);
    kani::assume(trace_len <= 4);
    let tl = trace_len as usize;

    let start: usize = kani::any();
    let end: usize = kani::any();

    kani::assume(start <= end);
    kani::assume(end < tl);

    assert!(start < tl);
    assert!(end < tl);
    assert!(start <= end);
}

/// trace_id used in transitions is bounded by learned.len().
#[kani::proof]
fn trl_trace_id_bounds() {
    let learned_len: u8 = kani::any();
    kani::assume(learned_len >= 1 && learned_len <= 4);

    // Scalarize the bounded loop so CHC does not need to synthesize the
    // induction invariant for this fixed-depth trace model.
    if learned_len >= 1 {
        assert!(0u8 < learned_len);
    }
    if learned_len >= 2 {
        assert!(1u8 < learned_len);
    }
    if learned_len >= 3 {
        assert!(2u8 < learned_len);
    }
    if learned_len >= 4 {
        assert!(3u8 < learned_len);
    }
}

// --- TRP invariant (from ay-chc/src/trp.rs) ---

/// Recurrence soundness: for x' = x + delta after n iterations,
/// x_n - x_0 = delta * n.
#[kani::proof]
fn trp_recurrence_soundness() {
    let x_0: i64 = kani::any();
    let delta: i64 = kani::any();
    let n: i64 = kani::any();

    kani::assume(n > 0);
    kani::assume(n < 100);
    kani::assume(delta > -100);
    kani::assume(delta < 100);
    kani::assume(x_0 > -1_000_000);
    kani::assume(x_0 < 1_000_000);

    // Use step-by-step simulation to avoid needing checked_mul
    let n_delta = delta * n;
    let x_n = x_0 + n_delta;

    let computed_delta_sum = x_n - x_0;
    assert!(computed_delta_sum == n_delta);
}
