// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: UNKNOWN
// kani-expect: proof_recurrence_soundness=PROOF
// kani-expect: sign_contradicts_consistency=PROOF
// NOTE: recurrence/sign constraints are clean CHC PROOF; handled_vars stays UNKNOWN under ay#8578 false-proof defenses.

//! AY self-verification bootstrap Tier 3: TRP recurrence + NRA sign invariants.
//!
//! Standalone models from:
//! - `ay-chc/src/trp.rs`: recurrence soundness (constant delta), handled_vars tracking
//! - `ay-theories/nra/src/verification.rs`: sign constraint consistency
//!
//! Source: 3 harnesses total
//! Part of #3766: Run AY's 258 Kani harnesses through trust_mc.

// ========================================================================
// TRP Recurrence Soundness
// ========================================================================

/// Recurrence: after n iterations with constant delta, x_n = x_0 + delta * n.
#[kani::proof]
fn proof_recurrence_soundness() {
    let x_0: i64 = kani::any();
    let delta: i64 = kani::any();
    let n: i64 = kani::any();

    kani::assume(n > 0 && n < 100);
    kani::assume(delta > -100 && delta < 100);
    kani::assume(x_0 > -1_000_000 && x_0 < 1_000_000);

    let n_delta = delta * n;
    let x_n = x_0 + n_delta;

    let computed_delta_sum = x_n - x_0;
    assert!(computed_delta_sum == n_delta, "Recurrence invariant: x_n - x_0 = delta * n");
}

// ========================================================================
// NRA Sign Constraint
// ========================================================================

#[derive(Clone, Copy, PartialEq, Eq)]
enum SignConstraint {
    Positive,
    NonNegative,
}

fn sign_contradicts(constraint: SignConstraint, sign: i32) -> bool {
    match constraint {
        SignConstraint::Positive => sign <= 0,
        SignConstraint::NonNegative => sign < 0,
    }
}

/// sign_contradicts is consistent with the semantics of Positive and NonNegative.
#[kani::proof]
fn sign_contradicts_consistency() {
    let sign: i32 = kani::any();
    kani::assume(sign >= -1 && sign <= 1);

    if sign > 0 {
        assert!(!sign_contradicts(SignConstraint::Positive, sign));
    }
    if sign >= 0 {
        assert!(!sign_contradicts(SignConstraint::NonNegative, sign));
    }
}

// ========================================================================
// TRP Handled Vars Tracking
// ========================================================================

/// Insert into a set makes the element present; set grows by at most 1.
/// Models the handled_vars tracking in TRP emit_recurrence_constraints.
#[kani::proof]
fn proof_handled_vars_tracking() {
    let mut handled: [bool; 3] = [false; 3];
    let mut count: usize = 0;

    let var_idx: u8 = kani::any();
    kani::assume(var_idx < 3);

    let initial_count = count;

    if !handled[var_idx as usize] {
        handled[var_idx as usize] = true;
        count += 1;
    }

    assert!(handled[var_idx as usize], "Variable must be in handled set after insertion");
    assert!(count >= initial_count, "Count must be monotonic");
    assert!(count <= initial_count + 1, "Count grows by at most 1 per insert");
}
