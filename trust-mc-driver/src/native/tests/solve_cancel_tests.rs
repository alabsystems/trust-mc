// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Decision NATIVE-SOLVE-CANCEL on the real ay lanes: the token a native
//! watchdog cancels when its deadline expires reaches the solve it stops.
//!
//! The watchdog's own contract (expiry cancels, a late result is dropped, a
//! fast result is returned uncancelled) is tested in `native::solve_watchdog`.
//! Here each lane is driven with a live token as the control, so a lane that
//! simply fails on the fixture cannot pass for one that observed a
//! cancellation. The strict PDR proof run takes no token, by decision (its
//! call site in `solve_typed_chc_pdr_pipeline` says why); the direct-SMT
//! decision's poll is tested in `direct_smt_cex`, and the SMT-LIB BMC
//! executor's interrupt in `native::tests`.

use super::*;

use ay_chc::CancellationToken;

/// The IC3 loop lane gives up once its token is cancelled: `None`, the lane's
/// no-candidate answer, where a live token admits the parity loop.
#[test]
fn the_ic3_loop_lane_observes_a_cancelled_token() {
    let problem = bv64_real_ssa_cfg(1);
    let live = CancellationToken::new();
    assert!(
        ic3_loop_lane_proof_run(&problem, Duration::from_secs(60), &live).is_some(),
        "control: under a live token the lane admits the true parity loop"
    );
    let cancelled = CancellationToken::new();
    cancelled.cancel();
    assert!(
        ic3_loop_lane_proof_run(&problem, Duration::from_secs(60), &cancelled).is_none(),
        "a cancelled lane yields no candidate"
    );
}

/// The clause check behind the PdrInvariant replay seal and the IC3 lane's
/// explicit re-validation observes the token: a cancelled check is not a
/// validation, where a live one accepts the same true invariant.
#[test]
fn the_invariant_model_check_observes_a_cancelled_token() {
    let problem = bv64_real_ssa_cfg(1);
    let candidate = ay_chc::ic3_lane::try_prove_chc_loop(&problem, Duration::from_secs(60))
        .expect("the IC3 lane finds the parity invariant");
    let config = || {
        ay_encode::invoke::EncodeConfig::new()
            .with_engine(ay_encode::invoke::Engine::Pdr)
            .with_proof_mode(ay_encode::invoke::ProofMode::Strict)
            .with_timeout(Duration::from_secs(60))
            .to_pdr_config()
    };
    let live = CancellationToken::new();
    assert_eq!(
        validate_invariant_model_with_cancellation(&problem, &candidate, config(), &live).ok(),
        Some(true),
        "control: a live check validates the true invariant"
    );
    let cancelled = CancellationToken::new();
    cancelled.cancel();
    assert_ne!(
        validate_invariant_model_with_cancellation(&problem, &candidate, config(), &cancelled).ok(),
        Some(true),
        "a cancelled check never validates"
    );
}
