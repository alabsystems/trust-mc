// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Shared AY solver runner for integration tests.
//!
//! Extracted from duplicated code in `integration_bmc_tests.rs` and
//! `integration_chc_tests.rs` (Part of #2596).

use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::mpsc::RecvTimeoutError;
use std::time::Duration;

use ay_dpll::Executor;
use ay_frontend::parse;

const AY_DEFAULT_TIMEOUT_SECS: u64 = 10;
/// The ay CHC fallback's budget. A PDR solve near a 10 s budget flips to
/// `unknown` under the parallel suite's load — measured 2026-09-16:
/// `test_chc_e2e_std_alloc_realloc_grow_full_proves_unsat` failed once in
/// 1714 and passed twice in isolation. A regression to `unknown` still shows
/// at 30 s; a proof that merely needed the machine to itself no longer does.
const AY_CHC_DEFAULT_TIMEOUT_SECS: u64 = 30;

/// Extra wall-clock slack added on top of the solve budget before the hard
/// guard fires. The portfolio's internal deadline (`time_budget`) is the
/// primary stop, but some routes (notably the BV+Array memory model with
/// `obj_valid`/`obj_size` arrays) only poll the deadline coarsely, so this
/// outer guard guarantees the test runner always returns in bounded time.
const AY_CHC_GUARD_SLACK_SECS: u64 = 5;

pub(super) fn ay_test_timeout_secs() -> u64 {
    std::env::var("TRUST_MC_AY_TEST_TIMEOUT_SECS")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(AY_DEFAULT_TIMEOUT_SECS)
}

/// Solve an SMT-LIB problem (plain SMT or the CHC dialect) and return the
/// verdict, with ay — trust-mc's only verification backend (CLAUDE.md).
///
/// Plain SMT goes to ay's SMT `Executor`, the CHC dialect
/// (`declare-rel`/`declare-var`/`rule`/`query`) to ay's CHC portfolio, each
/// under a hard wall-clock guard. The `sat`/`unsat`/`unknown` whitelist is
/// enforced on every path: a timeout or any other output is an `Err` (or, for
/// the CHC guard, an honest "unknown"), never a fabricated verdict.
///
/// These tests used to ask a `z3` found on PATH first and fall back to ay only
/// when none was there, on the claim that ay returned `unknown` on several of
/// them. That claim was falsified (design trust-mc-reds-final §7.1, E1: all 69
/// such engine tests decided by ay), and a solver taken by bare name from PATH
/// is not the one a measurement names: on a host where the name resolves to a
/// launcher that refuses it, every one of those tests failed.
///
/// This is the production trust-mc-driver path's test-harness analogue only;
/// the driver's own solver selection is untouched.
pub(in crate::codegen_ay) fn run_ay_on_smt2(smt: &str) -> Result<String, String> {
    if smt.contains("(query ") || smt.contains("(rule ") || smt.contains("(declare-rel ") {
        return run_ay_chc(smt);
    }
    run_ay_smt2(smt)
}

/// Plain-SMT solver: ay's own `Executor` under a hard wall-clock guard (the
/// plain-SMT half of [`run_ay_on_smt2`]; the float `%` regression tests,
/// `float_arithmetic_frem_tests.rs`, call it directly).
pub(in crate::codegen_ay) fn run_ay_smt2(smt: &str) -> Result<String, String> {
    let commands = parse(smt).map_err(|err| format!("AY failed to parse SMT-LIB: {err}"))?;

    let mut executor = Executor::new();
    // Verdict only: nothing here consumes a proof artifact. ay's bare
    // `Executor::new()` posture at 10bc4b185 does search-time proof tracking
    // that turned this emitter's BMC VCs from a 0.26 s `unsat` into a 10 s
    // `unknown` in-process, while the pinned ay CLI — the oracle for every
    // counted BMC row — decides the identical text in 0.26 s. Competition mode
    // is ay's own switch for "no search-time proof unless demanded"; it sheds
    // that work and nothing about the decision. Measured, one knob at a time:
    //   bare 9.84 s unknown · strict_logic_compliance(false) 10.07 s unknown ·
    //   best_effort_produce_proofs 8.01 s unknown · retain_parsed(false) 10.68 s
    //   unknown · produce_proofs(true) 10.45 s unknown ·
    //   competition_mode(true) 0.26 s UNSAT.
    executor.set_competition_mode(true);
    let interrupt = Arc::new(AtomicBool::new(false));
    executor.set_interrupt(Arc::clone(&interrupt));

    let timeout = Duration::from_secs(ay_test_timeout_secs());
    let (cancel_tx, cancel_rx) = std::sync::mpsc::channel();
    let timer_interrupt = Arc::clone(&interrupt);
    let timer = std::thread::spawn(move || {
        if cancel_rx.recv_timeout(timeout).is_err() {
            timer_interrupt.store(true, Ordering::Relaxed);
        }
    });

    // Hand ay the budget itself, as the driver's `ay_direct` path does: the
    // interrupt flag only stops a solver that polls it, a deadline lets every
    // budgeted pass bail on its own. The std wall instant enters ay through
    // ay's own `From`, as in `ay_direct`.
    #[expect(
        clippy::useless_conversion,
        reason = "identity while ay's Instant re-exports std's; delete once ay's clock seam makes it a newtype"
    )]
    executor.set_deadline(Some((std::time::Instant::now() + timeout).into()));

    // Execute command by command and STOP at the first verdict. A VC ends in
    // `(get-value …)` / `(get-model)` after `(check-sat)`; after `unsat` those
    // cannot change the verdict, they can only fail or stall. Measured at ay
    // 10bc4b185: `execute_all` on the emitted BMC VC timed out at 10 s
    // in-process while the pinned ay CLI answered `unsat` for the identical
    // text in 0.2 s — so the stall is not in the decision. Any single command
    // that takes a second or more is named on stderr, so a stall is a finding,
    // not a mystery.
    let mut verdict: Option<String> = None;
    let mut exec_err: Option<String> = None;
    for cmd in &commands {
        let started = std::time::Instant::now();
        let step = executor.execute(cmd);
        let took = started.elapsed();
        if took >= Duration::from_secs(1) {
            eprintln!(
                "run_ay_smt2: `{}` took {:.2}s",
                format!("{cmd:?}").chars().take(60).collect::<String>(),
                took.as_secs_f64()
            );
        }
        match step {
            Ok(Some(output)) => {
                let v = output.trim();
                if matches!(v, "sat" | "unsat" | "unknown") {
                    verdict = Some(v.to_string());
                    break;
                }
            }
            Ok(None) => {}
            Err(err) => {
                exec_err = Some(format!("AY failed to execute SMT-LIB: {err}"));
                break;
            }
        }
        if interrupt.load(Ordering::Relaxed) {
            break;
        }
    }
    let timed_out = interrupt.load(Ordering::Relaxed);
    let _ = cancel_tx.send(());
    let _ = timer.join();

    if timed_out {
        return Err(format!("AY timed out after {}s", timeout.as_secs()));
    }
    if let Some(err) = exec_err {
        return Err(err);
    }
    if let Some(v) = verdict {
        return Ok(v);
    }

    Err("AY returned no sat/unsat/unknown verdict".to_string())
}

/// Map a validated portfolio result to an SMT verdict string.
///
/// `VerifiedChcResult` is `#[non_exhaustive]`; the explicit catch-all maps any
/// future inconclusive variant to "unknown" (fail-closed — never a verdict).
fn verified_result_to_verdict(result: &ay_chc::VerifiedChcResult) -> &'static str {
    match result {
        ay_chc::VerifiedChcResult::Safe(_) => "unsat",
        ay_chc::VerifiedChcResult::Unsafe(_) => "sat",
        ay_chc::VerifiedChcResult::Unknown(_) => "unknown",
        _ => "unknown",
    }
}

/// Solve a CHC problem via ay's production `AdaptivePortfolio` engine under a
/// hard wall-clock guard (the CHC half of [`run_ay_on_smt2`]).
fn run_ay_chc(smt: &str) -> Result<String, String> {
    let problem = ay_chc::ChcParser::parse(smt)
        .map_err(|err| format!("AY failed to parse CHC SMT-LIB: {err}"))?;

    let budget = Duration::from_secs(
        std::env::var("TRUST_MC_AY_TEST_TIMEOUT_SECS")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(AY_CHC_DEFAULT_TIMEOUT_SECS),
    );
    let config = ay_chc::AdaptiveConfig::with_budget(budget, false);

    // Run the solve on a worker thread so the test runner can enforce a hard
    // wall-clock bound even if an inner route polls the budget too coarsely.
    let (tx, rx) = std::sync::mpsc::channel();
    let solver_thread = std::thread::Builder::new()
        .name("ay-chc-test-solver".to_string())
        .spawn(move || {
            let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                ay_chc::AdaptivePortfolio::new(problem, config).solve()
            }));
            let _ = tx.send(outcome);
        })
        .map_err(|err| format!("failed to spawn AY CHC solver thread: {err}"))?;

    let guard = budget + Duration::from_secs(AY_CHC_GUARD_SLACK_SECS);
    match rx.recv_timeout(guard) {
        Ok(Ok(result)) => {
            let _ = solver_thread.join();
            Ok(verified_result_to_verdict(&result).to_string())
        }
        Ok(Err(_panic)) => {
            let _ = solver_thread.join();
            Err("AY CHC solver panicked".to_string())
        }
        // Hard guard fired (or sender hung up): the worker may still be running,
        // so we deliberately leave it detached rather than block on join. Return
        // "unknown" — an honest, sound non-answer; never a fabricated verdict.
        Err(RecvTimeoutError::Timeout | RecvTimeoutError::Disconnected) => {
            Ok("unknown".to_string())
        }
    }
}
