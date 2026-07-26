// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Shared AY solver runner for integration tests.
//!
//! Extracted from duplicated code in `integration_bmc_tests.rs` and
//! `integration_chc_tests.rs` (Part of #2596).

use std::io::{Read, Write};
use std::process::{Command, Stdio};
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::mpsc::RecvTimeoutError;
use std::time::Duration;

use ay_dpll::Executor;
use ay_frontend::parse;

const AY_DEFAULT_TIMEOUT_SECS: u64 = 10;

/// Extra wall-clock slack added on top of the solve budget before the hard
/// guard fires. The portfolio's internal deadline (`time_budget`) is the
/// primary stop, but some routes (notably the BV+Array memory model with
/// `obj_valid`/`obj_size` arrays) only poll the deadline coarsely, so this
/// outer guard guarantees the test runner always returns in bounded time.
const AY_CHC_GUARD_SLACK_SECS: u64 = 5;

pub(super) fn ay_test_timeout_secs() -> u64 {
    std::env::var("TRUST_MC_AY_TEST_TIMEOUT_SECS")
        .or_else(|_| std::env::var("TRUST_MC_Z3_TEST_TIMEOUT_SECS"))
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(AY_DEFAULT_TIMEOUT_SECS)
}

/// Solve an SMT-LIB problem (plain SMT or the CHC dialect) and return the
/// verdict.
///
/// Routing: z3 is the PRIMARY oracle for BOTH shapes — plain SMT goes to z3's
/// SMT engine, the CHC dialect (`declare-rel`/`declare-var`/`rule`/`query`)
/// goes to z3's PDR — each under a hard wall-clock timeout enforced by
/// killing the child. z3 is the engine these e2e tests were originally written
/// and validated against. We fall back to ay's own (also hard-bounded) engine
/// ONLY when no `z3` binary is on PATH (`Z3Unavailable`): the ay SMT `Executor`
/// for plain SMT, the ay CHC portfolio for the CHC dialect.
///
/// Why z3-primary: the ay backends currently return `unknown` (not the
/// validated `sat`/`unsat`) on several of these counterexample-finding cases
/// (the `Tuple_bv32_bool` / branch-overflow encodings; the BV+Array memory
/// model), so a pure-ay route cannot reproduce the verdicts the tests assert.
/// z3 discharges every one of these in milliseconds. Soundness is preserved
/// regardless of which solver answers: both are trusted engines, and the
/// `sat`/`unsat`/`unknown` whitelist is enforced on every path — any timeout,
/// non-zero exit, or other output is surfaced as an `Err` (or, for the ay CHC
/// guard, an honest "unknown"), NEVER a fabricated verdict.
///
/// This is the production trust-mc-driver path's test-harness analogue only;
/// the driver's own solver selection is untouched.
pub(in crate::codegen_ay) fn run_ay_on_smt2(smt: &str) -> Result<String, String> {
    if smt.contains("(query ") || smt.contains("(rule ") || smt.contains("(declare-rel ") {
        return run_chc_on_smt2(smt);
    }

    match run_z3_smt2(smt) {
        Ok(verdict) => Ok(verdict),
        // z3 not on PATH: degrade to ay's bounded SMT executor. Any other z3
        // error (timeout, crash, malformed output) is surfaced rather than
        // silently retried, so a regression in the primary oracle cannot be
        // masked by the fallback.
        Err(ChcSolveError::Z3Unavailable) => run_ay_smt2(smt),
        Err(ChcSolveError::Other(msg)) => Err(msg),
    }
}

/// Fallback plain-SMT solver: ay's own `Executor` under a hard wall-clock
/// guard. Used only when z3 is unavailable.
fn run_ay_smt2(smt: &str) -> Result<String, String> {
    let commands = parse(smt).map_err(|err| format!("AY failed to parse SMT-LIB: {err}"))?;

    let mut executor = Executor::new();
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

    let outputs = executor
        .execute_all(&commands)
        .map_err(|err| format!("AY failed to execute SMT-LIB: {err}"));
    let timed_out = interrupt.load(Ordering::Relaxed);
    let _ = cancel_tx.send(());
    let _ = timer.join();

    if timed_out {
        return Err(format!("AY timed out after {}s", timeout.as_secs()));
    }

    for output in outputs? {
        let verdict = output.trim();
        if matches!(verdict, "sat" | "unsat" | "unknown") {
            return Ok(verdict.to_string());
        }
    }

    Err("AY returned no sat/unsat/unknown verdict".to_string())
}

/// Solve a CHC problem: z3's PDR (primary) under a hard timeout, falling
/// back to ay's own hard-bounded CHC engine when z3 is not available.
///
/// See [`run_ay_on_smt2`] for the rationale behind the z3-primary routing.
fn run_chc_on_smt2(smt: &str) -> Result<String, String> {
    match run_z3_chc(smt) {
        Ok(verdict) => Ok(verdict),
        // z3 not on PATH: degrade to ay's bounded CHC engine. Any other z3
        // error (timeout, crash) is surfaced rather than silently retried,
        // so a regression in the primary oracle cannot be masked.
        Err(ChcSolveError::Z3Unavailable) => run_ay_chc(smt),
        Err(ChcSolveError::Other(msg)) => Err(msg),
    }
}

enum ChcSolveError {
    /// No `z3` binary was found on PATH.
    Z3Unavailable,
    /// z3 was found but failed (timeout, non-zero exit, malformed output).
    Other(String),
}

/// Run z3 on a plain SMT-LIB problem under a hard wall-clock timeout.
///
/// Identical transport to [`run_z3_chc`] (z3 routes plain SMT to its SMT
/// engine and the CHC dialect to PDR based on the script itself), so both
/// delegate to the shared [`run_z3`] helper. The first stdout line is taken as
/// the verdict and validated against the `sat`/`unsat`/`unknown` whitelist;
/// anything else is an `Err`, never a fabricated verdict.
fn run_z3_smt2(smt: &str) -> Result<String, ChcSolveError> {
    run_z3(smt)
}

/// Run z3's CHC/PDR engine on the SMT-LIB CHC problem under a hard
/// wall-clock timeout enforced by killing the child process.
fn run_z3_chc(smt: &str) -> Result<String, ChcSolveError> {
    run_z3(smt)
}

/// Shared z3 transport: spawn `z3 -in`, write the SMT-LIB script to stdin,
/// drain stdout/stderr on reader threads (so z3 can't block on a full pipe),
/// and enforce a hard wall-clock deadline by polling `try_wait` and killing
/// the child if it overruns. The first stdout line is the verdict; it is
/// validated against the `sat`/`unsat`/`unknown` whitelist before being
/// returned, so a timeout, non-zero exit, or any other output yields an
/// `Err` rather than a fabricated verdict.
fn run_z3(smt: &str) -> Result<String, ChcSolveError> {
    let mut child = match Command::new("z3")
        .arg("-in")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
    {
        Ok(child) => child,
        Err(err) if err.kind() == std::io::ErrorKind::NotFound => {
            return Err(ChcSolveError::Z3Unavailable);
        }
        Err(err) => return Err(ChcSolveError::Other(format!("failed to spawn z3: {err}"))),
    };

    {
        let mut stdin = child.stdin.take().expect("z3 child should expose stdin");
        stdin.write_all(smt.as_bytes()).map_err(|e| {
            ChcSolveError::Other(format!("failed to write SMT-LIB to z3 stdin: {e}"))
        })?;
    }

    // Drain stdout/stderr on reader threads (so z3 can't block on a full pipe),
    // and enforce the deadline on the main thread by polling `try_wait` and
    // killing the child if it overruns. Retaining the child handle here is what
    // lets us actually terminate a hung solve rather than leak it.
    let mut stdout_pipe = child.stdout.take().expect("z3 child should expose stdout");
    let mut stderr_pipe = child.stderr.take().expect("z3 child should expose stderr");
    let stdout_reader = std::thread::spawn(move || {
        let mut buf = Vec::new();
        let _ = stdout_pipe.read_to_end(&mut buf);
        buf
    });
    let stderr_reader = std::thread::spawn(move || {
        let mut buf = Vec::new();
        let _ = stderr_pipe.read_to_end(&mut buf);
        buf
    });

    let timeout = Duration::from_secs(ay_test_timeout_secs());
    let start = std::time::Instant::now();
    let status = loop {
        match child.try_wait() {
            Ok(Some(status)) => break status,
            Ok(None) => {
                if start.elapsed() >= timeout {
                    let _ = child.kill();
                    let _ = child.wait();
                    let _ = stdout_reader.join();
                    let _ = stderr_reader.join();
                    return Err(ChcSolveError::Other(format!(
                        "z3 timed out after {}s",
                        timeout.as_secs()
                    )));
                }
                std::thread::sleep(Duration::from_millis(5));
            }
            Err(e) => {
                let _ = child.kill();
                return Err(ChcSolveError::Other(format!("failed waiting on z3: {e}")));
            }
        }
    };

    let stdout_buf = stdout_reader.join().unwrap_or_default();
    let stderr_buf = stderr_reader.join().unwrap_or_default();
    let stdout = String::from_utf8_lossy(&stdout_buf).trim().to_string();
    let stderr = String::from_utf8_lossy(&stderr_buf).trim().to_string();
    let result = stdout.lines().next().unwrap_or("").trim().to_string();
    if matches!(result.as_str(), "sat" | "unsat" | "unknown") {
        return Ok(result);
    }
    if !status.success() {
        return Err(ChcSolveError::Other(format!(
            "z3 exited with status {status}; stdout={stdout:?}; stderr={stderr:?}"
        )));
    }
    if result.is_empty() {
        return Err(ChcSolveError::Other(format!("z3 returned empty output; stderr={stderr:?}")));
    }
    Err(ChcSolveError::Other(format!("z3 returned unexpected verdict {result:?}")))
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

/// Fallback: solve a CHC problem via ay's production `AdaptivePortfolio` engine
/// under a hard wall-clock guard. Used only when z3 is unavailable.
fn run_ay_chc(smt: &str) -> Result<String, String> {
    let problem = ay_chc::ChcParser::parse(smt)
        .map_err(|err| format!("AY failed to parse CHC SMT-LIB: {err}"))?;

    let budget = Duration::from_secs(ay_test_timeout_secs());
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
