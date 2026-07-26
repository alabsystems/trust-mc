// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Direct AY Solver Integration.
//!
//! This module provides direct Rust-to-Rust integration with the AY SMT solver,
//! eliminating the need for text file interchange and subprocess spawning.
//!
//! ## Architecture
//!
//! Old path (subprocess-based):
//! ```text
//! compiler → .smt2 text file → driver → subprocess spawn → ay binary → parse stdout
//! ```
//!
//! New path (direct linking):
//! ```text
//! compiler → AYProgram → driver → AY Solver API → verification result
//! ```
//!
//! ## Usage
//!
//! The direct solver is used automatically when the `ay-direct` feature is enabled.
//! When disabled, the driver falls back to subprocess-based verification.
//!
//! See issue #513 for context.

#[cfg(test)]
mod tests;

use std::borrow::Cow;

use anyhow::{Result, bail};
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::mpsc;
use std::time::{Duration, Instant};

use crate::session::DEFAULT_TOOL_TIMEOUT_SECS;

use ay_frontend::Command;

use crate::property_model::{CheckStatus, Property, PropertyId, RawSourceLocation};
use crate::verification_result::{FailedProperties, VerificationStatus};

/// Run AY verification on an SMT-LIB2 string using direct linking.
///
/// This parses the SMT-LIB2 content and executes it using AY's native API,
/// avoiding subprocess spawning and text file I/O.
///
/// # REQUIRES
/// - `smt_content` is valid SMT-LIB2 syntax supported by AY
/// - Content should include (set-logic ...) and (check-sat) commands
/// - Violation variables follow the "ay_violation_*" naming convention
///
/// # ENSURES
/// - Returns Ok((status, failed_props, properties)) on successful execution
/// - `status` is Success (UNSAT) or Failure (SAT/UNKNOWN)
/// - `properties` contains one entry per ay_violation_* variable found
/// - Returns Err on parse failure or execution error
///
/// # Example
/// ```text
/// let smt = "(set-logic QF_LIA)(declare-const x Int)(assert (> x 0))(check-sat)";
/// let (status, _, _) = run_ay_direct(smt, false)?;
/// ```
///
/// NOTE: uses the fixed default tool timeout. Harness verification paths
/// must call [`run_ay_direct_with_timeout`] with a budget clamped to the
/// per-harness [`crate::deadline::Deadline`] instead (see
/// `KaniSession::try_ay_direct`); this wrapper remains for unit tests and
/// non-harness callers.
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) fn run_ay_direct(
    smt_content: &str,
    verbose: bool,
) -> Result<(VerificationStatus, FailedProperties, Vec<Property>)> {
    run_ay_direct_with_timeout(smt_content, verbose, Duration::from_secs(DEFAULT_TOOL_TIMEOUT_SECS))
}

/// Run AY verification with explicit timeout.
///
/// Part of #995: Timeout protection for direct solver execution.
pub(crate) fn run_ay_direct_with_timeout(
    smt_content: &str,
    verbose: bool,
    timeout: Duration,
) -> Result<(VerificationStatus, FailedProperties, Vec<Property>)> {
    let start = Instant::now();

    // Parse the SMT-LIB2 content
    let commands = parse_smt2_content(smt_content)?;

    if verbose {
        println!("[AY-direct] Parsed {} commands in {:?}", commands.len(), start.elapsed());
    }

    // Extract violation names before execution (needed for property building)
    let violations: Vec<String> = commands
        .iter()
        .filter_map(|cmd| {
            if let Command::DeclareConst(name, _) = cmd {
                if name.starts_with("ay_violation_") {
                    return Some(name.clone());
                }
            }
            None
        })
        .collect();

    // Execute commands with timeout protection (#995)
    // Move commands into the thread — violations already extracted above,
    // so the original Vec is no longer needed here. Avoids deep-cloning
    // the entire SMT-LIB2 AST (potentially megabytes of Term trees).
    let (tx, rx) = mpsc::channel();

    // Cancellation token: set to true when timeout fires so the solver
    // thread can exit promptly instead of running indefinitely.
    let cancelled = Arc::new(AtomicBool::new(false));
    let cancelled_clone = Arc::clone(&cancelled);

    std::thread::spawn(move || {
        let mut executor = ay_dpll::Executor::new();
        let mut check_sat_result: Option<&'static str> = None;
        let mut failed_assert_count: u32 = 0;
        let mut failed_other_count: u32 = 0;
        let mut failed_assert_indices: Vec<usize> = Vec::new();
        let mut failed_other_indices: Vec<usize> = Vec::new();

        for (idx, cmd) in commands.iter().enumerate() {
            // Check cancellation every 64 commands to limit overhead.
            if idx & 63 == 0 && cancelled_clone.load(Ordering::Relaxed) {
                break;
            }
            match executor.execute(cmd) {
                Ok(response) => {
                    if let Some(output) = response {
                        if output == "sat" {
                            check_sat_result = Some("sat");
                        } else if output == "unsat" {
                            check_sat_result = Some("unsat");
                        } else if output == "unknown" {
                            check_sat_result = Some("unknown");
                        }
                    }
                }
                Err(e) => {
                    let is_assert = matches!(cmd, Command::Assert(_));
                    if is_assert {
                        failed_assert_count += 1;
                        failed_assert_indices.push(idx + 1);
                    } else {
                        failed_other_count += 1;
                        failed_other_indices.push(idx + 1);
                    }
                    if verbose {
                        let cmd_kind = if is_assert { "assert" } else { "other" };
                        eprintln!(
                            "[AY-direct] Command error #{idx} ({cmd_kind}): {e}",
                            idx = idx + 1
                        );
                    }
                }
            }
        }
        let _ = tx.send((
            check_sat_result,
            failed_assert_count,
            failed_other_count,
            failed_assert_indices,
            failed_other_indices,
        ));
        // Drop executor and commands here — frees AY solver memory.
    });

    let (
        check_sat_result,
        failed_assert_count,
        failed_other_count,
        failed_assert_indices,
        failed_other_indices,
    ) = match rx.recv_timeout(timeout) {
        Ok(result) => result,
        Err(mpsc::RecvTimeoutError::Timeout) => {
            // Signal the solver thread to stop so it doesn't leak memory.
            cancelled.store(true, Ordering::Relaxed);
            bail!(
                "AY direct solver timed out after {:.1}s. Use --tool-timeout to increase.",
                timeout.as_secs_f64()
            );
        }
        Err(mpsc::RecvTimeoutError::Disconnected) => {
            bail!("AY direct solver thread panicked unexpectedly");
        }
    };

    let elapsed = start.elapsed();

    // Part of #2660: Demote result if assert commands failed.
    // A dropped assert weakens the constraint set, making UNSAT easier — false positive.
    // Always warn on assert failures — soundness-critical. Non-asserts gated on verbose.
    if failed_assert_count > 0 {
        let failed_assert_summary = summarize_command_indices(&failed_assert_indices, 8);
        eprintln!(
            "[AY-direct] WARNING: {failed_assert_count} assert command(s) failed at \
             command index(es) [{failed_assert_summary}] — demoting result to Failure \
             (dropped constraints = weaker problem)"
        );
    }
    if failed_other_count > 0 && verbose {
        let failed_other_summary = summarize_command_indices(&failed_other_indices, 8);
        eprintln!(
            "[AY-direct] WARNING: {failed_other_count} non-assert command(s) failed at \
             command index(es) [{failed_other_summary}]"
        );
    }

    // Interpret result
    let (status, failed_props) = match check_sat_result {
        Some("unsat") => {
            // UNSAT = verification passes (no counterexample found)
            if verbose {
                println!("[AY-direct] Result: UNSAT (verified) in {:?}", elapsed);
            }
            (VerificationStatus::Success, FailedProperties::None)
        }
        Some("sat") => {
            // SAT = counterexample found (verification fails)
            if verbose {
                println!("[AY-direct] Result: SAT (counterexample) in {:?}", elapsed);
            }
            (VerificationStatus::Failure, FailedProperties::Other)
        }
        Some("unknown") | None => {
            // Unknown or no check-sat command
            if verbose {
                println!("[AY-direct] Result: UNKNOWN in {:?}", elapsed);
            }
            (VerificationStatus::Failure, FailedProperties::Other)
        }
        Some(_) => {
            // Unexpected response
            (VerificationStatus::Failure, FailedProperties::Other)
        }
    };

    // Part of #2660: Demote to Failure if any assert commands failed.
    // Dropped asserts weaken the constraint set — UNSAT on a weaker problem is unsound.
    let (status, failed_props) = if failed_assert_count > 0 && status == VerificationStatus::Success
    {
        (VerificationStatus::Failure, FailedProperties::Other)
    } else {
        (status, failed_props)
    };

    // Build properties list
    let properties = build_properties(&violations, status);

    Ok((status, failed_props, properties))
}

/// Parse SMT-LIB2 content into commands.
///
/// # REQUIRES
/// - `content` is valid SMT-LIB2 syntax
///
/// # ENSURES
/// - On success, returns Vec of all parsed commands in order
/// - On error, returns parse error at first invalid syntax
fn parse_smt2_content(content: &str) -> Result<Vec<Command>> {
    ay_frontend::parse(content).map_err(|e| anyhow::anyhow!("SMT-LIB2 parse error: {e}"))
}

/// Build property list from violation declarations.
///
/// # REQUIRES
/// - `violations` contains violation variable names (typically "ay_violation_*")
///
/// # ENSURES
/// - Returns Vec<Property> with one entry per violation (empty if no violations)
/// - All properties have CheckStatus::Success (model inspection not implemented)
/// - Property descriptions are derived from violation names via violation_name_to_description
fn build_properties(violations: &[String], status: VerificationStatus) -> Vec<Property> {
    let prop_status = if status == VerificationStatus::Success {
        CheckStatus::Success
    } else {
        CheckStatus::Undetermined
    };
    violations
        .iter()
        .enumerate()
        .map(|(idx, name)| {
            let description = violation_name_to_description(name);
            Property {
                description: Cow::Owned(description),
                property_id: PropertyId {
                    fn_name: None,
                    class: Cow::Borrowed("assertion"),
                    id: idx as u32,
                },
                source_location: RawSourceLocation {
                    column: None,
                    file: None,
                    function: None,
                    line: None,
                },
                // Without model inspection we can't identify which property failed.
                // Mark properties as undetermined when verification is not UNSAT.
                status: prop_status,
                trace: None,
            }
        })
        .collect()
}

/// Summarize failed command indices for warning output.
///
/// Uses 1-based indices to match parser/execution order in logs.
fn summarize_command_indices(indices: &[usize], max_items: usize) -> String {
    let shown: Vec<String> = indices.iter().take(max_items).map(ToString::to_string).collect();
    if shown.is_empty() {
        return String::from("none");
    }
    if indices.len() > max_items {
        format!("{}, ... (+{} more)", shown.join(", "), indices.len() - max_items)
    } else {
        shown.join(", ")
    }
}

/// Convert a violation variable name to a human-readable description.
///
/// # REQUIRES
/// - None (any string is accepted)
///
/// # ENSURES
/// - Strips "ay_violation_" prefix if present
/// - Replaces underscores with spaces
/// - E.g., "ay_violation_kani_assert_0" -> "kani assert 0"
fn violation_name_to_description(name: &str) -> String {
    // ay_violation_kani_assert_0 -> "assertion 0"
    // ay_violation_overflow_check_add_1 -> "overflow check add 1"
    let stripped = name.strip_prefix("ay_violation_").unwrap_or(name);
    stripped.replace('_', " ")
}
