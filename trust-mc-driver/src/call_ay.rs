// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! AY Backend Driver.
//!
//! This module handles invocation of the AY solver for verification.
//! It reads SMT-LIB2 files produced by the AY codegen backend and
//! parses the solver output to produce verification results.
//!
//! ## Direct Linking (ay-direct feature)
//!
//! When the `ay-direct` feature is enabled, this module can call AY's
//! native Rust API directly, eliminating subprocess spawning and text
//! file interchange. See issue #513 for context.

use anyhow::{Context, Result, bail};
use std::path::Path;
use std::process::Command;
use std::time::{Duration, Instant};
use trust_mc_metadata::HarnessMetadata;

use crate::args::AYSolver;
use crate::ay_parse::{
    build_cover_properties_from_sat_checks, build_coverage_results_from_sat_checks,
    build_success_properties, determine_failed_from_properties, load_vc_artifact,
    parse_cover_properties, parse_cover_sat_check_output, parse_coverage_results,
    parse_kani_any_trace, parse_solver_output, parse_violation_entry_names,
    parse_violation_properties, vc_artifact_path_for_smt,
};
use crate::coverage::cov_results::CoverageResults;
use crate::deadline::Deadline;
use crate::property_model::{CheckStatus, Property, PropertyId, RawSourceLocation};
use crate::session::{KaniSession, run_piped_with_timeout};
use crate::smt_io::{
    SmtLogicClass, build_cover_sat_query, classify_smt_logic_from_content, content_uses_horn_logic,
    extract_cover_declarations_from_content, extract_coverage_declarations_from_content,
    extract_reach_declarations_from_content, extract_violation_declarations_from_content,
};
use crate::verification_result::{
    FailedProperties, LogicTier, ProofCrosscheck, SolverUnknownReason, VerificationResult,
    VerificationStatus,
};

/// Default timeout for SMT solver processes (120 seconds).
/// This prevents runaway solver processes from consuming unbounded memory.
/// Can be overridden with --harness-timeout.
const DEFAULT_SOLVER_TIMEOUT_SECS: u64 = 120;

use crate::args::Timeout;

/// Resolve the effective solver timeout: explicit `--harness-timeout` wins,
/// otherwise fall back to `DEFAULT_SOLVER_TIMEOUT_SECS`.
///
/// Every solver path (standalone SMT, CHC,
/// RM-bypass BMC, AdaptivePortfolio) routes through this helper so the
/// default budget is defined exactly once.  Part of #3820.
pub(crate) fn solver_timeout_duration(harness_timeout: Option<Timeout>) -> Duration {
    harness_timeout.map(Duration::from).unwrap_or(Duration::from_secs(DEFAULT_SOLVER_TIMEOUT_SECS))
}

fn solver_error_is_timeout(err: &anyhow::Error) -> bool {
    err.chain().any(|cause| cause.to_string().contains(" timed out after "))
}

#[cfg(feature = "ay-chc-native")]
fn native_chc_error_allows_external_proof_fallback(err: &anyhow::Error) -> bool {
    err.chain().any(|cause| {
        let message = cause.to_string();
        message.contains("returned Unknown - verification inconclusive")
            || message.contains("exceeded guard timeout")
            // A fail-closed external invariant-model validation that could not
            // COMPLETE (the validator timed out) is inconclusive — it neither
            // confirms nor refutes the candidate proof — so external proof
            // fallback stays sound. This matches ONLY the timeout wording: a
            // decided "false proof detected: ... fails clause verification" is a
            // real refutation and must NOT enable fallback (so it is excluded by
            // requiring both "validation failed" and "timed out").
            || (message.contains("external invariant model validation failed")
                && message.contains("timed out"))
    })
}

mod chc;

impl KaniSession {
    /// Run AY verification on an SMT-LIB2 file.
    ///
    /// When `ay-direct` feature is enabled, tries direct AY linking first (no subprocess).
    /// Otherwise, Auto mode uses AY as the only production solver (bails if not found).
    ///
    /// The `--ay-solver` flag can be used to override solver selection:
    /// - `--ay-solver=ay` (default in Auto mode) for production use
    ///
    /// Returns an error if no solver is available (never returns false Success).
    ///
    /// `demoted_fallback_count`: per-harness DEMOTED (write-dropping) fallback count
    /// from metadata. When > 0, cross-check fires on PROOF to detect
    /// false proofs caused by dropped writes (#3788).
    ///
    /// `deadline`: per-harness wall-clock deadline. Every solver invocation
    /// below budgets itself as `min(tool_timeout, deadline.remaining())` so
    /// retries and secondary queries cannot exceed the harness budget.
    pub(crate) fn run_ay(
        &self,
        smt_file: &Path,
        harness: &HarnessMetadata,
        demoted_fallback_count: usize,
        deadline: Deadline,
    ) -> Result<VerificationResult> {
        let start = Instant::now();

        // Check if the SMT file exists
        if !smt_file.exists() {
            bail!(
                "SMT-LIB2 file not found: {}. The AY backend may not have generated it correctly.",
                smt_file.display()
            );
        }

        // #1377: Warn when #[kani::solver] attribute is used — it has no effect on AY.
        if harness.attributes.solver.is_some() {
            eprintln!(
                "Warning: `#[kani::solver]` attribute on harness `{}` is ignored by AY backend. \
                 Use --smt-solver (or --ay-solver) to configure AY solver selection.",
                harness.pretty_name
            );
        }

        // Part of #2942: Read SMT file once and pass content to all classification functions.
        let smt_content = std::fs::read_to_string(smt_file)
            .with_context(|| format!("Failed to read SMT file: {}", smt_file.display()))?;

        // #1910: Export SMT-LIB query for external solver cross-check.
        // #1921: Filter out model query commands (get-value/get-model) — some solvers
        // error on UNSAT because "model is not available" when the result is unsat.
        if let Some(export_path) = &self.args.export_smtlib {
            export_smtlib_filtered(smt_file, export_path)?;
            eprintln!("[export-smtlib] Exported query to: {}", export_path.display());
        }

        // CHC-COMP uses SMT-LIB/HORN input. The compiler already emits standard
        // HORN SMT-LIB for `--ay-chc`, so the export path shares the same filter
        // as `--export-smtlib` while guarding against accidental BMC input.
        if let Some(export_path) = &self.args.export_chc_comp {
            if !content_uses_horn_logic(&smt_content) {
                bail!("--export-chc-comp requires a HORN/CHC SMT-LIB query; rerun with `--ay-chc`");
            }
            export_smtlib_filtered(smt_file, export_path)?;
            eprintln!("[export-chc-comp] Exported CHC query to: {}", export_path.display());
        }

        // Classify the logic tier (LIA vs NIA/NRA/DT+BV/Arrays)
        // NIA policy: classify logic tier for solver strategy selection
        let logic_class = classify_smt_logic_from_content(&smt_content);
        let logic_tier = match logic_class {
            SmtLogicClass::Linear => LogicTier::TierA,
            SmtLogicClass::Nia | SmtLogicClass::Nra | SmtLogicClass::DtBvArrays => LogicTier::TierB,
        };
        let is_chc_file = content_uses_horn_logic(&smt_content);

        // Emit diagnostic message when incomplete logic is detected
        if logic_class != SmtLogicClass::Linear {
            let (prefix, logic_name) = match logic_class {
                SmtLogicClass::Nia => ("NIA", "non-linear integer arithmetic"),
                SmtLogicClass::Nra => ("NRA", "non-linear real arithmetic"),
                SmtLogicClass::DtBvArrays => {
                    ("DT+BV/Arrays", "datatypes combined with bitvectors/arrays (ay#1766)")
                }
                SmtLogicClass::Linear => unreachable!(),
            };
            eprintln!(
                "[{}] Detected {}; solver may be incomplete; \
                 results are demoted unless proof-validated.",
                prefix, logic_name
            );
        }

        // With ay-direct feature: try direct linking first (no subprocess)
        #[cfg(feature = "ay-direct")]
        {
            if !is_chc_file {
                // Direct linking is the preferred path - no subprocess, no text parsing.
                // HORN/CHC files use `declare-rel`/`rule`/`query`, which must be routed
                // through the native CHC solver instead of the plain SMT direct parser.
                match self.try_ay_direct(smt_file, harness, deadline) {
                    Ok((status, failed_properties, properties)) => {
                        let runtime = start.elapsed();
                        let validation_status = logic_tier.validation_status();
                        return Ok(VerificationResult {
                            status,
                            failed_properties,
                            results: properties,
                            runtime,
                            generated_concrete_test: false,
                            coverage_results: None,
                            logic_tier,
                            validation_status,
                            demotion_reasons: Vec::new(),
                            ctrex_category: None,
                            unknown_quality: None,
                            solver_unknown_reason: None,
                            kani_mem_overapprox_count: 0,
                            sound_fallback_count: 0,
                            proof_crosscheck: ProofCrosscheck::NotRun,
                            proof_qualifiers: Vec::new(),
                            proof_transcript_metadata: None,
                            native_full_verification_verdict: None,
                        });
                    }
                    Err(e) => {
                        // For Direct mode, fail hard - don't fall back to subprocess
                        #[cfg(feature = "ay-direct")]
                        if self.args.ay_solver == AYSolver::Direct {
                            bail!(
                                "Direct AY linking failed: {e}\n\
                                   Use --ay-solver=auto to fall back to subprocess-based solvers."
                            );
                        }
                        if self.args.common_args.verbose {
                            eprintln!(
                                "[AY-direct] Direct linking failed: {e}; falling back to subprocess"
                            );
                        }
                        // Fall through to subprocess-based solvers
                    }
                }
            }
        }

        // Without ay-direct feature, AYSolver::Direct is not in the enum, so
        // clap rejects it at parse time. No runtime guard needed.

        if is_chc_file {
            // Native ay-chc portfolio solver is the sole CHC engine.
            #[cfg(feature = "ay-chc-native")]
            {
                if self.args.common_args.verbose {
                    println!("[AY] Detected HORN logic - using ay-chc portfolio solver");
                }
                match self.try_ay_chc_solver(smt_file, harness, demoted_fallback_count, deadline) {
                    Ok(chc_result) => {
                        let runtime = start.elapsed();
                        let validation_status = logic_tier.validation_status();
                        return Ok(VerificationResult {
                            status: chc_result.status,
                            failed_properties: chc_result.failed_properties,
                            results: chc_result.properties,
                            runtime,
                            generated_concrete_test: false,
                            coverage_results: None,
                            logic_tier,
                            validation_status,
                            demotion_reasons: Vec::new(),
                            ctrex_category: None,
                            unknown_quality: None,
                            solver_unknown_reason: None,
                            kani_mem_overapprox_count: 0,
                            sound_fallback_count: 0,
                            proof_crosscheck: chc_result.proof_crosscheck,
                            proof_qualifiers: chc_result.proof_qualifiers,
                            proof_transcript_metadata: chc_result.proof_transcript_metadata,
                            native_full_verification_verdict: chc_result
                                .native_full_verification_verdict,
                        });
                    }
                    Err(e) => {
                        if native_chc_error_allows_external_proof_fallback(&e) {
                            match self.try_ay_chc_external_proof_fallback(
                                smt_file,
                                &smt_content,
                                harness,
                                deadline,
                            ) {
                                Ok(Some(chc_result)) => {
                                    let runtime = start.elapsed();
                                    let validation_status = logic_tier.validation_status();
                                    return Ok(VerificationResult {
                                        status: chc_result.status,
                                        failed_properties: chc_result.failed_properties,
                                        results: chc_result.properties,
                                        runtime,
                                        generated_concrete_test: false,
                                        coverage_results: None,
                                        logic_tier,
                                        validation_status,
                                        demotion_reasons: Vec::new(),
                                        ctrex_category: None,
                                        unknown_quality: None,
                                        solver_unknown_reason: None,
                                        kani_mem_overapprox_count: 0,
                                        sound_fallback_count: 0,
                                        proof_crosscheck: chc_result.proof_crosscheck,
                                        proof_qualifiers: chc_result.proof_qualifiers,
                                        proof_transcript_metadata: chc_result
                                            .proof_transcript_metadata,
                                        native_full_verification_verdict: chc_result
                                            .native_full_verification_verdict,
                                    });
                                }
                                Ok(None) => {}
                                Err(fallback_err) => {
                                    if self.args.common_args.verbose {
                                        eprintln!(
                                            "[AY] external ay fallback errored after native UNKNOWN: {fallback_err}"
                                        );
                                    }
                                }
                            }
                        }
                        eprintln!("[AY] ay-chc failed ({e}) — returning UNKNOWN",);
                        let runtime = start.elapsed();
                        let validation_status = logic_tier.validation_status();
                        let properties = vec![Property {
                            description: std::borrow::Cow::Borrowed(
                                "CHC verification: ay-chc inconclusive",
                            ),
                            property_id: PropertyId {
                                fn_name: None,
                                class: std::borrow::Cow::Borrowed("chc"),
                                id: 0,
                            },
                            source_location: RawSourceLocation {
                                column: None,
                                file: None,
                                function: None,
                                line: None,
                            },
                            status: CheckStatus::Failure,
                            trace: None,
                        }];
                        return Ok(VerificationResult {
                            status: VerificationStatus::Failure,
                            failed_properties: FailedProperties::Other,
                            results: properties,
                            runtime,
                            generated_concrete_test: false,
                            coverage_results: None,
                            logic_tier,
                            validation_status,
                            demotion_reasons: Vec::new(),
                            ctrex_category: None,
                            unknown_quality: None,
                            // Split the old catch-all: a pre-solve deadline bail is
                            // BUDGET-bound (no solving was attempted), anything else
                            // here is a genuine ay-chc error. Attribution only.
                            solver_unknown_reason: Some(SolverUnknownReason::from_chc_error(&e)),
                            kani_mem_overapprox_count: 0,
                            sound_fallback_count: 0,
                            proof_crosscheck: ProofCrosscheck::NotRun,
                            proof_qualifiers: Vec::new(),
                            proof_transcript_metadata: None,
                            native_full_verification_verdict: None,
                        });
                    }
                }
            }

            #[cfg(not(feature = "ay-chc-native"))]
            {
                bail!(
                    "CHC/HORN logic detected but ay-chc-native feature is not enabled.\n\
                     Build with `--features ay-chc-native` to enable CHC solving.\n\
                     SMT-LIB2 file generated at: {}",
                    smt_file.display()
                );
            }
        }

        let ay_available = which::which("ay").is_ok();

        let (status, failed_properties, properties, coverage_results) = match self.args.ay_solver {
            AYSolver::Auto | AYSolver::AY => {
                // AY is the sole production solver.
                if ay_available {
                    match self.try_ay_solver(smt_file, &smt_content, harness, deadline) {
                        Ok(result) => result,
                        Err(err) if solver_error_is_timeout(&err) => {
                            let timeout =
                                deadline.clamp(solver_timeout_duration(self.args.harness_timeout));
                            eprintln!(
                                "[AY] ay solver timed out after {:.1}s; returning UNKNOWN",
                                timeout.as_secs_f64()
                            );
                            let runtime = start.elapsed();
                            let validation_status = logic_tier.validation_status();
                            return Ok(VerificationResult {
                                status: VerificationStatus::Failure,
                                failed_properties: FailedProperties::Other,
                                results: Vec::new(),
                                runtime,
                                generated_concrete_test: false,
                                coverage_results: None,
                                logic_tier,
                                validation_status,
                                demotion_reasons: Vec::new(),
                                ctrex_category: None,
                                unknown_quality: None,
                                solver_unknown_reason: Some(SolverUnknownReason::Timeout),
                                kani_mem_overapprox_count: 0,
                                sound_fallback_count: 0,
                                proof_crosscheck: ProofCrosscheck::NotRun,
                                proof_qualifiers: Vec::new(),
                                proof_transcript_metadata: None,
                                native_full_verification_verdict: None,
                            });
                        }
                        Err(err) => return Err(err),
                    }
                } else {
                    bail!(
                        "AY solver not found in PATH. Install ay to run verification.\n\
                         SMT-LIB2 file generated at: {}",
                        smt_file.display()
                    );
                }
            }
            // With ay-direct feature, Direct should have returned in the direct-linking block above
            #[cfg(feature = "ay-direct")]
            AYSolver::Direct => {
                unreachable!("Direct mode should have been handled by ay-direct code path")
            }
        };

        let runtime = start.elapsed();
        let validation_status = logic_tier.validation_status();
        // Residual-775 MECH C: the external-solver `(error` path and the
        // preserved undecided-model path reach here as Failure/Other with NO
        // decided failing property — solver-side inconclusiveness that
        // previously carried no reason, so [AY:UNKNOWN_REASON:] never printed
        // and the scoreboard filed these as unknown:None. Stamp the reason for
        // exactly that shape (a DECIDED failure has a failing property and
        // keeps reason=None). Attribution only; verdicts unchanged.
        //
        // This is UndecidedModel, NOT SolverError: nothing errored, the model was
        // simply not decided. Sharing one label with real ay-chc errors is what
        // made the gate's largest bucket unactionable.
        let solver_unknown_reason = if status == VerificationStatus::Failure
            && matches!(failed_properties, FailedProperties::Other)
            && matches!(determine_failed_from_properties(&properties), FailedProperties::None)
        {
            Some(SolverUnknownReason::UndecidedModel)
        } else {
            None
        };
        Ok(VerificationResult {
            status,
            failed_properties,
            results: properties,
            runtime,
            generated_concrete_test: false,
            coverage_results,
            logic_tier,
            validation_status,
            demotion_reasons: Vec::new(),
            ctrex_category: None,
            unknown_quality: None,
            solver_unknown_reason,
            kani_mem_overapprox_count: 0,
            sound_fallback_count: 0,
            proof_crosscheck: ProofCrosscheck::NotRun,
            proof_qualifiers: Vec::new(),
            proof_transcript_metadata: None,
            native_full_verification_verdict: None,
        })
    }

    /// Try to run the native AY solver on an SMT-LIB2 file.
    ///
    /// Returns (status, failed_properties, properties) on success, error if AY not available.
    fn try_ay_solver(
        &self,
        smt_file: &Path,
        smt_content: &str,
        _harness: &HarnessMetadata,
        deadline: Deadline,
    ) -> Result<(VerificationStatus, FailedProperties, Vec<Property>, Option<CoverageResults>)>
    {
        // Check if ay is available
        let ay_path = which::which("ay")
            .map_err(|_| {
                anyhow::anyhow!(
                    "ay solver not found in PATH. Install ay or choose a different solver with `--ay-solver`.\n\
                     SMT-LIB2 file generated at: {}",
                    smt_file.display()
                )
            })?;

        // Note: AY's datatype theory (ay#517) is now fully implemented.
        // Previously, files with datatypes were rejected here. That guard
        // was removed in #1781 since AY-native now supports datatypes.

        if self.args.common_args.verbose {
            let msg = match self.args.ay_solver {
                AYSolver::Auto => "Falling back to ay solver",
                AYSolver::AY => "Running ay solver",
                #[cfg(feature = "ay-direct")]
                AYSolver::Direct => "Running ay solver",
            };
            println!("[AY] {msg}: {}", ay_path.display());
        }

        let timeout = deadline.clamp(solver_timeout_duration(self.args.harness_timeout));

        let mut cmd = Command::new(&ay_path);
        cmd.arg(smt_file);
        // Suppress ay's default proof pipeline: the driver never consumes the
        // `.alethe` certificate ay writes next to the input on UNSAT, and for
        // SMT inputs ay's own `--verify-proof` re-check cannot validate Alethe
        // anyway ("treated as not verified") — yet leaving the default on flips
        // ay's in-solver clause tracing + per-conflict LRAT materialization,
        // measured at ~80% of SAT-search time on a 92MB BMC instance (turning
        // solvable instances into timeouts). Zero verification value, full tax.
        // ay's independent model-validation battery is deliberately LEFT ON
        // (no `--no-validate`): it re-checks SAT models against the assertions,
        // which is genuine soundness value for counterexample classification.
        cmd.arg("--no-proof");
        cmd.arg("--no-verify-proof");
        // Give ay a cooperative deadline slightly inside the hard-kill window so
        // it can return `unknown (:reason-unknown "timeout")` + stats instead of
        // dying by SIGKILL mid-phase with no diagnostics. The subprocess hard
        // kill below remains the backstop.
        let cooperative_ms = timeout
            .as_millis()
            .saturating_sub(std::cmp::min(10_000, (timeout.as_millis() / 10) as u64) as u128);
        if cooperative_ms > 0 {
            cmd.arg("-t");
            cmd.arg(cooperative_ms.to_string());
        }
        let output = run_piped_with_timeout(cmd, timeout)?;

        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);

        if self.args.common_args.verbose {
            println!("[AY] ay output:\n{stdout}");
            if !stderr.is_empty() {
                eprintln!("[AY] ay stderr:\n{stderr}");
            }
        }

        // Parse result first to determine actual verification status.
        let (base_status, base_failed) = parse_solver_output(&stdout);
        let any_trace = if base_status == VerificationStatus::Failure {
            parse_kani_any_trace(&stdout)
        } else {
            Vec::new()
        };

        // #1164: Load VC artifact for source location mapping
        let vc_artifact_path = vc_artifact_path_for_smt(smt_file);
        let location_map = load_vc_artifact(&vc_artifact_path);
        if let Some(ref map) = location_map
            && self.args.common_args.verbose
        {
            println!("[AY] Loaded VC artifact with {} properties", map.len());
        }

        // If UNSAT (verification success), enumerate all checks as passed.
        // We can't use get-value output (model not available on UNSAT), so we
        // parse the SMT file for violation declarations instead.
        if base_status == VerificationStatus::Success {
            let violation_names = extract_violation_declarations_from_content(&smt_content);
            let cover_names = extract_cover_declarations_from_content(&smt_content);
            let coverage_names = extract_coverage_declarations_from_content(&smt_content);
            // #1164: Pass location map for source location population
            let mut properties = build_success_properties(&violation_names, location_map.as_ref());

            // Kani-parity UNREACHABLE classification: even on an all-SUCCESS
            // verdict, a check whose guard (path condition ∧ assumption
            // context) is infeasible must be reported UNREACHABLE, matching
            // Kani (e.g. an assertion in dead code).
            self.classify_unreachable_properties(
                smt_content,
                &violation_names,
                &mut properties,
                &ay_path,
                smt_file,
                deadline,
            );

            // Part of #1162: Compute cover semantics via secondary SAT checks.
            // When covers exist, run a secondary query to determine SATISFIED/UNSATISFIABLE
            // instead of leaving them as UNDETERMINED.
            let cover_properties = if !cover_names.is_empty() {
                let sat_results = self.check_cover_satisfiability(
                    smt_content,
                    &cover_names,
                    &ay_path,
                    smt_file,
                    deadline,
                );
                if self.args.common_args.verbose {
                    for (name, result) in cover_names.iter().zip(sat_results.iter()) {
                        let status_str = match result {
                            Some(true) => "SATISFIED",
                            Some(false) => "UNSATISFIABLE",
                            None => "UNDETERMINED",
                        };
                        println!("[AY] Cover check: {} -> {}", name, status_str);
                    }
                }
                build_cover_properties_from_sat_checks(
                    &cover_names,
                    &sat_results,
                    location_map.as_ref(),
                )
            } else {
                Vec::new()
            };
            properties.extend(cover_properties);
            let coverage_results = if self.args.coverage {
                if coverage_names.is_empty() {
                    Some(CoverageResults::empty())
                } else {
                    let sat_results = self.check_cover_satisfiability(
                        smt_content,
                        &coverage_names,
                        &ay_path,
                        smt_file,
                        deadline,
                    );
                    Some(build_coverage_results_from_sat_checks(
                        &coverage_names,
                        &sat_results,
                        location_map.as_ref(),
                    ))
                }
            } else {
                None
            };
            return Ok((base_status, base_failed, properties, coverage_results));
        }

        // For non-success results, check if there are real errors (not model errors)
        let has_real_error = (stderr.contains("(error") || stdout.contains("(error"))
            && !stderr.contains("model is not available")
            && !stdout.contains("model is not available");

        if has_real_error {
            if self.args.common_args.verbose {
                println!("[AY] ay reported error, treating as inconclusive");
            }
            return Ok((VerificationStatus::Failure, FailedProperties::Other, vec![], None));
        }

        // SAT result - parse get-value output to identify failed properties
        // #1164: Pass location map for source location population
        let mut properties =
            parse_violation_properties(&stdout, true, Some(&any_trace), location_map.as_ref());

        // Kani-parity all-properties classification: the single SAT model only
        // surfaces one (or a subset) of the failing checks. Re-query each
        // undecided violation flag individually (sat → FAILURE, unsat →
        // provably not violated, unknown → keep the model-based status). Kani
        // reports ALL failing checks; classifying from one model under-reports.
        let entry_names = parse_violation_entry_names(&stdout);
        let undecided: Vec<usize> = properties
            .iter()
            .enumerate()
            .take(entry_names.len())
            .filter(|(_, p)| p.status != CheckStatus::Failure)
            .map(|(i, _)| i)
            .collect();
        if !undecided.is_empty() {
            let names: Vec<String> = undecided.iter().map(|&i| entry_names[i].clone()).collect();
            let results =
                self.check_cover_satisfiability(smt_content, &names, &ay_path, smt_file, deadline);
            for (&i, result) in undecided.iter().zip(results.iter()) {
                if *result == Some(true) {
                    // The violation flag is satisfiable on its own: this check
                    // can fail, even though the first model did not surface it.
                    properties[i].status = CheckStatus::Failure;
                }
                // Some(false): provably not violated — stays SUCCESS and is
                // eligible for UNREACHABLE classification below.
                // None (unknown/error): keep the model-based classification;
                // never invent a status from an inconclusive solver answer.
            }
        }

        // UNREACHABLE classification for the remaining non-FAILURE checks.
        // Sound regardless of the re-query outcome: an unsat reach flag implies
        // the violation flag is unsat too (violation ⇒ reach).
        self.classify_unreachable_properties(
            smt_content,
            &entry_names,
            &mut properties,
            &ay_path,
            smt_file,
            deadline,
        );

        // Part of #922: Also parse cover properties
        let cover_properties = parse_cover_properties(&stdout, true, Some(&any_trace));
        properties.extend(cover_properties);
        let coverage_results = if self.args.coverage {
            Some(parse_coverage_results(&stdout, location_map.as_ref()))
        } else {
            None
        };

        let property_failed = determine_failed_from_properties(&properties);

        // Preserve the "undecided" signal from parse_solver_output (#3374).
        //
        // On the non-success path, `base_failed` is `FailedProperties::Other`, which
        // encodes "solver could not decide a concrete violation" — this covers `unknown`
        // (solver incompleteness, e.g. `(:reason-unknown incomplete)`) and `sat` with an
        // empty/undecided model. When the model carries no decided violation properties,
        // `determine_failed_from_properties` returns `None`, which would erase that signal
        // and cause `harness_runner` to misclassify the result as a Genuine counterexample.
        //
        // Only let the property-derived classification override `base_failed` when it
        // actually identified a decided failure (PanicsOnly/Other from a Failure property).
        // Otherwise fall back to `base_failed` so the undecided signal survives and the
        // `harness_runner` Other -> CtrexCategory::Unknown path fires.
        let failed_props = if matches!(property_failed, FailedProperties::None) {
            base_failed
        } else {
            property_failed
        };

        // Detect contradictory result: solver returned SAT but no violation predicate
        // is true in the model. This indicates solver incompleteness (e.g., ALL logic
        // with datatypes + bitvectors) or a codegen constraint issue.
        if base_status == VerificationStatus::Failure
            && !properties.is_empty()
            && properties.iter().all(|p| p.status != CheckStatus::Failure)
        {
            eprintln!(
                "warning: Solver returned SAT but no violation predicate is true in the model. \
                 This may indicate solver incompleteness with combined theories (ALL logic). \
                 Result is conservatively reported as inconclusive (UNKNOWN)."
            );
        }

        if self.args.common_args.verbose {
            println!("[AY] ay: Parsed {} properties", properties.len());
            for (i, prop) in properties.iter().enumerate() {
                println!("[AY]   {}: {} ({:?})", i, prop.description, prop.status);
            }
        }

        Ok((base_status, failed_props, properties, coverage_results))
    }

    /// Classify non-failing checks as UNREACHABLE via their reach flags.
    ///
    /// Kani parity: a check whose guard (path condition ∧ ordered assumption
    /// context at the check site) is infeasible is reported UNREACHABLE rather
    /// than SUCCESS — e.g. an assertion after a failed `kani::assert` (the
    /// assert-assume lowering makes the suffix path-constrained) or in dead
    /// code. The compiler emits a per-check flag `ay_reach_<suffix>` paired
    /// with `ay_violation_<suffix>`, defined as the check's guard; checks with
    /// a trivially-true guard have no flag and are left untouched.
    ///
    /// Soundness:
    /// - Only the solver's `unsat` answer upgrades a check to UNREACHABLE;
    ///   `sat`, `unknown`, or solver errors leave the existing status.
    /// - Only checks currently classified SUCCESS are considered; a FAILURE is
    ///   never reclassified.
    /// - The secondary query strips the violation disjunction (and check-sat /
    ///   get-value), so it asks exactly "is this guard satisfiable under the
    ///   program constraints".
    ///
    /// `violation_names[i]` must correspond to `properties[i]` (both the UNSAT
    /// path via declaration order and the SAT path via get-value output order
    /// maintain this alignment).
    fn classify_unreachable_properties(
        &self,
        smt_content: &str,
        violation_names: &[String],
        properties: &mut [Property],
        ay_path: &Path,
        smt_file: &Path,
        deadline: Deadline,
    ) {
        let reach_decls: std::collections::HashSet<String> =
            extract_reach_declarations_from_content(smt_content).into_iter().collect();
        if reach_decls.is_empty() {
            return;
        }

        let mut candidate_idxs = Vec::new();
        let mut reach_names = Vec::new();
        for (i, violation_name) in violation_names.iter().enumerate() {
            if i >= properties.len() {
                break;
            }
            if properties[i].status != CheckStatus::Success {
                continue;
            }
            let Some(suffix) = violation_name.strip_prefix("ay_violation_") else {
                continue;
            };
            let reach_name = format!("ay_reach_{suffix}");
            if reach_decls.contains(&reach_name) {
                candidate_idxs.push(i);
                reach_names.push(reach_name);
            }
        }
        if reach_names.is_empty() {
            return;
        }

        let results =
            self.check_cover_satisfiability(smt_content, &reach_names, ay_path, smt_file, deadline);
        for (&i, result) in candidate_idxs.iter().zip(results.iter()) {
            // Soundness rule: only a definitive `unsat` from the solver may be
            // upgraded to UNREACHABLE. `unknown` is never upgraded.
            if *result == Some(false) {
                properties[i].status = CheckStatus::Unreachable;
            }
        }
        if self.args.common_args.verbose {
            for (name, result) in reach_names.iter().zip(results.iter()) {
                let status_str = match result {
                    Some(true) => "reachable",
                    Some(false) => "UNREACHABLE",
                    None => "undetermined",
                };
                println!("[AY] Reachability check: {} -> {}", name, status_str);
            }
        }
    }

    /// Run a secondary solver query to determine cover property satisfiability.
    ///
    /// When the main verification query returns UNSAT, the model is not available
    /// and cover property values cannot be read via get-value. This method constructs
    /// a secondary SMT query with push/pop blocks that checks each cover property
    /// individually, producing SATISFIED/UNSATISFIABLE results.
    ///
    /// Part of #1162: Compute proper cover semantics on UNSAT.
    ///
    /// REQUIRES: smt_content is valid SMT-LIB2 content from the main query
    /// REQUIRES: cover_names are non-empty cover variable names
    /// REQUIRES: solver_path points to a valid SMT solver executable
    /// ENSURES: result.len() == cover_names.len()
    /// ENSURES: each result is Some(true) for SAT, Some(false) for UNSAT, None for error
    fn check_cover_satisfiability(
        &self,
        smt_content: &str,
        cover_names: &[String],
        solver_path: &Path,
        smt_file: &Path,
        deadline: Deadline,
    ) -> Vec<Option<bool>> {
        if cover_names.is_empty() {
            return Vec::new();
        }

        let cover_query = build_cover_sat_query(smt_content, cover_names);

        // Write the secondary query to a temp file next to the original
        let cover_smt_path = smt_file.with_extension("cover_check.smt2");
        if let Err(e) = std::fs::write(&cover_smt_path, &cover_query) {
            if self.args.common_args.verbose {
                eprintln!("[AY] Failed to write cover check SMT file: {e}");
            }
            return vec![None; cover_names.len()];
        }

        let timeout = deadline.clamp(solver_timeout_duration(self.args.harness_timeout));

        let mut cmd = Command::new(solver_path);
        cmd.arg(&cover_smt_path);
        let output = match run_piped_with_timeout(cmd, timeout) {
            Ok(output) => output,
            Err(e) => {
                if self.args.common_args.verbose {
                    eprintln!("[AY] Cover check solver failed: {e}");
                }
                // Clean up temp file on error
                let _ = std::fs::remove_file(&cover_smt_path);
                return vec![None; cover_names.len()];
            }
        };

        let stdout = String::from_utf8_lossy(&output.stdout);

        if self.args.common_args.verbose {
            println!("[AY] Cover check output:\n{stdout}");
        }

        let results = parse_cover_sat_check_output(&stdout, cover_names.len());

        // Clean up temp file
        let _ = std::fs::remove_file(&cover_smt_path);

        results
    }

    /// Run a secondary solver query to determine cover property satisfiability
    /// from CHC/HORN content.
    ///
    /// CHC files use `(set-logic HORN)` with `(declare-rel)`, `(rule)`, and
    /// `(query)` constructs that standard SMT solvers cannot process. This method
    /// builds a plain SMT query by stripping CHC-specific constructs and checking
    /// each cover property individually.
    ///
    /// Part of #1162: Cover semantics for CHC path.
    ///
    /// Deadline note: this helper is invoked from deep inside the CHC
    /// result-interpretation paths (`native_result.rs`), which do not carry
    /// the per-harness [`Deadline`]. Its subprocess budget is the per-call
    /// solver timeout, additionally clamped to the process-wide watchdog
    /// deadline inside `run_piped_with_timeout` — so it cannot outlive the
    /// driver budget, but may slightly overshoot the per-harness deadline.
    ///
    /// REQUIRES: chc_content is valid CHC/HORN SMT-LIB2 content
    /// REQUIRES: cover_names are non-empty cover variable names
    /// ENSURES: result.len() == cover_names.len()
    /// ENSURES: each result is Some(true) for SAT, Some(false) for UNSAT, None for error
    pub(crate) fn check_cover_satisfiability_for_chc(
        &self,
        chc_content: &str,
        cover_names: &[String],
        smt_file: &Path,
    ) -> Vec<Option<bool>> {
        use crate::smt_io::build_cover_sat_query_for_chc;

        if cover_names.is_empty() {
            return Vec::new();
        }

        let cover_query = build_cover_sat_query_for_chc(chc_content, cover_names);

        // Normalize ay_bindings' qualified syntax for external solver consumption
        let cover_query = normalize_smt_qualified_syntax(&cover_query);

        // Write the secondary query to a temp file next to the original
        let cover_smt_path = smt_file.with_extension("cover_chc_check.smt2");
        if let Err(e) = std::fs::write(&cover_smt_path, &cover_query) {
            if self.args.common_args.verbose {
                eprintln!("[AY] Failed to write CHC cover check SMT file: {e}");
            }
            return vec![None; cover_names.len()];
        }

        let solver_path = which::which("ay").ok();
        let Some(solver_path) = solver_path else {
            if self.args.common_args.verbose {
                eprintln!("[AY] No ay solver found for CHC cover check");
            }
            let _ = std::fs::remove_file(&cover_smt_path);
            return vec![None; cover_names.len()];
        };

        let timeout = solver_timeout_duration(self.args.harness_timeout);

        let mut cmd = Command::new(&solver_path);
        cmd.arg(&cover_smt_path);
        let output = match run_piped_with_timeout(cmd, timeout) {
            Ok(output) => output,
            Err(e) => {
                if self.args.common_args.verbose {
                    eprintln!("[AY] CHC cover check solver failed: {e}");
                }
                let _ = std::fs::remove_file(&cover_smt_path);
                return vec![None; cover_names.len()];
            }
        };

        let stdout = String::from_utf8_lossy(&output.stdout);

        if self.args.common_args.verbose {
            println!("[AY] CHC cover check output:\n{stdout}");
        }

        let results = parse_cover_sat_check_output(&stdout, cover_names.len());

        // Clean up temp file
        let _ = std::fs::remove_file(&cover_smt_path);

        results
    }
}

/// Normalize ay_bindings' SMT-LIB2 syntax for standard compliance (Part of #3094, #3465).
///
/// ay_bindings emits `(as Constructor Sort)` for sort-qualified constructors
/// and testers. Standard SMT-LIB2 expects the unqualified form in two contexts:
///
/// 1. **Testers**: `(_ is (as Ctor Sort))` → `(_ is Ctor)`
/// 2. **Constructor applications**: `((as Ctor Sort) args)` → `(Ctor args)`
///
/// ay_bindings also formats FP rounding-mode literals as short internal atoms
/// (`RNE`, `RTZ`, ...) while the SMT-LIB standard uses long names
/// (`roundNearestTiesToEven`, `roundTowardZero`, ...).
///
/// This function rewrites `(as X Y)` to just `X` when Y is a simple symbol
/// (not a parenthesized sort like `(Array ...)`), preserving `(as const (Array ...))`,
/// then normalizes standalone FP rounding-mode tokens to the standard SMT-LIB names.
pub(crate) fn normalize_smt_qualified_syntax(smt_content: &str) -> String {
    let mut result = String::with_capacity(smt_content.len());
    let mut remaining = smt_content;

    while let Some(pos) = remaining.find("(as ") {
        // Copy everything before the match
        result.push_str(&remaining[..pos]);

        let after_prefix = &remaining[pos + "(as ".len()..];
        // Find the first symbol (constructor name, ends at space)
        if let Some(space_pos) = after_prefix.find(' ') {
            let symbol = &after_prefix[..space_pos];
            let after_symbol = &after_prefix[space_pos + 1..];

            // Check if the sort argument is a simple symbol (not parenthesized).
            // Preserve `(as const (Array ...))` and similar built-in uses.
            if !after_symbol.starts_with('(') {
                // Simple sort: `(as Ctor SortName)` -> `Ctor`
                if let Some(close_pos) = after_symbol.find(')') {
                    result.push_str(symbol);
                    remaining = &after_symbol[close_pos + 1..];
                    continue;
                }
            }
        }
        // If parsing fails or sort is parenthesized, keep the `(as ` prefix
        result.push_str("(as ");
        remaining = after_prefix;
    }

    // Copy the rest
    result.push_str(remaining);
    rewrite_rounding_mode_tokens(&result)
}

fn normalize_rounding_mode_token(token: &str) -> Option<&'static str> {
    match token {
        "RNE" | "roundNearestTiesToEven" => Some("roundNearestTiesToEven"),
        "RNA" | "roundNearestTiesToAway" => Some("roundNearestTiesToAway"),
        "RTP" | "roundTowardPositive" => Some("roundTowardPositive"),
        "RTN" | "roundTowardNegative" => Some("roundTowardNegative"),
        "RTZ" | "roundTowardZero" => Some("roundTowardZero"),
        _ => None,
    }
}

fn is_simple_symbol_char(ch: char) -> bool {
    ch.is_ascii_alphanumeric()
        || matches!(
            ch,
            '~' | '!'
                | '@'
                | '$'
                | '%'
                | '^'
                | '&'
                | '*'
                | '_'
                | '-'
                | '+'
                | '='
                | '<'
                | '>'
                | '.'
                | '?'
                | '/'
                | ':'
        )
}

fn rewrite_rounding_mode_tokens(smt_content: &str) -> String {
    fn rewrite_token(token: &str) -> &str {
        normalize_rounding_mode_token(token).unwrap_or(token)
    }

    let mut result = String::with_capacity(smt_content.len());
    let mut token = String::new();
    let mut in_string = false;
    let mut in_quoted_symbol = false;
    let mut in_line_comment = false;
    let mut escaped = false;

    let flush_token = |result: &mut String, token: &mut String| {
        if !token.is_empty() {
            result.push_str(rewrite_token(token));
            token.clear();
        }
    };

    for ch in smt_content.chars() {
        if in_line_comment {
            result.push(ch);
            if ch == '\n' {
                in_line_comment = false;
            }
            continue;
        }

        if in_string {
            result.push(ch);
            if escaped {
                escaped = false;
            } else if ch == '\\' {
                escaped = true;
            } else if ch == '"' {
                in_string = false;
            }
            continue;
        }

        if in_quoted_symbol {
            result.push(ch);
            if ch == '|' {
                in_quoted_symbol = false;
            }
            continue;
        }

        match ch {
            ';' => {
                flush_token(&mut result, &mut token);
                in_line_comment = true;
                result.push(ch);
            }
            '"' => {
                flush_token(&mut result, &mut token);
                in_string = true;
                result.push(ch);
            }
            '|' => {
                flush_token(&mut result, &mut token);
                in_quoted_symbol = true;
                result.push(ch);
            }
            _ if is_simple_symbol_char(ch) => token.push(ch),
            _ => {
                flush_token(&mut result, &mut token);
                result.push(ch);
            }
        }
    }

    flush_token(&mut result, &mut token);
    result
}

/// Export SMT-LIB file with model query commands filtered out.
///
/// Model query commands (e.g. `get-value`, `get-model`) cause some solvers to
/// error with "model is not available" when the result is UNSAT. For cross-checking
/// with external solvers, we strip these lines so the exported file is consumable
/// regardless of the solver result.
fn export_smtlib_filtered(src: &Path, dst: &Path) -> anyhow::Result<()> {
    fn is_model_query_command_start(trimmed_line: &str) -> bool {
        trimmed_line.starts_with("(get-value") || trimmed_line.starts_with("(get-model")
    }

    fn smtlib_line_paren_balance(line: &str) -> i64 {
        let mut balance: i64 = 0;
        let mut in_string = false;
        let mut in_quoted_symbol = false;
        let mut escaped = false;

        for ch in line.chars() {
            if in_string {
                if escaped {
                    escaped = false;
                    continue;
                }
                match ch {
                    '\\' => escaped = true,
                    '"' => in_string = false,
                    _ => {}
                }
                continue;
            }
            if in_quoted_symbol {
                if ch == '|' {
                    in_quoted_symbol = false;
                }
                continue;
            }

            match ch {
                ';' => break, // comment to end-of-line
                '"' => in_string = true,
                '|' => in_quoted_symbol = true,
                '(' => balance += 1,
                ')' => balance -= 1,
                _ => {}
            }
        }

        balance
    }

    use std::io::{BufRead, BufReader, Write};

    let input = std::fs::File::open(src)
        .with_context(|| format!("Failed to read SMT-LIB file {}", src.display()))?;
    let reader = BufReader::new(input);

    let mut output = std::fs::File::create(dst)
        .with_context(|| format!("Failed to create {}", dst.display()))?;

    // #1921: Some solvers reject model query commands on UNSAT. We want the exported file to be
    // consumable regardless of the solver's sat result, so we strip these commands.
    //
    // We filter by top-level command and track parenthesis balance so multi-line
    // (get-value ...) forms are removed without leaving trailing syntax behind.
    let mut skip_balance: i64 = 0;
    for (line_no, line) in reader.lines().enumerate() {
        let line_no = line_no + 1;
        let line =
            line.with_context(|| format!("Failed to read line {line_no} from {}", src.display()))?;

        if skip_balance == 0 {
            // Note: We filter on "starts_with" to avoid rewriting arbitrary content.
            let trimmed = line.trim_start();
            if is_model_query_command_start(trimmed) {
                skip_balance = smtlib_line_paren_balance(&line);
                if skip_balance < 0 {
                    anyhow::bail!(
                        "Malformed SMT-LIB: unmatched ')' while filtering model query command at {}:{}",
                        src.display(),
                        line_no
                    );
                }
                continue;
            }
            writeln!(output, "{}", line)?;
            continue;
        }

        skip_balance += smtlib_line_paren_balance(&line);
        if skip_balance < 0 {
            anyhow::bail!(
                "Malformed SMT-LIB: unmatched ')' while filtering model query command at {}:{}",
                src.display(),
                line_no
            );
        }
    }

    if skip_balance != 0 {
        anyhow::bail!(
            "Malformed SMT-LIB: unterminated model query command while filtering {}",
            src.display()
        );
    }

    Ok(())
}

#[cfg(test)]
mod tests;
