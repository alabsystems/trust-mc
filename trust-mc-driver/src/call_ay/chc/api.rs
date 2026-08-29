// Copyright 2026 Andrew Yates, Inc.
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Programmatic native CHC solving API.
//!
//! This module accepts HORN SMT-LIB text directly and returns a compact solver
//! verdict without requiring a `KaniSession`, harness metadata, or `.smt2`
//! artifact path. CLI-specific property mapping stays in `native.rs`.

use std::sync::OnceLock;
use std::time::Duration;

use ay::chc::{AdaptiveConfig, AdaptivePortfolio, ChcParser, InvariantModel, VerifiedChcResult};
use regex::Regex;
use trust_mc_core::full_verifier::{
    ChcPdrCounterexampleEvidence, ChcPdrProofEvidence, ChcPdrReport, ChcPdrStats, UnknownReason,
};

use crate::smt_io::strip_cover_assertions_for_chc_solver;

/// Concat rewrite policy for the native CHC parser.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
#[non_exhaustive]
pub(crate) enum ChcConcatRewrite {
    /// Pass SMT text through unchanged.
    #[default]
    Off,
    /// Compatibility alias retained for callers that previously requested concat rewriting.
    Arith,
}

/// Optional native CHC transformations to run before solving.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
#[non_exhaustive]
pub(crate) struct ChcTransformOptions {
    /// Enable transform execution.
    pub enabled: bool,
    /// Transform pass names. Empty or containing `"all"` runs all supported passes.
    pub passes: Vec<String>,
}

/// Configuration for session-free native CHC solving.
#[derive(Clone, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub(crate) struct ProgrammaticChcConfig {
    /// Adaptive portfolio budget.
    pub timeout: Duration,
    /// Extra wall-clock allowance beyond `timeout` for solver shutdown.
    pub guard_slack: Duration,
    /// Emit ay-chc verbose diagnostics.
    pub verbose: bool,
    /// Reject trust-backed ay-chc fallbacks without independent proof evidence.
    pub validate: bool,
    /// Parser compatibility rewrite for concat terms.
    pub concat_rewrite: ChcConcatRewrite,
    /// Native CHC pre-solve transformations.
    pub transforms: ChcTransformOptions,
}

impl Default for ProgrammaticChcConfig {
    fn default() -> Self {
        Self {
            timeout: Duration::from_secs(120),
            guard_slack: Duration::from_secs(5),
            verbose: false,
            validate: true,
            concat_rewrite: ChcConcatRewrite::Off,
            transforms: ChcTransformOptions::default(),
        }
    }
}

/// Session-free CHC solver verdict.
#[derive(Clone, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub(crate) enum ProgrammaticChcVerdict {
    /// The queried error predicate is unreachable.
    Safe { invariant_count: usize },
    /// The queried error predicate is reachable.
    Unsafe { counterexample_steps: usize },
    /// The solver could not determine a validated verdict.
    Unknown { reason: String },
}

/// Result of a programmatic CHC solve.
#[derive(Clone, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub(crate) struct ProgrammaticChcSolveResult {
    /// Final solver verdict.
    pub verdict: ProgrammaticChcVerdict,
    /// Predicate count after parsing and configured transformations.
    pub predicate_count: usize,
    /// Clause count after parsing and configured transformations.
    pub clause_count: usize,
}

impl ProgrammaticChcSolveResult {
    /// Converts the session-free ay-chc result into the stable full-verifier
    /// CHC/PDR report shape.
    #[must_use]
    pub(crate) fn into_chc_pdr_report(self) -> ChcPdrReport {
        let stats =
            ChcPdrStats { relation_count: self.predicate_count, clause_count: self.clause_count };

        match self.verdict {
            ProgrammaticChcVerdict::Safe { invariant_count } => {
                let evidence = if invariant_count == 0 {
                    ChcPdrProofEvidence::chc_validity(stats)
                } else {
                    ChcPdrProofEvidence::pdr_invariant(stats, invariant_count)
                };
                ChcPdrReport::proved(evidence)
            }
            ProgrammaticChcVerdict::Unsafe { counterexample_steps } => {
                ChcPdrReport::counterexample(
                    stats,
                    ChcPdrCounterexampleEvidence::new(counterexample_steps),
                )
            }
            ProgrammaticChcVerdict::Unknown { reason } => {
                ChcPdrReport::unknown(stats, classify_programmatic_unknown(reason))
            }
        }
    }
}

/// Solve HORN SMT-LIB text using the native ay-chc adaptive portfolio.
///
/// Parse/rewriter failures are returned as `Err`. Solver timeouts, panics, and
/// inconclusive results are returned as `Ok(Unknown { .. })` so callers can
/// decide their own fail-open/fail-closed policy.
pub(crate) fn solve_chc_smt_str(
    smt_content: &str,
    config: &ProgrammaticChcConfig,
) -> anyhow::Result<ProgrammaticChcSolveResult> {
    let smt_content = preprocess_smt_content(smt_content, config.concat_rewrite)?;

    if chc_smt_is_trivially_safe(&smt_content) {
        return Ok(ProgrammaticChcSolveResult {
            verdict: ProgrammaticChcVerdict::Safe { invariant_count: 0 },
            predicate_count: 1,
            clause_count: 0,
        });
    }

    let mut problem = ChcParser::parse(&smt_content)
        .map_err(|e| anyhow::anyhow!("failed to parse CHC problem: {e}"))?;

    problem.expand_nullary_fail_queries(config.verbose);
    apply_transforms(&mut problem, &config.transforms, config.verbose);

    let predicate_count = problem.predicates().len();
    let clause_count = problem.clauses().len();

    let mut adaptive_config = AdaptiveConfig::with_budget(config.timeout, config.verbose);
    adaptive_config.strict_proofs = config.validate;

    let solver = AdaptivePortfolio::new(problem, adaptive_config);
    let solve_result = solve_with_guard(solver, config.timeout, config.guard_slack);

    let verdict = match solve_result {
        Ok(VerifiedChcResult::Safe(verified_inv)) => {
            if !verify_safe_model(&smt_content, verified_inv.model(), config.verbose) {
                ProgrammaticChcVerdict::Unknown {
                    reason: "validated invariant failed fresh clause verification".to_string(),
                }
            } else {
                ProgrammaticChcVerdict::Safe { invariant_count: verified_inv.model().len() }
            }
        }
        Ok(VerifiedChcResult::Unsafe(verified_cex)) => {
            let steps = verified_cex.counterexample().steps.len();
            if steps == 0 {
                ProgrammaticChcVerdict::Unknown {
                    reason: "0-step counterexample is inconclusive".to_string(),
                }
            } else {
                ProgrammaticChcVerdict::Unsafe { counterexample_steps: steps }
            }
        }
        Ok(VerifiedChcResult::Unknown(_)) => ProgrammaticChcVerdict::Unknown {
            reason: "adaptive portfolio returned unknown".to_string(),
        },
        Ok(_) => ProgrammaticChcVerdict::Unknown {
            reason: "adaptive portfolio returned unrecognized CHC result".to_string(),
        },
        Err(reason) => ProgrammaticChcVerdict::Unknown { reason },
    };

    Ok(ProgrammaticChcSolveResult { verdict, predicate_count, clause_count })
}

fn classify_programmatic_unknown(reason: String) -> UnknownReason {
    let lower = reason.to_ascii_lowercase();
    if lower.contains("timeout") || lower.contains("exceeded guard") {
        UnknownReason::Timeout
    } else if lower.contains("failed fresh clause verification") || lower.contains("0-step") {
        UnknownReason::Demoted(reason)
    } else {
        UnknownReason::SolverReturnedUnknown
    }
}

fn preprocess_smt_content(
    smt_content: &str,
    concat_rewrite: ChcConcatRewrite,
) -> anyhow::Result<String> {
    let smt_content = match concat_rewrite {
        ChcConcatRewrite::Off => smt_content.to_string(),
        ChcConcatRewrite::Arith => smt_content.to_string(),
    };

    static BV2INT_RE: OnceLock<Regex> = OnceLock::new();
    let re =
        BV2INT_RE.get_or_init(|| Regex::new(r"\(bv2int #x([0-9a-fA-F]+)\)").expect("valid regex"));
    Ok(re
        .replace_all(&smt_content, |caps: &regex::Captures<'_>| {
            u128::from_str_radix(&caps[1], 16)
                .map(|v| v.to_string())
                .unwrap_or_else(|_| caps[0].to_string())
        })
        .into_owned())
    .map(|rewritten| strip_cover_assertions_for_chc_solver(&rewritten))
}

/// Detect CHC systems where `error` is queried but no rule can derive it.
pub(crate) fn chc_smt_is_trivially_safe(smt_content: &str) -> bool {
    super::smt_analysis::smt_error_query_is_trivially_safe(smt_content)
}

fn apply_transforms(
    problem: &mut ay::chc::ChcProblem,
    transforms: &ChcTransformOptions,
    verbose: bool,
) {
    if !transforms.enabled {
        return;
    }

    let all = transforms.passes.is_empty() || transforms.passes.iter().any(|s| s == "all");
    if all || transforms.passes.iter().any(|s| s == "scalarize") {
        problem.try_scalarize_const_array_selects();
    }
    if all || transforms.passes.iter().any(|s| s == "split-ite") {
        problem.try_split_ites_in_clauses(8, verbose);
    }
    if all || transforms.passes.iter().any(|s| s == "split-or") {
        problem.try_split_ors_in_clauses(8, verbose);
    }
}

fn solve_with_guard(
    solver: AdaptivePortfolio,
    timeout: Duration,
    guard_slack: Duration,
) -> Result<VerifiedChcResult, String> {
    // Held across the move so the guard-timeout arm can cancel the solve
    // instead of orphaning a thread that keeps burning cores after we have
    // stopped waiting for its answer. Cancellation only ever degrades a verdict
    // to Unknown, and this arm discards the verdict anyway.
    let (tx, rx) = std::sync::mpsc::channel();
    let cancel = solver.cancellation_handle();
    let solver_thread = std::thread::spawn(move || {
        let result = solver.try_solve();
        let _ = tx.send(result);
    });

    if timeout.is_zero() {
        let result = rx.recv().map_err(|e| format!("solver thread ended without result: {e}"))?;
        let _ = solver_thread.join();
        return result.map_err(|reason| format!("ay-chc panic during adaptive solve: {reason}"));
    }

    let guard_timeout = timeout + guard_slack;
    match rx.recv_timeout(guard_timeout) {
        Ok(result) => {
            let _ = solver_thread.join();
            result.map_err(|reason| format!("ay-chc panic during adaptive solve: {reason}"))
        }
        Err(_) => {
            cancel.cancel();
            let _ = rx.recv_timeout(Duration::from_secs(3));
            Err(format!("ay-chc portfolio exceeded guard timeout ({guard_timeout:?})"))
        }
    }
}

fn verify_safe_model(smt_content: &str, model: &InvariantModel, verbose: bool) -> bool {
    let Ok(verify_problem) = ChcParser::parse(smt_content) else {
        return false;
    };
    let mut pdr_config = ay::chc::PdrConfig::default();
    pdr_config.verbose = verbose;
    let mut verifier = ay::chc::engines::new_pdr_solver(verify_problem, pdr_config);
    verifier.verify_model(model)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn detects_trivially_safe_chc_without_error_rule() {
        let smt = "\
(set-logic HORN)
(declare-rel error ())
(query error)
";

        assert!(chc_smt_is_trivially_safe(smt));
    }

    #[test]
    fn solve_short_circuits_trivially_safe_chc() {
        let smt = "\
(set-logic HORN)
(declare-rel error ())
(query error)
";

        let result = solve_chc_smt_str(smt, &ProgrammaticChcConfig::default()).unwrap();

        assert_eq!(result.verdict, ProgrammaticChcVerdict::Safe { invariant_count: 0 });
    }

    #[test]
    fn programmatic_chc_strips_post_query_cover_metadata_before_parse() {
        let smt = "\
(set-logic HORN)
(declare-rel error ())
(rule (=> false error))
(query error)
(declare-const ay_cover_0 Bool)
(assert (= ay_cover_0 true))
";

        let processed = preprocess_smt_content(smt, ChcConcatRewrite::Off).unwrap();
        assert!(!processed.contains("ay_cover_"));

        let result = solve_chc_smt_str(
            smt,
            &ProgrammaticChcConfig {
                timeout: Duration::from_secs(5),
                guard_slack: Duration::from_secs(1),
                ..ProgrammaticChcConfig::default()
            },
        )
        .unwrap();

        assert!(matches!(result.verdict, ProgrammaticChcVerdict::Safe { .. }));
    }

    #[test]
    fn safe_programmatic_chc_result_maps_to_full_chc_pdr_proof() {
        let result = ProgrammaticChcSolveResult {
            verdict: ProgrammaticChcVerdict::Safe { invariant_count: 2 },
            predicate_count: 3,
            clause_count: 7,
        };

        let report = result.into_chc_pdr_report();

        assert_eq!(report.stats, ChcPdrStats { relation_count: 3, clause_count: 7 });
        assert!(matches!(
            report.verdict,
            trust_mc_core::full_verifier::ChcPdrVerdict::Proved(ref evidence)
                if evidence.kind == trust_mc_core::full_verifier::ChcPdrProofKind::PdrInvariant
                    && evidence.invariant_count == 2
                    && evidence.stats == ChcPdrStats { relation_count: 3, clause_count: 7 }
        ));
    }

    #[test]
    fn bounded_bmc_has_no_programmatic_full_proof_mapping() {
        let result = ProgrammaticChcSolveResult {
            verdict: ProgrammaticChcVerdict::Unknown {
                reason: "bounded BMC success is diagnostic only".to_string(),
            },
            predicate_count: 0,
            clause_count: 0,
        };

        let report = result.into_chc_pdr_report();

        assert!(matches!(
            report.verdict,
            trust_mc_core::full_verifier::ChcPdrVerdict::Unknown(
                UnknownReason::SolverReturnedUnknown
            )
        ));
    }

    #[test]
    fn exposes_concat_rewrite_option() {
        let config = ProgrammaticChcConfig {
            concat_rewrite: ChcConcatRewrite::Arith,
            ..ProgrammaticChcConfig::default()
        };

        assert_eq!(config.concat_rewrite, ChcConcatRewrite::Arith);
    }

    #[test]
    fn keeps_error_derivation_non_trivial() {
        let smt = "\
(set-logic HORN)
(declare-rel error ())
(rule error)
(query error)
";

        assert!(!chc_smt_is_trivially_safe(smt));
    }
}
