// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Informational proof summary pointer artifact.
//!
//! This module intentionally does not implement replacement-audit validation.
//! It summarizes ordinary verification results and points reviewers to the
//! authoritative replacement proof extraction and audit flow.

use std::fs::File;
use std::io::{BufWriter, Write};
use std::path::Path;

use anyhow::{Context, Result};
use serde::Serialize;

use crate::demotion::is_effective_manual_success;
use crate::harness_runner::HarnessResult;
use crate::property_model::{CheckStatus, Property};
use crate::session::KaniSession;
use crate::verification_provenance::SolverUnknownReason;
use crate::verification_result::{
    CtrexCategory, FailedProperties, VacuityShape, ValidationStatus, VerificationResult,
    VerificationStatus, classify_vacuity,
};

/// What actually happened to a harness, at the granularity the CONSOLE channel
/// has always reported it.
///
/// `--proof-summary-json`, `--sarif` and `--summary` all rendered three very
/// different pieces of news as the same `"status": "failure"` shape:
///
///   * VACUOUS — the assumptions contradict each other, so every check is
///     unreachable and nothing was verified;
///   * INCONCLUSIVE — the solver never decided, so the harness is neither
///     proved nor refuted;
///   * a refuted assertion — the code really is wrong.
///
/// The fixes are respectively "your assumptions are contradictory", "give it a
/// longer budget or --ay-chc", and "fix your code". A CI job reading only the
/// JSON could not tell which it had, and the console channel that could was a
/// prose stream nobody parses.
///
/// The arms below mirror `verification_result::format_result`'s verdict chain
/// in the same order, so the two channels cannot drift into disagreeing about
/// the same run. The one arm the console does not have is
/// [`HarnessVerdict::UncertifiedCounterexample`]: it prints that as a separate
/// `[AY:CTREX_NOT_CERTIFIED]` line beside `FAILED`, which a JSON consumer has
/// no way to read.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum HarnessVerdict {
    /// Proved (including a `should_panic` harness that panicked as expected).
    Successful,
    /// Proved, but on an unvalidated solver tier — provisional.
    SuccessfulUnvalidated,
    /// Every check is provably UNREACHABLE: contradictory assumptions.
    Vacuous,
    /// Every check is provably UNREACHABLE, but the harness itself is reachable
    /// — the checks sit on dead code, not on contradictory assumptions.
    InconclusiveDeadChecks,
    /// The solver had obligations and could not settle them.
    InconclusiveUndecided,
    /// There were no obligations at all — a proof of nothing.
    InconclusiveNoChecks,
    /// A counterexample the driver declined to certify as genuine.
    UncertifiedCounterexample,
    /// Refuted on an unvalidated solver tier.
    Unvalidated,
    /// An ordinary refutation: a check really can fail.
    Failed,
}

impl HarnessVerdict {
    /// The stable token written to JSON.
    ///
    /// ADDITIVE by contract: new values may appear here over time, so a
    /// consumer must treat an unrecognized token as "not a success" rather
    /// than matching exhaustively. `status` / `effective_success` keep their
    /// old meaning for consumers that never learn about this field.
    pub(crate) fn label(self) -> &'static str {
        match self {
            Self::Successful => "successful",
            Self::SuccessfulUnvalidated => "successful_unvalidated",
            Self::Vacuous => "vacuous",
            Self::InconclusiveDeadChecks => "inconclusive_dead_checks",
            Self::InconclusiveUndecided => "inconclusive_undecided",
            Self::InconclusiveNoChecks => "inconclusive_no_checks",
            Self::UncertifiedCounterexample => "uncertified_counterexample",
            Self::Unvalidated => "unvalidated",
            Self::Failed => "failed",
        }
    }

    /// One sentence saying what to do about it.
    ///
    /// Deliberately the same wording the SARIF rule descriptions use: one
    /// vocabulary across every channel, so a reader who learned it from a
    /// console run recognizes it in a report. `--summary` prints this verbatim
    /// rather than keeping its own copy of the sentences.
    pub(crate) fn description(self) -> &'static str {
        match self {
            Self::Successful => "every check was proved",
            Self::SuccessfulUnvalidated => {
                "every check was proved, but on an unvalidated solver tier -- \
                 treat the proof as provisional"
            }
            Self::Vacuous => {
                "every check is provably UNREACHABLE -- the proof is vacuous \
                 (contradictory assumptions; nothing was verified)"
            }
            Self::InconclusiveDeadChecks => {
                "the harness is reachable, but every check it emitted is provably \
                 UNREACHABLE -- the checks sit on dead code, so no obligation was \
                 exercised and this is not a proof"
            }
            Self::InconclusiveUndecided => {
                "the solver could not decide this harness within its budget -- \
                 it is not proved and not refuted; try --ay-chc or a longer \
                 --timeout"
            }
            Self::InconclusiveNoChecks => {
                "the harness produced no verification conditions -- there was \
                 nothing to prove, so this is not a proof"
            }
            Self::UncertifiedCounterexample => {
                "a counterexample was found but NOT certified as a genuine bug \
                 -- the encoding approximated something, so the failing values \
                 may be ones your program cannot produce"
            }
            Self::Unvalidated => {
                "verification did not succeed, and the solver tier is \
                 unvalidated (DT+BV)"
            }
            Self::Failed => "verification did not succeed for this harness",
        }
    }

    /// Proved, in either of the two shapes a proof can take.
    pub(crate) fn is_success(self) -> bool {
        matches!(self, Self::Successful | Self::SuccessfulUnvalidated)
    }

    /// Neither proved nor refuted — the class that says "ask again with a
    /// bigger budget", not "your code is wrong".
    pub(crate) fn is_inconclusive(self) -> bool {
        matches!(
            self,
            Self::InconclusiveUndecided | Self::InconclusiveNoChecks | Self::InconclusiveDeadChecks
        )
    }
}

/// The check count the console verdict is computed from.
///
/// Mirrors `format_result`: a cover property with a cover-shaped status is NOT
/// a check, everything else is. Recomputing it here rather than eyeballing
/// `results.len()` is what keeps `inconclusive_no_checks` agreeing with the
/// console's `INCONCLUSIVE (no checks)` on a cover-only harness.
fn console_check_count(properties: &[Property]) -> usize {
    let covers = properties
        .iter()
        .filter(|p| {
            p.is_cover_property()
                && matches!(
                    p.status,
                    CheckStatus::Satisfied
                        | CheckStatus::Unsatisfiable
                        | CheckStatus::Undetermined
                        | CheckStatus::Unreachable
                )
        })
        .count();
    properties.len() - covers
}

/// Classify one harness result the way the console channel does.
pub(crate) fn classify_harness_verdict(
    result: &VerificationResult,
    should_panic: bool,
) -> HarnessVerdict {
    let effective_success =
        is_effective_manual_success(result.status, should_panic, result.failed_properties);
    let unvalidated = result.validation_status == ValidationStatus::Unvalidated;

    if effective_success {
        return if unvalidated {
            HarnessVerdict::SuccessfulUnvalidated
        } else {
            HarnessVerdict::Successful
        };
    }
    // `should_panic` is excluded here for the same reason the V4 gate in
    // `harness_runner` excludes it: its verdict is panic-shaped, not
    // reachability-shaped.
    //
    // Two arms, not one: the all-UNREACHABLE table means "the harness cannot
    // run" or "its checks are dead code", and a CI job that reads only this
    // field gets told to go fix assumptions that were never contradictory.
    if !should_panic {
        match classify_vacuity(&result.results, result.harness_feasibility) {
            VacuityShape::UnsatAssumption => return HarnessVerdict::Vacuous,
            VacuityShape::DeadChecks => return HarnessVerdict::InconclusiveDeadChecks,
            VacuityShape::None => {}
        }
    }
    if console_check_count(&result.results) == 0 {
        // Only the reasons that actually mean "we had something and could not
        // settle it". `SolverError` / `ChcParseError` / `PreSolveDeadline` fell
        // over BEFORE there was anything to decide, and "no checks" is then the
        // honest description — the same split `format_result` documents.
        return if matches!(
            result.solver_unknown_reason,
            Some(SolverUnknownReason::UndecidedModel | SolverUnknownReason::Timeout)
        ) {
            HarnessVerdict::InconclusiveUndecided
        } else {
            HarnessVerdict::InconclusiveNoChecks
        };
    }
    // Exactly the two categories that make the driver print
    // `[AY:CTREX_NOT_CERTIFIED]`. `Genuine` is a real bug and `Unknown` carries
    // no counterexample at all, so neither belongs here.
    if matches!(
        result.ctrex_category,
        Some(CtrexCategory::EncodingGap { .. } | CtrexCategory::OverApproximation { .. })
    ) {
        return HarnessVerdict::UncertifiedCounterexample;
    }
    if unvalidated { HarnessVerdict::Unvalidated } else { HarnessVerdict::Failed }
}

const ARTIFACT_KIND: &str = "trust_mc.proof_summary_pointer";
const EXTRACTOR: &str = "scripts/extract_replacement_proof_report.py";
const AUDITOR: &str = "tools/replacement-audit";
const NOTICE: &str = "Informational summary only. This artifact is not replacement-audit \
validation and must not be used as authoritative replacement proof evidence.";

impl KaniSession {
    pub(crate) fn write_proof_summary_json(&self, results: &[HarnessResult<'_>]) -> Result<()> {
        let Some(path) = &self.args.proof_summary_json else { return Ok(()) };
        write_proof_summary_file(path, results)
    }
}

fn write_proof_summary_file(path: &Path, results: &[HarnessResult<'_>]) -> Result<()> {
    if let Some(parent) = path.parent()
        && !parent.as_os_str().is_empty()
    {
        std::fs::create_dir_all(parent).with_context(|| {
            format!("Failed to create proof summary output directory `{}`", parent.display())
        })?;
    }

    let file = File::create(path).with_context(|| {
        format!("Failed to create proof summary output file `{}`", path.display())
    })?;
    let mut writer = BufWriter::new(file);
    serde_json::to_writer_pretty(&mut writer, &ProofSummaryArtifact::from_results(results))
        .with_context(|| format!("Failed to write proof summary JSON to `{}`", path.display()))?;
    writer.write_all(b"\n")?;
    Ok(())
}

#[derive(Serialize)]
struct ProofSummaryArtifact {
    schema_version: u32,
    artifact_kind: &'static str,
    notice: &'static str,
    authoritative_replacement_proof_flow: AuthoritativeReplacementProofFlow,
    summary: ProofSummaryCounts,
    harnesses: Vec<HarnessSummary>,
}

#[derive(Serialize)]
struct AuthoritativeReplacementProofFlow {
    extractor: &'static str,
    auditor: &'static str,
    note: &'static str,
}

#[derive(Default, Serialize)]
struct ProofSummaryCounts {
    total_harnesses: usize,
    manual_harnesses: usize,
    automatic_harnesses: usize,
    effective_successes: usize,
    failures: usize,
    /// `failures` split by WHAT went wrong, because the three classes need
    /// three different responses from whoever reads the artifact. The four
    /// always sum to `failures`, which is left alone so existing consumers
    /// keep the number they already gate on.
    vacuous_harnesses: usize,
    inconclusive_harnesses: usize,
    uncertified_harnesses: usize,
    refuted_harnesses: usize,
    validated_results: usize,
    unvalidated_results: usize,
    native_full_verification_verdicts: usize,
    proof_transcript_metadata: usize,
}

#[derive(Serialize)]
struct HarnessSummary {
    harness: String,
    crate_name: String,
    automatically_generated: bool,
    should_panic: bool,
    status: &'static str,
    /// Which of the verdicts the console prints this harness got.
    ///
    /// `status` only ever says success/failure, so INCONCLUSIVE (the solver
    /// never decided), VACUOUS (contradictory assumptions — nothing was
    /// verified) and a genuinely refuted assertion all arrived here as
    /// `"failure"`, and no consumer could tell "raise the budget" from "your
    /// code is wrong". Additive: `status`, `failed_properties` and
    /// `effective_success` are untouched.
    verdict: &'static str,
    /// The same sentence the console and the SARIF rule descriptions use, so
    /// a renderer needs no table of its own.
    verdict_description: &'static str,
    failed_properties: &'static str,
    validation_status: &'static str,
    effective_success: bool,
    property_counts: PropertyCounts,
    /// The checks that actually FAILED, with what failed and where.
    ///
    /// The counts above say a harness failed; they never said WHY or WHERE, so
    /// nothing could render a useful verdict table from this artifact — the
    /// information existed only in the prose stream, interleaved across
    /// harnesses and separated from the harness name by pages of per-check
    /// listing. Additive, and empty for a passing harness.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    failed_checks: Vec<FailedCheck>,
    proof_qualifiers: Vec<String>,
    has_proof_transcript_metadata: bool,
    native_full_verification_verdict: Option<&'static str>,
}

/// One failed check: what failed, and the source position to open.
#[derive(Serialize)]
struct FailedCheck {
    description: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    file: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    line: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    column: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    function: Option<String>,
}

/// Collect the failed checks, in the order the engine reported them.
fn failed_checks(result: &VerificationResult) -> Vec<FailedCheck> {
    result
        .results
        .iter()
        .filter(|p| p.status == crate::property_model::CheckStatus::Failure)
        .map(|p| FailedCheck {
            description: p.description.to_string(),
            file: p.source_location.file.clone(),
            line: p.source_location.line.clone(),
            column: p.source_location.column.clone(),
            function: p.source_location.function.clone(),
        })
        .collect()
}

#[derive(Default, Serialize)]
struct PropertyCounts {
    total: usize,
    failed: usize,
    undetermined: usize,
    unknown: usize,
    successful: usize,
    cover_satisfied: usize,
    cover_unsatisfied: usize,
    coverage_covered: usize,
    coverage_uncovered: usize,
}

impl ProofSummaryArtifact {
    fn from_results(results: &[HarnessResult<'_>]) -> Self {
        let mut summary =
            ProofSummaryCounts { total_harnesses: results.len(), ..Default::default() };
        let harnesses = results
            .iter()
            .map(|result| {
                if result.harness.is_automatically_generated {
                    summary.automatic_harnesses += 1;
                } else {
                    summary.manual_harnesses += 1;
                }

                if result.result.validation_status == ValidationStatus::Validated {
                    summary.validated_results += 1;
                } else {
                    summary.unvalidated_results += 1;
                }

                if result.result.proof_transcript_metadata.is_some() {
                    summary.proof_transcript_metadata += 1;
                }
                if result.result.native_full_verification_verdict.is_some() {
                    summary.native_full_verification_verdicts += 1;
                }

                let effective_success = is_effective_manual_success(
                    result.result.status,
                    result.harness.attributes.should_panic,
                    result.result.failed_properties,
                );
                let verdict = classify_harness_verdict(
                    &result.result,
                    result.harness.attributes.should_panic,
                );
                debug_assert_eq!(
                    verdict.is_success(),
                    effective_success,
                    "the verdict chain and `is_effective_manual_success` must agree on success"
                );
                if effective_success {
                    summary.effective_successes += 1;
                } else {
                    summary.failures += 1;
                    match verdict {
                        HarnessVerdict::Vacuous => summary.vacuous_harnesses += 1,
                        HarnessVerdict::UncertifiedCounterexample => {
                            summary.uncertified_harnesses += 1
                        }
                        v if v.is_inconclusive() => summary.inconclusive_harnesses += 1,
                        _ => summary.refuted_harnesses += 1,
                    }
                }

                HarnessSummary {
                    harness: result.harness.pretty_name.clone(),
                    crate_name: result.harness.crate_name.clone(),
                    automatically_generated: result.harness.is_automatically_generated,
                    should_panic: result.harness.attributes.should_panic,
                    status: verification_status_label(result.result.status),
                    verdict: verdict.label(),
                    verdict_description: verdict.description(),
                    failed_properties: failed_properties_label(result.result.failed_properties),
                    validation_status: validation_status_label(result.result.validation_status),
                    effective_success,
                    property_counts: property_counts(&result.result),
                    failed_checks: failed_checks(&result.result),
                    proof_qualifiers: result.result.proof_qualifiers.clone(),
                    has_proof_transcript_metadata: result
                        .result
                        .proof_transcript_metadata
                        .is_some(),
                    native_full_verification_verdict: result
                        .result
                        .native_full_verification_verdict
                        .as_ref()
                        .map(native_full_verification_verdict_label),
                }
            })
            .collect();

        Self {
            schema_version: 1,
            artifact_kind: ARTIFACT_KIND,
            notice: NOTICE,
            authoritative_replacement_proof_flow: AuthoritativeReplacementProofFlow {
                extractor: EXTRACTOR,
                auditor: AUDITOR,
                note: "Run the extractor on the compiletest per-harness report, then audit the \
result with replacement-audit. This JSON does not duplicate those checks.",
            },
            summary,
            harnesses,
        }
    }
}

fn property_counts(result: &VerificationResult) -> PropertyCounts {
    let mut counts = PropertyCounts { total: result.results.len(), ..Default::default() };
    for property in &result.results {
        match property.status {
            CheckStatus::Failure => counts.failed += 1,
            CheckStatus::Undetermined => counts.undetermined += 1,
            CheckStatus::Unknown => counts.unknown += 1,
            // A cover statement on dead code is reported UNREACHABLE (Kani
            // parity, see `classify_unreachable_covers`). That is a NEGATIVE
            // cover outcome, the sibling of `Unsatisfiable` — not a discharged
            // check — so it must not land in `successful`, which would tell a
            // JSON reader the harness proved something it did not.
            CheckStatus::Unreachable if property.is_cover_property() => {
                counts.cover_unsatisfied += 1
            }
            CheckStatus::Success | CheckStatus::Unreachable => counts.successful += 1,
            CheckStatus::Satisfied => counts.cover_satisfied += 1,
            CheckStatus::Unsatisfiable => counts.cover_unsatisfied += 1,
            CheckStatus::Covered => counts.coverage_covered += 1,
            CheckStatus::Uncovered => counts.coverage_uncovered += 1,
        }
    }
    counts
}

fn verification_status_label(status: VerificationStatus) -> &'static str {
    match status {
        VerificationStatus::Success => "success",
        VerificationStatus::Failure => "failure",
    }
}

fn failed_properties_label(failed_properties: FailedProperties) -> &'static str {
    match failed_properties {
        FailedProperties::None => "none",
        FailedProperties::PanicsOnly => "panics_only",
        FailedProperties::Other => "other",
    }
}

fn validation_status_label(validation_status: ValidationStatus) -> &'static str {
    match validation_status {
        ValidationStatus::Validated => "validated",
        ValidationStatus::Unvalidated => "unvalidated",
    }
}

fn native_full_verification_verdict_label(
    verdict: &trust_mc_core::FullVerificationVerdict,
) -> &'static str {
    if matches!(
        trust_mc_core::classify_proof_grade_verdict(verdict),
        trust_mc_core::ProofGradeVerdict::ProofGrade { .. }
    ) {
        return "proof_grade";
    }
    match verdict {
        trust_mc_core::FullVerificationVerdict::Proved { .. } => "candidate_not_proof_grade",
        trust_mc_core::FullVerificationVerdict::Failed { .. } => "failed",
        trust_mc_core::FullVerificationVerdict::Unknown { .. } => "unknown",
        trust_mc_core::FullVerificationVerdict::DiagnosticOnly { .. } => "diagnostic_only",
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_support::{test_harness, test_result};

    #[test]
    fn proof_summary_points_to_authoritative_replacement_audit_flow() {
        let harness = test_harness("crate::proof", "crate");
        let result = test_result(VerificationStatus::Success, FailedProperties::None);
        let harness_result = HarnessResult { harness: &harness, result };

        let artifact = ProofSummaryArtifact::from_results(&[harness_result]);
        let json = serde_json::to_value(&artifact).unwrap();

        assert_eq!(json["artifact_kind"], ARTIFACT_KIND);
        assert_eq!(json["notice"], NOTICE);
        assert_eq!(json["authoritative_replacement_proof_flow"]["extractor"], EXTRACTOR);
        assert_eq!(json["authoritative_replacement_proof_flow"]["auditor"], AUDITOR);
        assert_eq!(json["summary"]["total_harnesses"], 1);
        assert_eq!(json["summary"]["effective_successes"], 1);
        assert_eq!(json["harnesses"][0]["status"], "success");
    }

    #[test]
    fn proof_summary_records_unvalidated_and_transcript_metadata_without_auditing() {
        let harness = test_harness("crate::proof", "crate");
        let mut result = test_result(VerificationStatus::Success, FailedProperties::None);
        result.validation_status = ValidationStatus::Unvalidated;
        result.proof_qualifiers.push("trivial_safe=no_error_rule".to_string());
        result.proof_transcript_metadata = Some(serde_json::json!({"solver": "ay-chc"}));
        let harness_result = HarnessResult { harness: &harness, result };

        let artifact = ProofSummaryArtifact::from_results(&[harness_result]);
        let json = serde_json::to_value(&artifact).unwrap();

        assert_eq!(json["summary"]["unvalidated_results"], 1);
        assert_eq!(json["summary"]["proof_transcript_metadata"], 1);
        assert_eq!(json["harnesses"][0]["validation_status"], "unvalidated");
        assert_eq!(json["harnesses"][0]["proof_qualifiers"][0], "trivial_safe=no_error_rule");
        assert_eq!(json["harnesses"][0]["has_proof_transcript_metadata"], true);
    }

    // ─── verdict classification ───

    use crate::property_model::{Property, PropertyId, RawSourceLocation};
    use std::borrow::Cow;

    fn check(status: CheckStatus) -> Property {
        Property {
            description: Cow::Borrowed("assertion failed: x == 0"),
            property_id: PropertyId {
                fn_name: Some("h".to_string()),
                class: Cow::Borrowed("assertion"),
                id: 1,
            },
            source_location: RawSourceLocation {
                file: Some("src/lib.rs".to_string()),
                line: Some("7".to_string()),
                column: None,
                function: Some("h".to_string()),
            },
            status,
            trace: None,
        }
    }

    fn verdict_of(result: &VerificationResult) -> &'static str {
        classify_harness_verdict(result, false).label()
    }

    /// The three failures that need three different fixes must not share one
    /// shape. Before this, `status: "failure"` was all any of them said.
    #[test]
    fn the_verdict_separates_vacuous_undecided_and_a_real_refutation() {
        // Contradictory assumptions: every check provably unreachable.
        let mut vacuous = test_result(VerificationStatus::Failure, FailedProperties::Other);
        vacuous.results = vec![check(CheckStatus::Unreachable)];
        assert_eq!(verdict_of(&vacuous), "vacuous");

        // Had obligations, could not settle them.
        let mut undecided = test_result(VerificationStatus::Failure, FailedProperties::Other);
        undecided.solver_unknown_reason = Some(SolverUnknownReason::UndecidedModel);
        assert_eq!(verdict_of(&undecided), "inconclusive_undecided");

        // Had no obligations at all — a different diagnosis entirely.
        let empty = test_result(VerificationStatus::Failure, FailedProperties::Other);
        assert_eq!(verdict_of(&empty), "inconclusive_no_checks");

        // ...and an ordinary refuted assertion still reads as one.
        let mut failed = test_result(VerificationStatus::Failure, FailedProperties::PanicsOnly);
        failed.results = vec![check(CheckStatus::Failure)];
        assert_eq!(verdict_of(&failed), "failed");

        // A proof is a proof, in both tiers.
        let ok = test_result(VerificationStatus::Success, FailedProperties::None);
        assert_eq!(verdict_of(&ok), "successful");
        let mut ok_unvalidated = test_result(VerificationStatus::Success, FailedProperties::None);
        ok_unvalidated.validation_status = ValidationStatus::Unvalidated;
        assert_eq!(verdict_of(&ok_unvalidated), "successful_unvalidated");
    }

    /// A `should_panic` pass is a pass, and its panic-shaped verdict must not
    /// be read as vacuity — the V4 gate exempts it for the same reason.
    #[test]
    fn a_should_panic_pass_is_successful_not_vacuous() {
        let mut result = test_result(VerificationStatus::Failure, FailedProperties::PanicsOnly);
        result.results = vec![check(CheckStatus::Failure), check(CheckStatus::Unreachable)];
        assert_eq!(classify_harness_verdict(&result, true).label(), "successful");
        assert!(classify_harness_verdict(&result, true).is_success());
    }

    /// A counterexample the driver declined to certify is not the same news as
    /// "your assertion can fail", and the console says so in a marker line the
    /// JSON channel had no way to carry.
    #[test]
    fn an_uncertified_counterexample_has_its_own_verdict() {
        let mut result = test_result(VerificationStatus::Failure, FailedProperties::Other);
        result.results = vec![check(CheckStatus::Failure)];
        result.ctrex_category =
            Some(CtrexCategory::OverApproximation { categories: vec!["havoc=4".to_string()] });
        assert_eq!(verdict_of(&result), "uncertified_counterexample");

        // A GENUINE counterexample keeps the plain verdict, or the caveat is
        // noise that teaches people to ignore it.
        result.ctrex_category = Some(CtrexCategory::Genuine);
        assert_eq!(verdict_of(&result), "failed");
    }

    /// The added counts are a partition of `failures`, which itself is left
    /// exactly as it was for consumers that already gate on it.
    #[test]
    fn the_failure_breakdown_partitions_the_failure_count() {
        let harness = test_harness("crate::proof", "crate");
        let mut vacuous = test_result(VerificationStatus::Failure, FailedProperties::Other);
        vacuous.results = vec![check(CheckStatus::Unreachable)];
        let mut undecided = test_result(VerificationStatus::Failure, FailedProperties::Other);
        undecided.solver_unknown_reason = Some(SolverUnknownReason::Timeout);
        let mut refuted = test_result(VerificationStatus::Failure, FailedProperties::PanicsOnly);
        refuted.results = vec![check(CheckStatus::Failure)];
        let mut uncertified = test_result(VerificationStatus::Failure, FailedProperties::Other);
        uncertified.results = vec![check(CheckStatus::Failure)];
        uncertified.ctrex_category =
            Some(CtrexCategory::EncodingGap { categories: vec!["gap=1".to_string()] });
        let ok = test_result(VerificationStatus::Success, FailedProperties::None);

        let artifact = ProofSummaryArtifact::from_results(&[
            HarnessResult { harness: &harness, result: vacuous },
            HarnessResult { harness: &harness, result: undecided },
            HarnessResult { harness: &harness, result: refuted },
            HarnessResult { harness: &harness, result: uncertified },
            HarnessResult { harness: &harness, result: ok },
        ]);
        let json = serde_json::to_value(&artifact).unwrap();
        let summary = &json["summary"];

        assert_eq!(summary["failures"], 4, "the pre-existing count must not move");
        assert_eq!(summary["effective_successes"], 1);
        assert_eq!(summary["vacuous_harnesses"], 1);
        assert_eq!(summary["inconclusive_harnesses"], 1);
        assert_eq!(summary["uncertified_harnesses"], 1);
        assert_eq!(summary["refuted_harnesses"], 1);
        let parts = [
            "vacuous_harnesses",
            "inconclusive_harnesses",
            "uncertified_harnesses",
            "refuted_harnesses",
        ]
        .iter()
        .map(|k| summary[*k].as_u64().unwrap())
        .sum::<u64>();
        assert_eq!(parts, summary["failures"].as_u64().unwrap(), "the split must be a partition");

        // Every harness carries the sentence a reader acts on.
        assert_eq!(json["harnesses"][0]["verdict"], "vacuous");
        assert!(
            json["harnesses"][0]["verdict_description"].as_str().unwrap().contains("UNREACHABLE"),
            "{}",
            json["harnesses"][0]["verdict_description"]
        );
        // ...and the fields consumers already read are untouched.
        assert_eq!(json["harnesses"][0]["status"], "failure");
        assert_eq!(json["harnesses"][0]["effective_success"], false);
    }
}
