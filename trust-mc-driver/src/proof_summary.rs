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
use crate::property_model::CheckStatus;
use crate::session::KaniSession;
use crate::verification_result::{
    FailedProperties, ValidationStatus, VerificationResult, VerificationStatus,
};

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
    failed_properties: &'static str,
    validation_status: &'static str,
    effective_success: bool,
    property_counts: PropertyCounts,
    proof_qualifiers: Vec<String>,
    has_proof_transcript_metadata: bool,
    native_full_verification_verdict: Option<&'static str>,
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
                if effective_success {
                    summary.effective_successes += 1;
                } else {
                    summary.failures += 1;
                }

                HarnessSummary {
                    harness: result.harness.pretty_name.clone(),
                    crate_name: result.harness.crate_name.clone(),
                    automatically_generated: result.harness.is_automatically_generated,
                    should_panic: result.harness.attributes.should_panic,
                    status: verification_status_label(result.result.status),
                    failed_properties: failed_properties_label(result.result.failed_properties),
                    validation_status: validation_status_label(result.result.validation_status),
                    effective_success,
                    property_counts: property_counts(&result.result),
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
}
