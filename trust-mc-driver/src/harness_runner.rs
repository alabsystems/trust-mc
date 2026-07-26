// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Harness orchestration: dispatches verification for each proof harness.
//!
//! Unsoundness counting is in [`crate::unsoundness_counts`],
//! demotion/classification in [`crate::demotion`],
//! result output/summary in [`crate::result_summary`].

use anyhow::{Error, Result, anyhow, bail};
use rayon::prelude::*;
use std::path::Path;
use std::path::PathBuf;
use trust_mc_metadata::{HarnessKind, HarnessMetadata};

use crate::args::NumThreads;
use crate::ctrex_classify::classify_ctrex;
use crate::demotion::{
    apply_sound_fallback_fail_close, demote_for_all_unsoundness, lookup_per_harness,
    resolve_per_harness_count_fail_closed,
};
use crate::project::Project;
use crate::session::KaniSession;
use crate::unknown_quality::classify_unknown_quality;
use crate::unsoundness_counts::UnsoundnessCounts;
use crate::verification_result::{
    CtrexCategory, FailedProperties, ProofCrosscheck, VerificationResult, VerificationStatus,
    has_satisfied_cover, has_unsatisfiable_cover, is_unsat_assumption_vacuous,
};

/// A HarnessRunner is responsible for checking all proof harnesses. The data in this structure represents
/// "background information" that the controlling driver (e.g. cargo-kani or kani) computed.
///
/// This struct is basically just a nicer way of passing many arguments to [`Self::check_all_harnesses`]
pub(crate) struct HarnessRunner<'sess, 'pr> {
    /// The underlying kani session
    pub sess: &'sess KaniSession,
    /// The project under verification.
    pub project: &'pr Project,
}

/// The result of checking a single harness. This both hangs on to the harness metadata
/// (as a means to identify which harness), and provides that harness's verification result.
pub(crate) struct HarnessResult<'pr> {
    pub harness: &'pr HarnessMetadata,
    pub result: VerificationResult,
}

#[derive(Debug)]
struct FailFastHarnessInfo {
    pub index_to_failing_harness: usize,
    pub result: VerificationResult,
}

impl std::error::Error for FailFastHarnessInfo {}

impl std::fmt::Display for FailFastHarnessInfo {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "harness failed")
    }
}

impl<'pr> HarnessRunner<'_, 'pr> {
    /// Given a [`HarnessRunner`] (to abstract over how these harnesses were generated), this runs
    /// the proof-checking process for each harness in `harnesses`.
    pub(crate) fn check_all_harnesses(
        &self,
        harnesses: &'pr [&HarnessMetadata],
    ) -> Result<Vec<HarnessResult<'pr>>> {
        let sorted_harnesses = crate::metadata::sort_harnesses_by_loc(harnesses);
        let unsoundness_counts = UnsoundnessCounts::from_project(self.project);
        let pool = {
            let mut builder = rayon::ThreadPoolBuilder::new();
            match self.sess.args.jobs() {
                NumThreads::UserSpecified(num_threads) => {
                    builder = builder.num_threads(num_threads);
                }
                NumThreads::NoMultithreading => {
                    builder = builder.num_threads(1);
                }
                NumThreads::ThreadPoolDefault => { /* rayon will automatically set num_threads to the default if not specified here */
                }
            }
            builder.build()?
        };

        let results = pool.install(|| -> Result<Vec<HarnessResult<'pr>>> {
            sorted_harnesses
                .par_iter()
                .enumerate()
                .map(|(idx, harness)| -> Result<HarnessResult<'pr>> {
                    let binary = self.resolve_harness_input(harness)?;
                    let crate_counts =
                        unsoundness_counts.get_for_crate(harness.crate_name.as_str());

                    let result = self.sess.check_harness(&binary, harness, &crate_counts)?;
                    if self.sess.args.fail_fast && result.status == VerificationStatus::Failure {
                        Err(Error::new(FailFastHarnessInfo {
                            index_to_failing_harness: idx,
                            result,
                        }))
                    } else {
                        Ok(HarnessResult { harness, result })
                    }
                })
                .collect::<Result<Vec<_>>>()
        });
        match results {
            Ok(results) => Ok(results),
            Err(err) => {
                if err.is::<FailFastHarnessInfo>() {
                    let failed = err.downcast::<FailFastHarnessInfo>()?;
                    Ok(vec![HarnessResult {
                        harness: sorted_harnesses[failed.index_to_failing_harness],
                        result: failed.result,
                    }])
                } else {
                    Err(err)
                }
            }
        }
    }

    fn resolve_harness_input(&self, harness: &HarnessMetadata) -> Result<PathBuf> {
        // AY backend uses SMT files produced by codegen, not goto binaries.
        find_smt_file(&harness.model_file, &self.project.outdir).map_err(|e| {
            anyhow!(
                "{} for harness {}. Ensure compilation succeeded with --backend=ay.",
                e,
                harness.pretty_name
            )
        })
    }
}

/// Find an SMT file from a model_file reference, checking both the original path
/// and the path resolved against an output directory.
///
/// Returns the found path, or an error with the list of tried paths.
fn find_smt_file(model_file: &Path, outdir: &Path) -> Result<PathBuf> {
    let mut path = PathBuf::from(model_file);
    path.set_extension("smt2");

    let mut candidates = vec![path];
    if candidates[0].is_relative() {
        candidates.push(outdir.join(&candidates[0]));
    }

    let mut non_file_path = None;
    for candidate in &candidates {
        if candidate.is_file() {
            return Ok(candidate.clone());
        }
        if candidate.exists() {
            non_file_path = Some(candidate.clone());
        }
    }

    if let Some(candidate) = non_file_path {
        bail!("SMT-LIB2 path exists but is not a file: {}", candidate.display());
    }

    let tried = candidates.iter().map(|c| c.display().to_string()).collect::<Vec<_>>().join(", ");
    bail!("SMT-LIB2 file not found (tried: {})", tried)
}

fn demotion_reasons_marker(result: &VerificationResult) -> Option<String> {
    (!result.demotion_reasons.is_empty())
        .then(|| format!("[AY:DEMOTION_REASONS:{}]", result.demotion_reasons.join(",")))
}

fn proof_crosscheck_marker(proof_crosscheck: &ProofCrosscheck) -> Option<String> {
    proof_crosscheck.label().map(|label| format!("[AY:PROOF_CROSSCHECK:{label}]"))
}

pub(crate) fn proof_qualifiers_marker(result: &VerificationResult) -> Option<String> {
    if result.status != VerificationStatus::Success {
        return None;
    }

    let mut quals = result.proof_qualifiers.clone();
    if result.sound_fallback_count > 0 {
        quals.push(format!("sound_fallback={}", result.sound_fallback_count));
    }

    if quals.is_empty() {
        Some("[AY:PROOF_QUALIFIERS:clean]".to_string())
    } else {
        Some(format!("[AY:PROOF_QUALIFIERS:{}]", quals.join(",")))
    }
}

fn hex_encode(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut encoded = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        encoded.push(HEX[(byte >> 4) as usize] as char);
        encoded.push(HEX[(byte & 0x0f) as usize] as char);
    }
    encoded
}

pub(crate) fn proof_transcript_metadata_marker(result: &VerificationResult) -> Option<String> {
    let metadata = result.proof_transcript_metadata.as_ref()?;
    let json = serde_json::to_string(metadata).ok()?;
    Some(format!("[AY:PROOF_TRANSCRIPT_METADATA:v1:json_hex={}]", hex_encode(json.as_bytes())))
}

pub(crate) fn native_proof_grade_marker(result: &VerificationResult) -> Option<String> {
    if let Some(verdict) = &result.native_full_verification_verdict {
        return Some(match trust_mc_core::classify_proof_grade_verdict(verdict) {
            trust_mc_core::ProofGradeVerdict::ProofGrade { .. } => {
                "[AY:NATIVE_PROOF_GRADE:accepted]".to_string()
            }
            trust_mc_core::ProofGradeVerdict::NotProofGrade { reasons, .. } => {
                let reason = reasons
                    .first()
                    .map(|reason| marker_reason(reason))
                    .unwrap_or_else(|| "not_proof_grade".to_string());
                format!("[AY:NATIVE_PROOF_GRADE:rejected:{reason}]")
            }
        });
    }

    let metadata = result.proof_transcript_metadata.as_ref()?;
    match trust_trust_mc_chc_pdr_evidence_payload(metadata) {
        Ok(_) => Some(format!(
            "[AY:NATIVE_PROOF_GRADE:rejected:{}]",
            marker_reason(trust_mc_core::PDR_INVARIANT_FRESH_CONSUMER_REPLAY_REQUIRED)
        )),
        Err(reason) => Some(format!("[AY:NATIVE_PROOF_GRADE:rejected:{reason}]")),
    }
}

pub(crate) fn trust_trust_mc_chc_pdr_evidence_marker(
    result: &VerificationResult,
) -> Option<String> {
    if let Some(verdict) = &result.native_full_verification_verdict {
        let payload = trust_trust_mc_chc_pdr_evidence_payload_from_verdict(verdict)?;
        let json = serde_json::to_string(&payload).ok()?;
        return Some(format!("trust-trust_mc-chc-pdr-evidence: {json}"));
    }

    // Legacy transcript metadata is retained for diagnostics only. It cannot
    // publish an accepted evidence marker without a typed verdict that passes
    // trust-mc-core's admission policy.
    None
}

fn trust_trust_mc_chc_pdr_evidence_payload_from_verdict(
    verdict: &trust_mc_core::FullVerificationVerdict,
) -> Option<serde_json::Value> {
    if !matches!(
        trust_mc_core::classify_proof_grade_verdict(verdict),
        trust_mc_core::ProofGradeVerdict::ProofGrade { .. }
    ) {
        return None;
    }

    let trust_mc_core::FullVerificationVerdict::Proved {
        evidence: trust_mc_core::FullProofEvidence::ChcPdr(proof),
    } = verdict
    else {
        return None;
    };

    let transcript = matching_artifact(
        proof,
        trust_mc_core::FullVerificationArtifactKind::SolverTranscript,
        &proof.metadata.transcript_hashes,
    )?;
    let replay = matching_artifact(
        proof,
        trust_mc_core::FullVerificationArtifactKind::ReplayLog,
        &proof.metadata.replay_log_hashes,
    )?;
    let checked_report = matching_artifact(
        proof,
        trust_mc_core::FullVerificationArtifactKind::CheckedProofReport,
        &proof.metadata.checked_report_hashes,
    )?;
    let transcript_hash = transcript.digest.as_ref()?;
    let replay_hash = replay.digest.as_ref()?;
    let checked_report_hash = checked_report.digest.as_ref()?;
    let reasoning = match proof.kind {
        trust_mc_core::ChcPdrProofKind::PdrInvariant => "Pdr",
        trust_mc_core::ChcPdrProofKind::ChcValidity => "Chc",
    };

    Some(serde_json::json!({
        "schema": "trust.trust_mc-chc-pdr-evidence.v1",
        "reasoning": reasoning,
        "accepted_as_proof": true,
        "normalized_input_sha256": proof.obligation.normalized_input_hash.value.clone(),
        "transcript": transcript.label.clone(),
        "transcript_sha256": transcript_hash.value.clone(),
        "transcript_bytes": transcript.byte_len,
        "replay_log": replay.label.clone(),
        "replay_log_sha256": replay_hash.value.clone(),
        "replay_log_bytes": replay.byte_len,
        "checked_report": checked_report.label.clone(),
        "checked_report_sha256": checked_report_hash.value.clone(),
        "checked_report_bytes": checked_report.byte_len,
    }))
}

fn matching_artifact<'a>(
    proof: &'a trust_mc_core::ChcPdrProofEvidence,
    kind: trust_mc_core::FullVerificationArtifactKind,
    hashes: &[trust_mc_core::EvidenceHash],
) -> Option<&'a trust_mc_core::FullVerificationArtifact> {
    proof.artifacts.iter().find(|artifact| {
        artifact.kind == kind
            && artifact.digest.as_ref().is_some_and(|digest| hashes.contains(digest))
    })
}

fn marker_reason(reason: &str) -> String {
    let mut out = String::with_capacity(reason.len());
    for byte in reason.bytes() {
        if byte.is_ascii_alphanumeric() {
            out.push((byte as char).to_ascii_lowercase());
        } else if !out.ends_with('_') {
            out.push('_');
        }
    }
    let trimmed = out.trim_matches('_');
    if trimmed.is_empty() { "not_proof_grade".to_string() } else { trimmed.to_string() }
}

fn trust_trust_mc_chc_pdr_evidence_payload(
    metadata: &serde_json::Value,
) -> Result<serde_json::Value, &'static str> {
    if string_field(metadata, &["schema"]) != Some("ay.chc-proof-transcript/v1") {
        return Err("unexpected_schema");
    }
    if bool_field(metadata, &["accepted_as_proof"]) != Some(true) {
        return Err("not_accepted_as_proof");
    }
    if string_field(metadata, &["result"]) != Some("safe") {
        return Err("non_safe_result");
    }
    if string_field(metadata, &["replay", "status"]) != Some("replayable") {
        return Err("replay_not_replayable");
    }
    if string_field(metadata, &["transcript", "status"]) != Some("replayable") {
        return Err("transcript_not_replayable");
    }
    if bool_field(metadata, &["transcript", "metadata_only"]) == Some(true) {
        return Err("transcript_metadata_only");
    }

    let transcript = string_field(metadata, &["transcript", "uri"])
        .or_else(|| string_field(metadata, &["transcript", "path"]))
        .or_else(|| string_field(metadata, &["transcript_uri"]))
        .or_else(|| string_field(metadata, &["transcript_path"]))
        .filter(|value| !value.trim().is_empty())
        .ok_or("missing_transcript_path")?;
    let transcript_sha256 = sha256_field(metadata, &["transcript", "sha256"])
        .or_else(|| sha256_field(metadata, &["transcript", "digest"]))
        .or_else(|| sha256_field(metadata, &["transcript", "hash", "value"]))
        .or_else(|| sha256_field(metadata, &["transcript_sha256"]))
        .ok_or("missing_transcript_sha256")?;

    if sha256_field(metadata, &["replay", "sha256"])
        .or_else(|| sha256_field(metadata, &["replay", "digest"]))
        .or_else(|| sha256_field(metadata, &["replay", "hash", "value"]))
        .or_else(|| sha256_field(metadata, &["replay_log_sha256"]))
        .is_none()
    {
        return Err("missing_replay_sha256");
    }
    if sha256_field(metadata, &["checked_report", "sha256"])
        .or_else(|| sha256_field(metadata, &["checked_report", "digest"]))
        .or_else(|| sha256_field(metadata, &["checked_report", "hash", "value"]))
        .or_else(|| sha256_field(metadata, &["checked_proof_report", "sha256"]))
        .or_else(|| sha256_field(metadata, &["checked_proof_report", "digest"]))
        .or_else(|| sha256_field(metadata, &["checked_proof_report", "hash", "value"]))
        .or_else(|| sha256_field(metadata, &["checked_report_sha256"]))
        .is_none()
    {
        return Err("missing_checked_report_sha256");
    }

    Ok(serde_json::json!({
        "schema": "trust.trust_mc-chc-pdr-evidence.v1",
        "reasoning": trust_mc_reasoning_from_metadata(metadata),
        "transcript": transcript,
        "transcript_sha256": transcript_sha256,
    }))
}

fn trust_mc_reasoning_from_metadata(metadata: &serde_json::Value) -> &'static str {
    match string_field(metadata, &["proof_status"]) {
        Some("verified-invariant") => "Pdr",
        _ => "Chc",
    }
}

fn string_field<'a>(value: &'a serde_json::Value, path: &[&str]) -> Option<&'a str> {
    let mut cursor = value;
    for key in path {
        cursor = cursor.get(*key)?;
    }
    cursor.as_str()
}

fn bool_field(value: &serde_json::Value, path: &[&str]) -> Option<bool> {
    let mut cursor = value;
    for key in path {
        cursor = cursor.get(*key)?;
    }
    cursor.as_bool()
}

fn sha256_field<'a>(value: &'a serde_json::Value, path: &[&str]) -> Option<&'a str> {
    string_field(value, path).filter(|digest| {
        digest.len() == 64
            && digest.bytes().all(|byte| byte.is_ascii_hexdigit())
            && digest.bytes().all(|byte| !byte.is_ascii_uppercase())
    })
}

/// Task #78: pure (no-I/O) decision — can this OverApproximation counterexample
/// be SOUNDLY certified Genuine? Split out of `recertify_overapprox_ctrex` for
/// unit testing (see `harness_runner_tests`).
///
/// `categories` are the harness's sound-approximation taint entries
/// (`"name=count"`), `ev` the compiler-plumbed identity evidence, `results` the
/// per-check verdicts. Returns true iff BOTH completeness gates hold AND at
/// least one violated `error_p{N}` is data-independent of every freed var.
fn ctrex_certifiable_genuine(
    categories: &[String],
    ev: &crate::ay_parse::vc_artifact::ApproximationEvidence,
    results: &[crate::property_model::Property],
) -> bool {
    // Parse the harness taint total and its `unhandled_calls` share. Each
    // `unhandled_calls` double-labels a `chc_translation_drop` event from the
    // SAME SoundFallback site, so subtracting it recovers the count of DISTINCT
    // freed-value events the compiler was expected to account.
    let mut taint_total = 0usize;
    let mut unhandled = 0usize;
    for entry in categories {
        let Some((name, count)) = entry.rsplit_once('=') else { continue };
        let Ok(count) = count.parse::<usize>() else { continue };
        taint_total += count;
        if name == "unhandled_calls" {
            unhandled += count;
        }
    }
    let effective_total = taint_total.saturating_sub(unhandled);

    // COMPLETENESS: there was real taint (effective_total > 0), the compiler's
    // local flag holds, AND the accounted count equals the driver's own
    // (double-count adjusted) taint total — i.e. EVERY approximation on the
    // harness recorded its freed-var identity. Any failure means an
    // approximation freed a value the dependence analysis never saw, so the
    // whole harness stays tainted (an unplumbed site is fail-closed).
    if effective_total == 0 || !ev.complete || ev.accounted != effective_total {
        return false;
    }

    // DEPENDENCE: the counterexample is genuine iff at least one VIOLATED
    // `error_p{N}` is data-INDEPENDENT of every freed var. A violated check
    // whose verdict is dependent, or unknown/absent, leaves the taint.
    results.iter().any(|p| {
        p.status == crate::property_model::CheckStatus::Failure
            && matches!(ev.dependent_by_id.get(&p.property_id.id), Some(Some(false)))
    })
}

impl KaniSession {
    /// Task #78: soundly upgrade an `OverApproximation` counterexample to
    /// `Genuine` when the compiler-plumbed approximation-identity evidence
    /// proves the violated check's reachability is independent of every
    /// sound-approximation-freed SMT var.
    ///
    /// Fail-closed on every uncertainty: missing evidence, incomplete identity
    /// plumbing (an unplumbed approximation anywhere on the harness), or a
    /// violated `error_p{N}` that reads (or might read) a freed value keeps the
    /// original `OverApproximation` verdict. This is the driver side of the
    /// Task #77 twin-dual proof: `dual_77_independent` (bug reads raw input)
    /// certifies Genuine; `dual_77_dependent` and `ffi_ptr` (bug reads the
    /// havocked extern return) stay `OverApproximation` because their violated
    /// `error_p3` is `approximation_dependent`.
    fn recertify_overapprox_ctrex(
        &self,
        category: CtrexCategory,
        smt_binary: &Path,
        results: &[crate::property_model::Property],
    ) -> CtrexCategory {
        // Two certifiable lanes (OFFSET_PROV_GENUINE_CERT):
        //   * OverApproximation — the sound-approximation taint lane (Task #77
        //     twin duals); and
        //   * EncodingGap whose SOLE demoting reason is
        //     `offset_provenance_unresolved` — the skipped allocation-bound /
        //     in-bounds check frees no readable var, so an INDEPENDENT violated
        //     check (e.g. the isize-overflow property, reading only count+size)
        //     is a genuine counterexample. Skipping an in-bounds check can only
        //     ADD failures, never fabricate one, so the FAILED verdict is real.
        // Any OTHER EncodingGap reason is a real model gap and is NOT
        // certifiable — it stays EncodingGap (fail-closed). The completeness
        // and per-property dependence gates in `ctrex_certifiable_genuine`
        // still apply to BOTH lanes.
        let categories: Vec<String> = match &category {
            CtrexCategory::OverApproximation { categories } => categories.clone(),
            CtrexCategory::EncodingGap { categories }
                if !categories.is_empty()
                    && categories
                        .iter()
                        .all(|c| c.starts_with("offset_provenance_unresolved=")) =>
            {
                categories.clone()
            }
            _ => return category,
        };
        let vc_path = crate::ay_parse::vc_artifact::vc_artifact_path_for_smt(smt_binary);
        let Some(ev) = crate::ay_parse::vc_artifact::load_approximation_evidence(&vc_path) else {
            return category; // no evidence → stay tainted (fail-closed)
        };
        if ctrex_certifiable_genuine(&categories, &ev, results) {
            println!(
                "[AY:CTREX_CAT:Genuine:certified independent of {} freed var(s) (was {})]",
                ev.approximated_vars.len(),
                category.label()
            );
            CtrexCategory::Genuine
        } else {
            category
        }
    }

    /// Run the verification process for a single harness
    pub(crate) fn check_harness(
        &self,
        binary: &Path,
        harness: &HarnessMetadata,
        unsoundness_counts: &crate::unsoundness_counts::CrateUnsoundnessCounts,
    ) -> Result<VerificationResult> {
        let thread_index = rayon::current_thread_index().unwrap_or_default();
        if !self.args.common_args.quiet {
            // If the harness is automatically generated, pretty_name refers to the function under verification.
            let mut msg = if harness.is_automatically_generated {
                if matches!(harness.attributes.kind, HarnessKind::Proof) {
                    format!(
                        "Autoharness: Checking function {} against all possible inputs...",
                        harness.pretty_name
                    )
                } else {
                    format!(
                        "Autoharness: Checking function {}'s contract against all possible inputs...",
                        harness.pretty_name
                    )
                }
            } else {
                format!("Checking harness {}...", harness.pretty_name)
            };

            if rayon::current_num_threads() > 1 {
                msg = format!("Thread {thread_index}: {msg}");
            }

            println!("{msg}");
        }

        // #3788: Look up DEMOTED fallback count for BMC cross-check trigger.
        // Task #65: fail-closed — a fn-keyed survivor map must trigger the
        // cross-check instead of silently resolving to 0.
        let demoted_fallback_count = resolve_per_harness_count_fail_closed(
            unsoundness_counts.chc_fallback,
            &unsoundness_counts.chc_fallback_per_harness,
            &harness.pretty_name,
            &unsoundness_counts.harness_names,
        );
        // Per-harness wall-clock deadline: every solver attempt below
        // (external subprocess, native CHC, direct linking, retries, cover
        // checks) budgets itself as min(tool_timeout, deadline.remaining()),
        // so one harness can never consume more than its retry-ladder
        // budget of the driver's wall clock.
        let deadline = crate::deadline::Deadline::for_harness(self.args.harness_timeout);
        let mut result = self.with_timer(
            || self.run_ay(binary, harness, demoted_fallback_count, deadline),
            "run_ay",
        )?;
        demote_for_all_unsoundness(&mut result, harness, unsoundness_counts);
        if let Some(marker) = demotion_reasons_marker(&result) {
            println!("{marker}");
        }

        // Classify CTREX verdicts after demotion (#3128). Only non-demoted failures
        // are actual counterexamples — demoted results were originally PROOF.
        if result.status == VerificationStatus::Failure && result.demotion_reasons.is_empty() {
            // UNKNOWN/inconclusive verdicts have no actual counterexample —
            // classify as Unknown, not Genuine (#3374).
            //
            // Detection: FailedProperties::Other AND no non-CHC property has Failure status.
            // On the CHC path, Other means UNKNOWN (or soundness override) — both inconclusive.
            // On the BMC path, Other can also mean a real non-assertion violation (overflow,
            // division-by-zero, bounds-check). Those produce non-"chc" class Failure properties.
            let has_non_chc_violation = result.results.iter().any(|p| {
                p.status == crate::property_model::CheckStatus::Failure
                    && p.property_id.class != "chc"
            });
            if matches!(result.failed_properties, FailedProperties::Other) && !has_non_chc_violation
            {
                result.ctrex_category = Some(CtrexCategory::Unknown);
            } else {
                // Task #78: an OverApproximation counterexample can be SOUNDLY
                // certified Genuine when the compiler plumbed every
                // approximation's freed-var identity AND the violated
                // `error_p{N}`'s reachability is independent of every freed var.
                let category = classify_ctrex(harness, unsoundness_counts);
                result.ctrex_category =
                    Some(self.recertify_overapprox_ctrex(category, binary, &result.results));
            }
        }

        // Vacuity gate (#vacuity): a "proof" that discharged its obligations without
        // actually verifying anything. Runs AFTER CTREX classification — a vacuous
        // harness is originally a non-counterexample SUCCESS, so the block above left
        // its `ctrex_category` as None and never mislabeled it as a counterexample.
        //
        // V4 (unsatisfiable assumption): EVERY non-cover check is provably UNREACHABLE,
        // so the assumption context is contradictory (`kani::assume(false)` / an
        // over-constrained precondition) and the assertions "passed" only vacuously.
        // `should_panic` harnesses are exempt (their verdict is panic-shaped, handled by
        // `is_effective_manual_success`). On by default; `--allow-vacuous` relaxes it,
        // always with a loud marker so the relaxation is never silent.
        if !harness.attributes.should_panic
            && result.status != VerificationStatus::Failure
            && is_unsat_assumption_vacuous(&result.results)
        {
            if self.args.allow_vacuous {
                println!(
                    "[AY:VACUOUS:allowed] {}: every check is provably UNREACHABLE \
                     (unsatisfiable assumptions) — relaxed to a pass by --allow-vacuous",
                    harness.pretty_name
                );
            } else {
                println!(
                    "[AY:VACUOUS:unsat-assumption] {}: every check is provably UNREACHABLE — \
                     the proof is vacuous (contradictory assumptions; nothing was verified). \
                     Pass --allow-vacuous to relax.",
                    harness.pretty_name
                );
                result.status = VerificationStatus::Failure;
                result.failed_properties = FailedProperties::Other;
            }
        }

        // V5 (mandatory witness): a declared `cover(...)` the solver PROVED unsatisfiable
        // or unreachable — the harness claims to exercise a behavior it provably never
        // reaches. WARNING by default (the witness is vacuous but the assertions may
        // still hold); `--strict-vacuity` escalates it to a hard failure.
        if has_unsatisfiable_cover(&result.results) {
            if self.args.strict_vacuity {
                println!(
                    "[AY:VACUOUS:cover] {}: a declared cover(...) is provably \
                     unsatisfiable/unreachable — failing under --strict-vacuity.",
                    harness.pretty_name
                );
                result.status = VerificationStatus::Failure;
                if matches!(result.failed_properties, FailedProperties::None) {
                    result.failed_properties = FailedProperties::Other;
                }
            } else {
                eprintln!(
                    "warning: {}: a declared cover(...) is provably unsatisfiable/unreachable — \
                     the witness is vacuous (pass --strict-vacuity to fail on this).",
                    harness.pretty_name
                );
            }
        }

        // V5 conformance tier (the manifest-driven ERROR): a harness explicitly tagged
        // a conformance harness (`--conformance-harness <name>`) CLAIMS to exercise a
        // binding, so it must demonstrate it by reaching ≥1 SATISFIED cover. No satisfied
        // cover ⇒ the conformance claim proved nothing about behavior → hard failure
        // (VACUOUS), independent of `--strict-vacuity`. Plain harnesses are unaffected
        // (covers stay optional for them). `should_panic` conformance harnesses are
        // exempt for the same reason as V4 (their verdict is panic-shaped).
        if !harness.attributes.should_panic
            && self.args.conformance_harnesses.iter().any(|h| h == &harness.pretty_name)
            && !has_satisfied_cover(&result.results)
        {
            println!(
                "[AY:VACUOUS:conformance] {}: a conformance harness with NO satisfied \
                 cover(...) — it never demonstrably reached the behavior it claims to \
                 exercise, so it proves nothing. Marking VACUOUS (failure).",
                harness.pretty_name
            );
            result.status = VerificationStatus::Failure;
            if matches!(result.failed_properties, FailedProperties::None) {
                result.failed_properties = FailedProperties::Other;
            }
        }

        // Step B (recognize-clean) + Step C (fail-close) — the SoundHavoc split.
        // Extracted to `demotion::apply_sound_fallback_fail_close` (task #65)
        // so the decision is unit-testable and fail-closed against fn-keyed
        // survivor maps (which previously zeroed the lookup and skipped the
        // fail-close silently).
        apply_sound_fallback_fail_close(&mut result, harness, unsoundness_counts);

        // Emit CTREX category marker for shell-script consumption (#3314).
        // Parsed by ay-compiletest.sh to include in per-harness JSON reports.
        if let Some(cat) = &result.ctrex_category {
            let (label, details) = match cat {
                CtrexCategory::EncodingGap { categories } => ("EncodingGap", categories.join(",")),
                CtrexCategory::OverApproximation { categories } => {
                    ("OverApproximation", categories.join(","))
                }
                CtrexCategory::Genuine => ("Genuine", String::new()),
                CtrexCategory::Unknown => ("Unknown", String::new()),
            };
            if details.is_empty() {
                println!("[AY:CTREX_CAT:{label}]");
            } else {
                println!("[AY:CTREX_CAT:{label}:{details}]");
            }
        }

        // Set kani::mem over-approximation count for result/audit bookkeeping.
        // This is a demoting category, so it must not be emitted as a proof qualifier.
        result.kani_mem_overapprox_count = lookup_per_harness(
            &unsoundness_counts.kani_mem_overapprox_per_harness,
            &harness.pretty_name,
        )
        .copied()
        .unwrap_or(0);

        // `result.sound_fallback_count` was computed above (Step B), excluding
        // recognized-clean SoundHavoc drops.

        // Emit sound fallback marker for shell-script consumption (Part of #3476).
        // Parsed by ay-compiletest.sh to include in per-harness JSON reports.
        if result.sound_fallback_count > 0 {
            println!("[AY:SOUND_FALLBACK:{}]", result.sound_fallback_count);
        }

        // Classify UNKNOWN quality and emit marker (Part of #2985).
        // Distinguishes clean solver UNKNOWN from UNKNOWN with known encoding/approximation issues.
        if result.ctrex_category == Some(CtrexCategory::Unknown) {
            let quality = classify_unknown_quality(harness, unsoundness_counts);
            let label = quality.label();
            if let Some(details) = quality.details() {
                println!("[AY:UNKNOWN_QUALITY:{label}:{details}]");
            } else {
                println!("[AY:UNKNOWN_QUALITY:{label}]");
            }
            result.unknown_quality = Some(quality);
        }

        if let Some(reason) = result.solver_unknown_reason {
            println!("[AY:UNKNOWN_REASON:{}]", reason.label());
        }

        if let Some(marker) = proof_crosscheck_marker(&result.proof_crosscheck) {
            println!("{marker}");
        }

        if let Some(marker) = proof_transcript_metadata_marker(&result) {
            println!("{marker}");
        }
        if let Some(marker) = trust_trust_mc_chc_pdr_evidence_marker(&result) {
            println!("{marker}");
        }
        if let Some(marker) = native_proof_grade_marker(&result) {
            println!("{marker}");
        }

        self.process_output(&result, harness, thread_index)?;
        self.gen_and_add_concrete_playback(harness, &mut result)?;
        Ok(result)
    }
}

#[cfg(test)]
#[path = "harness_runner_tests.rs"]
mod tests;
