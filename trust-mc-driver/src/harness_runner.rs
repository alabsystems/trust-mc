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
use std::sync::Mutex;
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
    CtrexCategory, FailedProperties, ProofCrosscheck, VacuityShape, VerificationResult,
    VerificationStatus, classify_vacuity, has_satisfied_cover, has_unsatisfiable_cover,
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

/// Print a machine-readable marker line on stdout unless `--quiet` was asked
/// for.
///
/// `--quiet` promises "nothing but the exit code and requested artifacts", but
/// every `[AY:*]` marker below went out through a bare `println!`, so a quiet
/// run still printed `[AY:CTREX_CAT:Genuine]`, `[AY:VACUOUS:...]`,
/// `[AY:DEMOTION_REASONS:...]` and the rest. `process_output` already gated
/// `[AY:PROOF_QUALIFIERS:...]` on the same flag; this brings the runner's
/// markers in line with it.
///
/// Only the PRINTING is conditional. Every call site keeps its surrounding
/// logic — the demotion, the vacuity fail-close, the CTREX classification —
/// so `--quiet` changes what you see and never what the tool concluded or what
/// it exits with. With `--quiet` absent the text is byte-identical to before,
/// which matters because `scripts/ay-compiletest.sh` parses these exact lines.
///
/// Deliberately stdout-only: the `warning:`/`eprintln!` diagnostics stay on
/// stderr as they are, the same way the compiler's `UNSOUND:` warnings do.
/// Silencing a soundness warning is a worse failure than a chatty `--quiet`.
macro_rules! marker_println {
    ($session:expr, $($arg:tt)*) => {
        if !$session.args.common_args.quiet {
            println!($($arg)*);
        }
    };
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
        // Mirror `--quiet` where the CHC portfolio's `solver_stdout!` can see
        // it: those sites print from free functions with no session in reach.
        // Set once, here, because every solver print happens underneath this
        // call. See `args::common::QUIET_OUTPUT`.
        crate::args::common::set_quiet_output(self.sess.args.common_args.quiet);
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

        // Harnesses that finished before any `--fail-fast` abort, keyed by their
        // position in `sorted_harnesses`.
        //
        // The obvious shape here is `.map(..).collect::<Result<Vec<_>>>()`, but
        // that silently loses work: a short-circuiting collect keeps the first
        // `Err` and DISCARDS every `Ok` already produced. With `--fail-fast` the
        // summary then contradicted the transcript it was printing under --
        // three harnesses, one bad, reported the success and then denied it:
        //
        //     Checking harness c_ok...   VERIFICATION:- SUCCESSFUL
        //     Checking harness b_bad...  VERIFICATION:- FAILED
        //     Complete - 0 successfully verified harnesses, 1 failures, 1 total.
        //
        // `c_ok` was verified, was reported as verified, and was then counted as
        // neither verified nor attempted. Collecting into a keyed side channel
        // keeps those results; sorting by the key on the way out reproduces the
        // ordering `collect` used to give.
        //
        // Only SUCCESSES are preserved, never the concurrent failures. Under
        // `--jobs N` several harnesses can fail in the same instant, and which
        // ones did is a race; reporting all of them would make the failure count
        // nondeterministic. `--fail-fast` promises to stop at *a* failure, so
        // exactly the one that triggered the abort is reported.
        let completed: Mutex<Vec<(usize, HarnessResult<'pr>)>> = Mutex::new(Vec::new());

        let outcome = pool.install(|| -> Result<()> {
            sorted_harnesses.par_iter().enumerate().try_for_each(|(idx, harness)| -> Result<()> {
                let binary = self.resolve_harness_input(harness)?;
                let crate_counts = unsoundness_counts.get_for_crate(harness.crate_name.as_str());

                let result = self.sess.check_harness(&binary, harness, &crate_counts)?;
                if self.sess.args.fail_fast && result.status == VerificationStatus::Failure {
                    Err(Error::new(FailFastHarnessInfo { index_to_failing_harness: idx, result }))
                } else {
                    completed
                        .lock()
                        .expect("harness result collector poisoned")
                        .push((idx, HarnessResult { harness, result }));
                    Ok(())
                }
            })
        });

        let mut results = completed.into_inner().expect("harness result collector poisoned");
        match outcome {
            Ok(()) => {}
            Err(err) if err.is::<FailFastHarnessInfo>() => {
                let failed = err.downcast::<FailFastHarnessInfo>()?;
                results.push((
                    failed.index_to_failing_harness,
                    HarnessResult {
                        harness: sorted_harnesses[failed.index_to_failing_harness],
                        result: failed.result,
                    },
                ));
            }
            Err(err) => return Err(err),
        }
        results.sort_by_key(|(idx, _)| *idx);
        Ok(results.into_iter().map(|(_, result)| result).collect())
    }

    fn resolve_harness_input(&self, harness: &HarnessMetadata) -> Result<PathBuf> {
        // AY backend uses SMT files produced by codegen, not goto binaries.
        let smt_file = find_smt_file(&harness.model_file, &self.project.outdir).map_err(|e| {
            anyhow!(
                "{} for harness {}. Ensure compilation succeeded with --backend=ay.",
                e,
                harness.pretty_name
            )
        })?;

        // Register the per-harness codegen output for cleanup, but ONLY for a
        // single-file run. `Project::try_new` records no artifacts for the AY
        // backend, so without this a plain `trust-mc file.rs` leaves
        // `<crate>__<mangled>.symtab.smt2` and its `.vc.json` sidecar next to the
        // user's source — two files per harness, every run, in whatever directory
        // they happened to be in. `--keep-temps` still keeps them (the session's
        // `Drop` honors it), which the debugging workflows in `explain flags` need.
        //
        // A cargo run must NOT delete them: its outputs live under
        // `target/kani/…`, a build directory rather than the user's source tree,
        // and cargo CACHES the build. Deleting the query there makes the NEXT
        // `cargo trust-mc` fail with "SMT-LIB2 file not found", because the cached
        // build is a no-op and never regenerates it. A standalone run recompiles
        // unconditionally, so removal is safe there.
        if self.project.input.is_some() {
            self.sess.record_temporary_file(&smt_file);
            self.sess.record_temporary_file(
                &crate::ay_parse::vc_artifact::vc_artifact_path_for_smt(&smt_file),
            );
        }

        Ok(smt_file)
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

/// The BMC unwind bound was exhausted: some loop asked for an iteration past
/// `--unwind N` / `#[kani::unwind(N)]`, so the unwinding assertion the unroller
/// planted on the cut back-edge is among the FAILED checks (class `"unwind"`,
/// see `classify_violation`).
///
/// This is the one counterexample shape that says nothing whatsoever about the
/// program: the search was truncated, not a bug found. Every consumer that would
/// otherwise present it as a bug — the CTREX category, the not-certified caveat,
/// concrete playback — keys off this predicate.
fn unwind_bound_exhausted(results: &[crate::property_model::Property]) -> bool {
    results.iter().any(|p| {
        p.status == crate::property_model::CheckStatus::Failure && p.property_id.class == "unwind"
    })
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
            marker_println!(
                self,
                "[AY:CTREX_CAT:Genuine:certified independent of {} freed var(s) (was {})]",
                ev.approximated_vars.len(),
                category.label()
            );
            CtrexCategory::Genuine
        } else {
            category
        }
    }

    /// Answer a loop contract's TWO questions with the strongest sound method
    /// for each, when this harness's single lane could not answer both.
    ///
    /// Obligations lane: rule ON + `--prove-safety-only` -> base / step /
    /// decreases. Properties lane: rule OFF + bounded unroll -> assertions and
    /// memory safety. Both are CHILD PROCESSES: the unsoundness counters are
    /// process-global and accumulate, so an in-process second lane would trip
    /// markers this lane never trips and demote a clean proof to a failure.
    ///
    /// Only ever upgrades a verdict, and only when BOTH lanes discharge what
    /// they own; on any doubt the original verdict stands untouched.
    fn maybe_two_lane_retry(
        &self,
        binary: &Path,
        harness: &HarnessMetadata,
        result: &mut VerificationResult,
    ) {
        use crate::loop_two_lane as lanes;

        // `binary` is already the resolved `.smt2` for this harness (see the
        // call site) — the artifact sits beside it.
        let vc_path = crate::ay_parse::vc_artifact::vc_artifact_path_for_smt(binary);
        if !lanes::harness_is_eligible(&vc_path) {
            return;
        }

        // One clock for the WHOLE retry: the parent's watchdog kills it at
        // ~80s (harness_timeout*5+5), and a kill degrades this row to a
        // timeout — which would make the feature a regression.
        let retry_start = std::time::Instant::now();
        // `--harness` is a filter over PRETTY names; passing the mangled name
        // yields "no harnesses matched the harness filter" and a silent no-op.
        let harness_name = harness.pretty_name.as_str();

        // RUN THE LANES CONCURRENTLY. They are INDEPENDENT — the obligations
        // lane proves base/step/decreases, the properties lane proves the user
        // assertions — so sequencing them cost `sum` where `max` suffices.
        // MEASURED: obligations ~44s, properties ~20s. Sequential 64s left only
        // ~6s of headroom under the parent's 80s watchdog, and under the
        // corpus's `--jobs 3` contention that overran the retry budget: the row
        // reported false_positive at exactly the 70s cap while the SAME harness
        // proved in 64.4s on an idle machine. A feature that only works on an
        // unloaded machine is not working.
        let budget = match lanes::lane_budget(retry_start.elapsed()) {
            Some(b) => b,
            None => return,
        };
        let (o_res, p_res) = std::thread::scope(|scope| {
            let o = scope.spawn(|| {
                lanes::lane_o_command(harness_name)
                    .and_then(|c| crate::session::run_piped_with_timeout(c, budget).ok())
            });
            let p = scope.spawn(|| {
                lanes::lane_p_command(harness_name, lanes::LANE_P_DEPTHS[0])
                    .and_then(|c| crate::session::run_piped_with_timeout(c, budget).ok())
            });
            (o.join().ok().flatten(), p.join().ok().flatten())
        });

        let Some(out_o) = o_res else {
            println!("[AY:LOOP_TWO_LANE] obligations lane did not run");
            return;
        };
        let o_stdout = String::from_utf8_lossy(&out_o.stdout).into_owned();
        if !lanes::child_proved(&o_stdout) {
            let tail: Vec<&str> = o_stdout
                .lines()
                .filter(|l| l.starts_with("VERIFICATION") || l.starts_with("error"))
                .collect();
            println!("[AY:LOOP_TWO_LANE] obligations lane did not prove: {tail:?}");
            return;
        }
        println!("[AY:LOOP_TWO_LANE] obligations lane discharged");

        let mut p_proved = p_res
            .as_ref()
            .is_some_and(|o| lanes::child_proved(&String::from_utf8_lossy(&o.stdout)));

        // Deepen only if the first depth did not answer AND time remains.
        if !p_proved {
            for depth in &lanes::LANE_P_DEPTHS[1..] {
                let Some(b) = lanes::lane_budget(retry_start.elapsed()) else {
                    println!("[AY:LOOP_TWO_LANE] out of retry budget before depth {depth}");
                    break;
                };
                let Some(cmd) = lanes::lane_p_command(harness_name, *depth) else { break };
                let Ok(out) = crate::session::run_piped_with_timeout(cmd, b) else { continue };
                if lanes::child_proved(&String::from_utf8_lossy(&out.stdout)) {
                    p_proved = true;
                    break;
                }
            }
        }

        match lanes::merge(true, &o_stdout, p_proved) {
            lanes::TwoLaneOutcome::Proved => {
                println!(
                    "[AY:LOOP_TWO_LANE] obligations and properties discharged in separate lanes"
                );
                // Every check this lane could not discharge WAS discharged —
                // the obligations in Lane O, the user properties in Lane P.
                // Leaving them marked FAILURE would print "Failed Checks: ..."
                // directly above a SUCCESSFUL verdict: contradictory output that
                // misleads a reader and any tool parsing the check list. Record
                // WHERE each one was discharged rather than silently flipping it.
                for prop in &mut result.results {
                    if prop.status == crate::property_model::CheckStatus::Failure {
                        prop.status = crate::property_model::CheckStatus::Success;
                        prop.description = std::borrow::Cow::Owned(format!(
                            "{} [discharged in the two-lane loop-contract retry]",
                            prop.description
                        ));
                    }
                }
                result.status = VerificationStatus::Success;
                result.failed_properties = FailedProperties::None;
            }
            lanes::TwoLaneOutcome::Inconclusive(why) => {
                println!("[AY:LOOP_TWO_LANE] not proved: {why}");
            }
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
            marker_println!(self, "{marker}");
            // Say what the marker means, for the same reason
            // `[AY:CTREX_NOT_CERTIFIED]` exists — and this case needs it MORE.
            //
            // A demoted result was originally a PROOF (see the classification
            // guard directly below: CTREX runs only when `demotion_reasons` is
            // empty). Nothing was disproved; the proof was downgraded because it
            // leaned on an approximation. But it renders as
            //
            //     VERIFICATION:- FAILED
            //
            // identical to a real counterexample, with the explanation sitting
            // in a marker line that means nothing unless you know the
            // vocabulary. `HashMap::len()` after two inserts lands here, so it
            // is not an exotic path — and a reader would go hunting for a bug
            // that was never found.
            //
            // The CTREX caveat cannot cover this: these two are mutually
            // exclusive by that same guard.
            marker_println!(
                self,
                "[AY:DEMOTED_NOT_A_COUNTEREXAMPLE] {}: no counterexample was found — this \
                 harness was PROVED and then downgraded because the encoding approximated {}. \
                 There is nothing here to debug in your code; the proof simply could not be \
                 certified.",
                harness.pretty_name,
                result.demotion_reasons.join(", ")
            );
        }

        // Was the verdict produced by running out of unwind budget rather than by
        // finding anything? Computed once and consulted twice: here (category)
        // and at the marker block below (the caveat line).
        let unwind_exhausted = unwind_bound_exhausted(&result.results);

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
            if unwind_exhausted {
                // The unwind budget ran out, so the search was TRUNCATED. Nothing
                // was disproved: the paths that would have decided the harness
                // were never explored. That is exactly `Unknown` ("no actual
                // counterexample exists" — the sibling case of a solver UNKNOWN),
                // and emphatically not `Genuine`.
                //
                // Deliberately whole-harness, not per-check, and this is the
                // conservative direction: a check that failed on a path the
                // unroller did NOT cut is still a real failure, but the query is
                // one `(or viol_0 … viol_n)` and the model that satisfied it may
                // have used the cut edge, so we cannot tell which checks the
                // truncation implicates. Upstream Kani takes the same position —
                // `tests/expected/unwind-recursion-fail` pins every sibling check
                // as UNDETERMINED once an unwinding assertion fails. Costs at
                // worst a "raise the bound, then look again"; the alternative
                // costs someone a day hunting a bug that was never found.
                result.ctrex_category = Some(CtrexCategory::Unknown);
            } else if matches!(result.failed_properties, FailedProperties::Other)
                && !has_non_chc_violation
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
        // V4 (every check unreachable): EVERY non-cover check is provably UNREACHABLE,
        // so no obligation this harness emitted was discharged over a run that can
        // happen. `should_panic` harnesses are exempt (their verdict is panic-shaped,
        // handled by `is_effective_manual_success`). On by default; `--allow-vacuous`
        // relaxes it, always with a loud marker so the relaxation is never silent.
        //
        // That table has TWO causes and they are opposite diagnoses, so the gate
        // splits on `classify_vacuity` (BMC's harness-reachability probe / the CHC
        // lane's exit-block test) rather than reporting one cause for both:
        //
        //   UnsatAssumption — the harness cannot run: `kani::assume(false)`, mutually
        //     exclusive assumptions, an infeasible body. The case V4 was written for.
        //   DeadChecks — the harness DEMONSTRABLY runs (the solver decided its
        //     constraints satisfiable) and its checks sit on dead code, e.g.
        //     `if x > 200 && x < 100 { panic!() }`. Naming "contradictory
        //     assumptions" here was wrong on both clauses: there are none, and the
        //     panic-freedom of that branch WAS settled.
        //
        // Both still fail closed, and deliberately so. What the dead-check harness
        // established is that its assertions cannot be *reached* — never that the
        // code under them is right — and "every obligation is unreachable" is also
        // the shape a mis-encoded guard produces, which is how a false proof hides.
        // Downgrading only the CLAIM, not the verdict, fixes the misattribution
        // without moving anything from fail-closed to fail-open; promoting the
        // dead-check arm to a pass is a separate decision that needs its own corpus
        // run (see docs/findings/2026-08-23-v4-fires-on-a-dead-check.md).
        let vacuity_shape = classify_vacuity(&result.results, result.harness_feasibility);
        if !harness.attributes.should_panic
            && result.status != VerificationStatus::Failure
            && vacuity_shape != VacuityShape::None
        {
            match (self.args.allow_vacuous, vacuity_shape) {
                (true, VacuityShape::UnsatAssumption) => {
                    marker_println!(
                        self,
                        "[AY:VACUOUS:allowed] {}: every check is provably UNREACHABLE \
                         (unsatisfiable assumptions) — relaxed to a pass by --allow-vacuous",
                        harness.pretty_name
                    );
                }
                (true, VacuityShape::DeadChecks) => {
                    marker_println!(
                        self,
                        "[AY:VACUOUS:allowed] {}: every check is provably UNREACHABLE \
                         (dead code; the harness itself is reachable) — relaxed to a pass \
                         by --allow-vacuous",
                        harness.pretty_name
                    );
                }
                (false, VacuityShape::UnsatAssumption) => {
                    marker_println!(
                        self,
                        "[AY:VACUOUS:unsat-assumption] {}: every check is provably UNREACHABLE — \
                         the proof is vacuous (contradictory assumptions; nothing was verified). \
                         Pass --allow-vacuous to relax.",
                        harness.pretty_name
                    );
                    result.status = VerificationStatus::Failure;
                    result.failed_properties = FailedProperties::Other;
                }
                (false, VacuityShape::DeadChecks) => {
                    marker_println!(
                        self,
                        "[AY:VACUOUS:dead-checks] {}: the harness IS reachable — its \
                         assumptions are satisfiable — but every check it emitted is provably \
                         UNREACHABLE, so no obligation was exercised. This is not a proof of \
                         the code under those checks; look for a guard that can never hold. \
                         Pass --allow-vacuous to relax.",
                        harness.pretty_name
                    );
                    result.status = VerificationStatus::Failure;
                    result.failed_properties = FailedProperties::Other;
                }
                (_, VacuityShape::None) => unreachable!("guarded by vacuity_shape != None"),
            }
        }

        // V4b (nothing to verify): the harness produced NO checks at all, yet the
        // status is Success — so the run is reported as a clean proof of nothing.
        //
        // `is_unsat_assumption_vacuous` above cannot see this case: it requires at
        // least one check to compare against (`checks > 0`). Zero checks arise when
        // codegen emitted no obligation for the body — an empty harness, or a body
        // whose only failure path was folded away before it became a violation (the
        // observed instance: `Option::<u32>::None.unwrap()`, which panics
        // unconditionally at runtime yet yields an obligation-free query).
        //
        // A proof of zero obligations is not a proof. Fail closed so it renders as
        // `VERIFICATION:- INCONCLUSIVE (no checks)` — the verdict
        // `verification_result` already defines for this shape but could never
        // reach while the status stayed Success — and exits non-zero. Cover-only
        // harnesses are exempt: their covers ARE the obligation, and V5 below
        // adjudicates them.
        // A body with NO obligation site (no Call, no Assert terminator) cannot
        // have had an obligation dropped — zero checks there is the
        // `fn check() {}` shape Kani reports as a clean `0 of 0 failed`.
        // Certified by the compiler, which is the only side that sees the MIR;
        // absent or unreadable evidence keeps the fail-closed path.
        let body_has_no_obligation_site = crate::ay_parse::vc_artifact::
            artifact_body_is_obligation_free(
                &crate::ay_parse::vc_artifact::vc_artifact_path_for_smt(binary),
            );
        if !harness.attributes.should_panic
            && result.status != VerificationStatus::Failure
            && result.results.is_empty()
            && !body_has_no_obligation_site
        {
            marker_println!(
                self,
                "[AY:VACUOUS:no-checks] {}: the harness produced no verification \
                 conditions — there was nothing to prove, so this is not a proof.",
                harness.pretty_name
            );
            result.status = VerificationStatus::Failure;
            result.failed_properties = FailedProperties::Other;
        }

        // V5 (mandatory witness): a declared `cover(...)` the solver PROVED unsatisfiable
        // or unreachable — the harness claims to exercise a behavior it provably never
        // reaches. WARNING by default (the witness is vacuous but the assertions may
        // still hold); `--strict-vacuity` escalates it to a hard failure.
        if has_unsatisfiable_cover(&result.results) {
            if self.args.strict_vacuity {
                marker_println!(
                    self,
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
            marker_println!(
                self,
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
                marker_println!(self, "[AY:CTREX_CAT:{label}]");
            } else {
                marker_println!(self, "[AY:CTREX_CAT:{label}:{details}]");
            }

            // The bound, not the program. Same reason the caveats below exist —
            // `VERIFICATION:- FAILED` reads as "your code is broken" whatever the
            // category marker says — but this shape needs it most: there is not
            // even a candidate bug behind it, only a search that stopped early,
            // and the fix is a flag rather than a code change. Named here in the
            // CTREX vocabulary so the same reader/tooling that trusts
            // `[AY:CTREX_NOT_CERTIFIED]` sees it; `verification_result` also
            // appends the raise-the-bound tip off the check description.
            if unwind_exhausted {
                println!(
                    "[AY:CTREX_NOT_CERTIFIED] {}: NOT a counterexample — a loop hit the unwind \
                     bound, so the search was truncated before it could decide this harness. \
                     Nothing in your program was disproved. Raise the bound (--unwind N, \
                     --default-unwind N, or #[kani::unwind(N)]) and re-run; if the loop has no \
                     constant bound, use --ay-chc for unbounded proofs.",
                    harness.pretty_name
                );
            }

            // Say in words what the marker says in shorthand.
            //
            // A counterexample the classifier could NOT certify as genuine still
            // renders as `VERIFICATION:- FAILED`, identical to a real bug. The
            // only signal was the word "EncodingGap" inside a line reading
            // "CTREX breakdown: 1 EncodingGap, 0 OverApproximation, ..." -- which
            // tells you nothing unless you already know the vocabulary, and
            // costs an hour hunting a bug that is not there.
            //
            // `kani::bounded_any::<String, 4>()` is the everyday case: the
            // failure comes from `utf8_chunks` being abstracted, not from the
            // harness. Name the categories so the reader can tell which of their
            // code, if any, is implicated -- and say plainly that this one is
            // not certified as theirs.
            match cat {
                CtrexCategory::EncodingGap { categories } => {
                    marker_println!(
                        self,
                        "[AY:CTREX_NOT_CERTIFIED] {}: this counterexample was NOT certified as \
                         a genuine bug — the encoding fell back for {}, so the failing values \
                         may be ones your program cannot produce. It may still be a real bug: \
                         the check says only that the fallback makes it uncertain. The \
                         `warning:` lines name the constructs involved.",
                        harness.pretty_name,
                        if categories.is_empty() {
                            "an unmodelled construct".to_string()
                        } else {
                            categories.join(", ")
                        }
                    );
                }
                CtrexCategory::OverApproximation { categories } => {
                    marker_println!(
                        self,
                        "[AY:CTREX_NOT_CERTIFIED] {}: this counterexample was NOT certified as \
                         a genuine bug — over-approximation in {} may have admitted values the \
                         real program never produces. It may still be a real bug; the check \
                         says only that the approximation makes it uncertain.",
                        harness.pretty_name,
                        if categories.is_empty() {
                            "the encoding".to_string()
                        } else {
                            categories.join(", ")
                        }
                    );
                }
                CtrexCategory::Genuine | CtrexCategory::Unknown => {}
            }
        }

        // V6 (should_panic + an UNCERTIFIED counterexample): fail closed.
        //
        // For an ordinary harness a counterexample is the bad news either way,
        // so an uncertified one needs no more than the caveat printed above.
        // For `#[kani::should_panic]` the counterexample IS the proof
        // obligation: `is_effective_manual_success` turns `PanicsOnly` into
        //
        //     VERIFICATION:- SUCCESSFUL (encountered one or more panics as expected)
        //
        // and exit 0, and the harness counts as verified. So a panic the driver
        // had just declined to certify -- one it described in the very previous
        // line as values "your program cannot produce" -- was accepted AS the
        // proof. Observed with `kani::bounded_any::<String, 4>()` under
        // --ay-chc, where the panic comes entirely from the over-approximated
        // call and the real program cannot panic at all:
        //
        //     [AY:CTREX_CAT:OverApproximation:chc_sound_havoc_drop=4]
        //     [AY:CTREX_NOT_CERTIFIED] sp_chc_gap: ... NOT certified ...
        //     VERIFICATION:- SUCCESSFUL (encountered one or more panics as expected)
        //
        // Demoting `failed_properties` (rather than `status`, which is already
        // `Failure` here) is what every channel reads: the console verdict, the
        // exit code, SARIF and the proof summary all route through
        // `is_effective_manual_success`, so one flip fails them all closed
        // together.
        //
        // NARROW on purpose -- only the two categories that printed
        // `[AY:CTREX_NOT_CERTIFIED]` just above. `Genuine` is a real panic and
        // still passes (that is the feature working), and `Unknown` cannot
        // reach here: it is only ever set on the `FailedProperties::Other`
        // branch, which is not an effective success in the first place.
        if harness.attributes.should_panic
            && matches!(result.failed_properties, FailedProperties::PanicsOnly)
            && matches!(
                result.ctrex_category,
                Some(CtrexCategory::EncodingGap { .. } | CtrexCategory::OverApproximation { .. })
            )
        {
            println!(
                "[AY:SHOULD_PANIC_NOT_CERTIFIED] {}: the expected panic is a counterexample \
                 the classifier could NOT certify as genuine, so it cannot stand as the proof \
                 this should_panic harness asks for. Failing closed -- nothing was verified. \
                 (The verdict line below reads `other than panics` because the certified-panic \
                 count is now zero.)",
                harness.pretty_name
            );
            result.status = VerificationStatus::Failure;
            result.failed_properties = FailedProperties::Other;
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
            marker_println!(self, "[AY:SOUND_FALLBACK:{}]", result.sound_fallback_count);
        }

        // Classify UNKNOWN quality and emit marker (Part of #2985).
        // Distinguishes clean solver UNKNOWN from UNKNOWN with known encoding/approximation issues.
        if result.ctrex_category == Some(CtrexCategory::Unknown) {
            let quality = classify_unknown_quality(harness, unsoundness_counts);
            let label = quality.label();
            if let Some(details) = quality.details() {
                marker_println!(self, "[AY:UNKNOWN_QUALITY:{label}:{details}]");
            } else {
                marker_println!(self, "[AY:UNKNOWN_QUALITY:{label}]");
            }
            result.unknown_quality = Some(quality);
        }

        if let Some(reason) = result.solver_unknown_reason {
            marker_println!(self, "[AY:UNKNOWN_REASON:{}]", reason.label());
        }

        if let Some(marker) = proof_crosscheck_marker(&result.proof_crosscheck) {
            marker_println!(self, "{marker}");
        }

        if let Some(marker) = proof_transcript_metadata_marker(&result) {
            marker_println!(self, "{marker}");
        }
        if let Some(marker) = trust_trust_mc_chc_pdr_evidence_marker(&result) {
            marker_println!(self, "{marker}");
        }
        if let Some(marker) = native_proof_grade_marker(&result) {
            marker_println!(self, "{marker}");
        }

        // ── Two-lane retry for loop-contract harnesses ──────────────────
        // A loop contract asks two independent questions and this single lane
        // had to answer both, so a VALID but WEAK invariant made a CORRECT
        // program report FAILED. Only reached when THIS lane did not already
        // succeed, so a passing harness is never re-adjudicated — that is the
        // no-regression net. See loop_two_lane.rs for the soundness argument.
        if !crate::demotion::is_effective_manual_success(
            result.status,
            harness.attributes.should_panic,
            result.failed_properties,
        ) {
            self.maybe_two_lane_retry(binary, harness, &mut result);
        }

        self.process_output(&result, harness, thread_index)?;
        // A concrete-playback `#[test]` asserts "these inputs reproduce the
        // failure". Once a loop has hit the unwind bound we cannot honour that
        // claim: the satisfying model was free to use the cut back-edge, so the
        // emitted test may reproduce nothing at all. `extract_harness_values`
        // already skips the class-"unwind" check itself; this covers the sibling
        // checks in the same truncated run, which are `Unknown` for the reason
        // recorded at the classification site above. Narrow on purpose — it fires
        // only when an unwinding assertion actually FAILED.
        if unwind_exhausted && self.args.concrete_playback.is_some() {
            println!(
                "WARNING: no concrete playback for `{}`: a loop hit the unwind bound, so the \
                 counterexample may depend on a truncated path and the generated test could \
                 fail to reproduce. Raise the bound and re-run.",
                harness.pretty_name
            );
        } else {
            self.gen_and_add_concrete_playback(harness, &mut result)?;
        }
        Ok(result)
    }
}

#[cfg(test)]
#[path = "harness_runner_tests.rs"]
mod tests;
