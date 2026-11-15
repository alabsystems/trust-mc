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
use crate::chc_claim_policy::{EvidenceAccounting, ctrex_evidence_is_complete};
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
    CtrexCategory, FailedProperties, OBLIGATION_FREE_CERTIFIED_QUALIFIER, ProofCrosscheck,
    VacuityShape, VerificationResult, VerificationStatus, classify_vacuity, has_satisfied_cover,
    has_unsatisfiable_cover,
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
        // Register the schedule so a wall-clock fire can NAME any harness that
        // never starts instead of dropping it from the transcript
        // (wall_clock_watchdog::write_unattempted_harnesses).
        crate::wall_clock_watchdog::register_harnesses(
            sorted_harnesses.iter().map(|harness| harness.pretty_name.as_str()),
        );
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

/// An unwinding bound was exhausted, so the search was TRUNCATED rather than a
/// bug found. Two shapes, one meaning:
///
/// * class `"unwind"` — the BMC loop bound. Some loop asked for an iteration
///   past `--unwind N` / `#[kani::unwind(N)]`, so the unwinding assertion the
///   unroller planted on the cut back-edge is among the FAILED checks (see
///   `classify_violation`).
/// * class `"recursion"` — the recursive-inline bound. `; RECURSIVE_UNWIND_ASSERTION:`
///   says recursive inlining exhausted the active harness unwind bound, and
///   `verdict_policy::recursion_unwind_property` relabels the harness's failure
///   as "recursion unwinding assertion" (class `"recursion"`, id 1).
///
/// These are the counterexample shapes that say nothing whatsoever about the
/// program. Every consumer that would otherwise present one as a bug — the CTREX
/// category, the not-certified caveat, concrete playback — keys off this
/// predicate.
///
/// The `"recursion"` arm is the fix for a measured false positive: on the trustc
/// route `kani/DynTrait/unsized_cast.rs` and `unsized_rc_cast.rs` exhaust the
/// bound in `Box`/`Rc` drop-glue dyn dispatch, and the truncated search was
/// reported as `[AY:CTREX_CAT:Genuine]` — a CERTIFIED failure on a correct
/// program — purely because the class was spelled `recursion` and not `unwind`.
/// Fail closed: the engine could not decide the harness, so it must not certify.
fn unwind_bound_exhausted(results: &[crate::property_model::Property]) -> bool {
    results.iter().any(|p| {
        p.status == crate::property_model::CheckStatus::Failure
            && matches!(p.property_id.class.as_ref(), "unwind" | "recursion")
    })
}

fn demotion_reasons_marker(result: &VerificationResult) -> Option<String> {
    (!result.demotion_reasons.is_empty())
        .then(|| format!("[AY:DEMOTION_REASONS:{}]", result.demotion_reasons.join(",")))
}

fn proof_crosscheck_marker(proof_crosscheck: &ProofCrosscheck) -> Option<String> {
    proof_crosscheck.label().map(|label| format!("[AY:PROOF_CROSSCHECK:{label}]"))
}

/// V4b's trigger: a harness about to count as verified while its obligation set
/// is EMPTY.
///
/// Deliberately reads no certificate FILE. Whether the compiler vouched for the
/// body decides how [`settle_no_checks_result`] settles the result, never
/// whether this fires: zero obligations discharged is not a proof, whichever
/// lane produced them. A result already settled as a certified obligation-free
/// success carries [`OBLIGATION_FREE_CERTIFIED_QUALIFIER`] and is not about to
/// count as a CLEAN success, so the gate does not fire twice on it (the second
/// check after the two-lane retry would otherwise print the marker again).
/// `should_panic` is exempt, as for V4, because its verdict is panic-shaped.
/// A cover-only harness has non-empty `results`, so V5 adjudicates it.
pub(crate) fn no_checks_gate_fires(result: &VerificationResult, should_panic: bool) -> bool {
    !should_panic
        && result.status != VerificationStatus::Failure
        && result.results.is_empty()
        && !result.is_certified_obligation_free()
}

/// Settle a result whose obligation set is EMPTY, once [`no_checks_gate_fires`]
/// has said so.
///
/// * CERTIFIED (`ArtifactMetadata.obligation_free_body`): the walk in
///   `codegen_ay/obligation_free_walk.rs` proved every reachable statement and
///   terminator carries no obligation, so nothing was dropped and nothing
///   could fail. The harness stays a success and exits 0, as it does under
///   Kani — carrying [`OBLIGATION_FREE_CERTIFIED_QUALIFIER`], which keeps it
///   from ever reading as a clean proof: the verdict line, the qualifier
///   marker, the summary verdict and the SARIF note all key on it (D16).
/// * NOT certified: an obligation may have been dropped, and zero checks
///   discharged is not a proof. `INCONCLUSIVE (no checks)`, exit 1.
pub(crate) fn settle_no_checks_result(
    result: &mut VerificationResult,
    certified_obligation_free: bool,
) {
    if certified_obligation_free {
        result.status = VerificationStatus::Success;
        result.failed_properties = FailedProperties::None;
        if !result.is_certified_obligation_free() {
            result.proof_qualifiers.push(OBLIGATION_FREE_CERTIFIED_QUALIFIER.to_string());
        }
    } else {
        result.status = VerificationStatus::Failure;
        result.failed_properties = FailedProperties::Other;
    }
}

/// The `[AY:VACUOUS:no-checks]` line.
///
/// The tag prefix is identical for both causes, because consumers key on it:
/// `tools/kani-domination` classifies `[AY:VACUOUS`, and the tests and
/// expected files match `[AY:VACUOUS:no-checks]`. The explanation — and, since
/// D16's second step, the verdict — differs: a certified body dropped no
/// obligation and had none to prove; an uncertified one may have dropped one.
pub(crate) fn no_checks_marker(harness: &str, certified_obligation_free: bool) -> String {
    if certified_obligation_free {
        format!(
            "[AY:VACUOUS:no-checks] {harness}: the harness produced no verification conditions \
             — the compiler certified that no obligation site is reachable from it (every \
             reachable statement and terminator was walked), so nothing was dropped and \
             nothing could fail. Reported SUCCESSFUL with the proof qualifier \
             `{OBLIGATION_FREE_CERTIFIED_QUALIFIER}`, never as a clean proof: nothing was \
             proved because there was nothing to prove (Kani reports this shape as \
             SUCCESSFUL; see `trust-mc explain kani`)."
        )
    } else {
        format!(
            "[AY:VACUOUS:no-checks] {harness}: the harness produced no verification conditions \
             — and the compiler could not certify the body obligation-free, so an obligation \
             may have been dropped. Zero checks discharged is not a proof."
        )
    }
}

/// The non-clean proof qualifier of a SUCCESSFUL whose only checks are the anonymous
/// `chc.0` fallback ([`crate::property_model::Property::is_unattributed_chc_check`]).
pub(crate) const UNATTRIBUTED_CHC_CHECK_QUALIFIER: &str = "unattributed_check=chc.0";

/// [`UNATTRIBUTED_CHC_CHECK_QUALIFIER`] when `result` is a success whose every non-cover
/// check is the anonymous CHC fallback. A cover is its own obligation and does not
/// attribute the proof, so covers are ignored. Only a success qualifies: the qualifier
/// marks a proof that names nothing, and a FAILED verdict is reported unchanged.
pub(crate) fn unattributed_chc_check_qualifier(
    result: &VerificationResult,
) -> Option<&'static str> {
    if result.status != VerificationStatus::Success {
        return None;
    }
    let mut checks = result.results.iter().filter(|property| !property.is_cover_property());
    let first = checks.next()?;
    (first.is_unattributed_chc_check()
        && checks.all(|property| property.is_unattributed_chc_check()))
    .then_some(UNATTRIBUTED_CHC_CHECK_QUALIFIER)
}

/// Whether every FAILED non-cover check of `result` is the anonymous CHC fallback
/// ([`crate::property_model::Property::is_unattributed_chc_check`]), and there is at least one.
/// Such a failure names no property, so it cannot be certified as a panic (V7).
pub(crate) fn should_panic_rests_on_unattributed_chc_check(result: &VerificationResult) -> bool {
    let mut failing = result
        .results
        .iter()
        .filter(|property| !property.is_cover_property())
        .filter(|property| property.status == crate::property_model::CheckStatus::Failure);
    let Some(first) = failing.next() else {
        return false;
    };
    first.is_unattributed_chc_check()
        && failing.all(|property| property.is_unattributed_chc_check())
}

/// The proof qualifiers a result reports: the backend's own, then
/// [`UNATTRIBUTED_CHC_CHECK_QUALIFIER`] when it applies.
pub(crate) fn reported_proof_qualifiers(result: &VerificationResult) -> Vec<String> {
    let mut quals = result.proof_qualifiers.clone();
    if let Some(qualifier) = unattributed_chc_check_qualifier(result) {
        quals.push(qualifier.to_string());
    }
    quals
}

pub(crate) fn proof_qualifiers_marker(result: &VerificationResult) -> Option<String> {
    if result.status != VerificationStatus::Success {
        return None;
    }

    let mut quals = reported_proof_qualifiers(result);
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
/// Sound-approximation categories whose events the compiler never accounts
/// with a freed-var identity (`ChcVc::record_approximation_identity`): the
/// reachability boundary's unstubbed abstraction is decided before the CHC
/// encoder runs, so no dependence analysis sees what it frees.
fn ctrex_certifiable_genuine(
    categories: &[String],
    ev: &crate::ay_parse::vc_artifact::ApproximationEvidence,
    results: &[crate::property_model::Property],
) -> bool {
    if !ctrex_evidence_is_complete(
        categories,
        EvidenceAccounting { complete: ev.complete, accounted: ev.accounted },
    ) {
        return false;
    }

    // DEPENDENCE: the counterexample is genuine iff at least one VIOLATED
    // `error_p{N}` is data-INDEPENDENT of every freed var. A violated check
    // whose verdict is dependent, or unknown/absent, leaves the taint.
    // An unattributed failure (`chc.0`) carries id 0, which is not the id of
    // the check that failed, so its lookup would read another check's verdict.
    results.iter().any(|p| {
        p.status == crate::property_model::CheckStatus::Failure
            && !p.is_unattributed_chc_check()
            && matches!(ev.dependent_by_id.get(&p.property_id.id), Some(Some(false)))
    })
}

/// Replay gate for a counterexample certified independent of a float-binop
/// table (`trust_mc_core::chc::FLOAT_BINOP_TABLE_F32` / `_F64`).
///
/// `None` when no table is among the freed variables: the gate does not apply.
/// Otherwise `Ok` names the violated, table-independent `error_p{N}` that a
/// replay derived on the system with every table read removed
/// (`trust_mc_driver::replay_error_derivation_free_of`), and `Err` says why no
/// violated check did.
///
/// The per-property dependence verdict is computed by a name-based taint
/// closure over the compiler's rules. The table is a whole array threaded
/// through every relation, so a counterexample certified from that verdict
/// alone would rest entirely on the closure seeing every flow of a table value;
/// the replay confirms the counterexample itself instead — a derivation of the
/// violated check that never evaluates a select, re-checked with a total model
/// on an independently rebuilt system. Only a SAT verdict can be upgraded by
/// this gate, and only when BOTH the dependence analysis and the replay agree.
fn float_table_ctrex_replay(
    smt_text: &str,
    ev: &crate::ay_parse::vc_artifact::ApproximationEvidence,
    results: &[crate::property_model::Property],
) -> Option<Result<String, String>> {
    let tables: Vec<&str> = ev
        .approximated_vars
        .iter()
        .map(String::as_str)
        .filter(|var| trust_mc_core::chc::is_float_binop_table_var(var))
        .collect();
    if tables.is_empty() {
        return None;
    }
    let mut refusals = Vec::new();
    for property in results {
        if property.status != crate::property_model::CheckStatus::Failure
            || !matches!(ev.dependent_by_id.get(&property.property_id.id), Some(Some(false)))
        {
            continue;
        }
        let Some(relation) = ev.relation_by_id.get(&property.property_id.id) else {
            continue;
        };
        match trust_mc_driver::replay_error_derivation_free_of(smt_text, relation, &tables) {
            Ok(summary) => return Some(Ok(summary)),
            Err(reason) => refusals.push(format!("{relation}: {reason}")),
        }
    }
    Some(Err(if refusals.is_empty() {
        "no violated table-independent check to replay".to_string()
    } else {
        refusals.join("; ")
    }))
}

/// Kani's wording for both same-allocation obligations of the offset models.
const SAME_ALLOCATION_CHECK: &str = "point to the same allocation";

/// BMC lane: a counterexample whose ONLY taint is `offset_provenance_unresolved`
/// and whose failing checks all lie OUTSIDE the same-allocation family is
/// genuine.
///
/// In the BMC lane that record frees no value. A `ptr::offset` / `add` / `sub`
/// site whose allocation cannot be named emits no same-allocation obligation at
/// all (alloc_view.rs `emit_offset_same_allocation_check`), which can only REMOVE
/// failures; an `offset_from` site falls back to the region predicate, which
/// affects only its own same-allocation check and an assumption that cuts
/// paths. Neither can make a DIFFERENT check fail, so an assertion, overflow or
/// bounds counterexample under that taint is real — and the record still
/// demotes every proof. The CHC lane frees a symbolic `obj_id` instead and keeps
/// the per-property dependence route (`ctrex_certifiable_genuine`); its
/// artifacts carry `error_p{N}` properties, a BMC artifact carries none.
fn bmc_offset_only_ctrex_is_genuine(
    categories: &[String],
    ev: &crate::ay_parse::vc_artifact::ApproximationEvidence,
    results: &[crate::property_model::Property],
) -> bool {
    let is_bmc_artifact = ev.dependent_by_id.is_empty();
    let offset_only = !categories.is_empty()
        && categories.iter().all(|c| c.starts_with("offset_provenance_unresolved="));
    let mut failing =
        results.iter().filter(|p| p.status == crate::property_model::CheckStatus::Failure);
    let any_failing = failing.clone().next().is_some();
    is_bmc_artifact
        && offset_only
        && any_failing
        && failing.all(|p| !p.description.contains(SAME_ALLOCATION_CHECK))
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
    ///
    /// An upgrade also returns what it certified (`independent of ...`), which
    /// the caller prints as the `[AY:CTREX_CAT:Genuine:certified ...]` marker only
    /// when the category is still `Genuine` after
    /// [`Self::gate_genuine_on_havoc_reads`]. Printed here, a counterexample the
    /// havoc gate then refused carried a `Genuine` marker before its final
    /// `OverApproximation` one, and the readers that take any `Genuine` marker as
    /// a certificate (the dual gate, the corpus scorer's single-harness path)
    /// counted a false certificate (`chc_dead_heap_owner_target_dual.rs`
    /// `safe_string_moved_read`, once main's Rule E accounted its havoc).
    fn recertify_overapprox_ctrex(
        &self,
        category: CtrexCategory,
        smt_binary: &Path,
        results: &[crate::property_model::Property],
    ) -> (CtrexCategory, Option<String>) {
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
            _ => return (category, None),
        };
        let vc_path = crate::ay_parse::vc_artifact::vc_artifact_path_for_smt(smt_binary);
        let Some(ev) = crate::ay_parse::vc_artifact::load_approximation_evidence(&vc_path) else {
            return (category, None); // no evidence → stay tainted (fail-closed)
        };
        if bmc_offset_only_ctrex_is_genuine(&categories, &ev, results) {
            let upgrade = format!(
                "independent of the unresolved offset allocation(s) (was {})",
                category.label()
            );
            return (CtrexCategory::Genuine, Some(upgrade));
        }
        if !ctrex_certifiable_genuine(&categories, &ev, results) {
            return (category, None);
        }
        // A float-binop table among the freed variables: the counterexample must
        // also REPLAY without any table read (`float_table_ctrex_replay`).
        if ev.approximated_vars.iter().any(|var| trust_mc_core::chc::is_float_binop_table_var(var))
        {
            let replay = std::fs::read_to_string(smt_binary)
                .map_err(|error| format!("cannot read {}: {error}", smt_binary.display()))
                .and_then(|text| {
                    float_table_ctrex_replay(&text, &ev, results)
                        .unwrap_or_else(|| Err("no float-binop table is freed".to_string()))
                });
            match replay {
                Ok(summary) => marker_println!(self, "[AY:CTREX_REPLAY:confirmed] {summary}"),
                Err(reason) => {
                    marker_println!(
                        self,
                        "[AY:CTREX_REPLAY:refused] the counterexample is independent of the \
                         float-binop table by the dependence analysis but did not replay \
                         without it, so it stays {}: {reason}",
                        category.label()
                    );
                    return (category, None);
                }
            }
        }
        let upgrade = format!(
            "independent of {} freed var(s) (was {})",
            ev.approximated_vars.len(),
            category.label()
        );
        (CtrexCategory::Genuine, Some(upgrade))
    }

    /// fix/chc-false-certificates: a `Genuine` CHC counterexample stays
    /// `Genuine` only when some violated check is derivable without reading a
    /// value no clause defines (`crate::ctrex_havoc`). A refused counterexample
    /// is an over-approximation: it still fails the harness, but it is never
    /// reported as a certified bug.
    ///
    /// `strict` (a `should_panic` harness, where a `Genuine` counterexample is
    /// the proof) adds the gate's strict rules (`certify_error_free_of_havoc`).
    fn gate_genuine_on_havoc_reads(
        &self,
        category: CtrexCategory,
        smt_binary: &Path,
        results: &[crate::property_model::Property],
        strict: bool,
    ) -> CtrexCategory {
        if category != CtrexCategory::Genuine {
            return category;
        }
        match crate::ctrex_havoc::havoc_gate(smt_binary, results, strict) {
            crate::ctrex_havoc::HavocGate::NotApplicable
            | crate::ctrex_havoc::HavocGate::Certified(None) => category,
            crate::ctrex_havoc::HavocGate::Certified(Some(summary)) => {
                marker_println!(self, "[AY:CTREX_HAVOC:certified] {summary}");
                category
            }
            crate::ctrex_havoc::HavocGate::Refused(reason) => {
                marker_println!(
                    self,
                    "[AY:CTREX_HAVOC:refused] every violated check depends on a value no \
                     clause defines, so the counterexample is not certified: {reason}"
                );
                CtrexCategory::OverApproximation { categories: vec!["havoc_read=1".to_string()] }
            }
        }
    }

    /// Retry a loop-contract harness this run did not prove, once, in a child
    /// driver that checks the same harness under the same loop-contract
    /// semantics with the CHC lane, the compound-measure encoding and a longer
    /// per-query budget (`loop_two_lane.rs` has the design and why it has one
    /// lane since review round 3). A CHILD PROCESS: the unsoundness counters
    /// are process-global and accumulate, so an in-process second run would
    /// trip markers this run never trips and demote a clean proof to a failure.
    ///
    /// The verdict moves only toward SUCCESS, and only when `lanes::merge`
    /// accepts the child: it checked exactly this harness, proved every check,
    /// and reported the base-case and inductive-step obligations. A wrongly
    /// accepted child is a missed bug, so each of those is a precondition; on
    /// any doubt the original verdict stands untouched.
    fn maybe_two_lane_retry(
        &self,
        binary: &Path,
        harness: &HarnessMetadata,
        result: &mut VerificationResult,
        deadline: crate::deadline::Deadline,
    ) {
        use crate::loop_two_lane as lanes;

        // `binary` is already the resolved `.smt2` for this harness (see the
        // call site) — the artifact sits beside it.
        let vc_path = crate::ay_parse::vc_artifact::vc_artifact_path_for_smt(binary);
        if !lanes::harness_is_eligible(&vc_path) {
            return;
        }

        // Never START a lane the active route will refuse. The lane sets an
        // engine generation knob on its child and the Trustc route refuses a
        // child while one is set, so spawning one there cost the retry AND
        // printed the CHILD's refusal inside this process's diagnostic — where
        // a reader (`tools/kani-domination`'s route check included) took it for
        // THIS process refusing and scored an attested, verdict-bearing run a
        // route error. Say by name what the route cannot do instead; the
        // first run's verdict stands.
        let is_trustc = matches!(self.route, crate::session::CompilerRoute::Trustc { .. });
        if let Some(limitation) = lanes::route_limitation(is_trustc) {
            println!("{}", limitation.marker());
            println!("{}", limitation.explanation());
            return;
        }

        // One clock for the retry, inside the harness's own deadline: the
        // parent's watchdog kills it ~10s past that deadline, and a kill
        // degrades this row to a timeout — which would make the feature a
        // regression. So the retry is not started when what the first run left
        // is below a lane's floor.
        let retry_start = std::time::Instant::now();
        // `--harness` is a filter over PRETTY names; passing the mangled name
        // yields "no harnesses matched the harness filter" and a silent no-op.
        let harness_name = harness.pretty_name.as_str();
        let Some(budget) = lanes::lane_budget(retry_start.elapsed(), deadline.remaining()) else {
            marker_println!(
                self,
                "{} — the loop-contract retry is not started; the first lane's verdict stands",
                deadline.stage_skipped_marker("two-lane-retry", lanes::LANE_MIN_BUDGET)
            );
            return;
        };
        // The lane's memory cap is what THIS HARNESS owns of the driver's armed
        // cap (AY ask R2), the same share its in-process envelope gets: under
        // `--jobs N` that is the cap less the driver's footprint, divided by N.
        // The lane runs alone and one harness, on a one-thread pool (its argv
        // carries no `--jobs`), so the whole share is its cap.
        let child_cap_mb = retry_child_cap();
        // The row export (`TRUST_MC_CHC_ROW_EXPORT_DIR`): the lane writes its own
        // export below this harness's, never over it.
        let export_dir = retry_lane_export_dir(harness_name);
        let Some(mut cmd) = lanes::retry_lane_command(harness_name, export_dir.as_deref()) else {
            println!("[AY:LOOP_TWO_LANE] obligations lane did not run");
            return;
        };
        if let Some(mb) = child_cap_mb {
            cmd.env("TRUST_MC_AY_MEMORY_LIMIT_MB", mb.to_string());
        }
        let child_argv: Vec<String> =
            cmd.get_args().map(|a| a.to_string_lossy().into_owned()).collect();
        let lane = crate::session::run_piped_with_timeout(cmd, budget).ok();

        // Under --allow-unpinned-ay the lane demotes its own success; see
        // `lanes::child_proved`.
        let unpinned = crate::ay_binary::unpinned_solver_accepted();

        let outcome = match &lane {
            None => {
                println!("[AY:LOOP_TWO_LANE] obligations lane did not run");
                "did not run".to_string()
            }
            Some(out) => {
                let stdout = String::from_utf8_lossy(&out.stdout).into_owned();
                match lanes::merge(harness_name, lanes::child_proved(&stdout, unpinned), &stdout) {
                    lanes::TwoLaneOutcome::Proved => {
                        println!(
                            "[AY:LOOP_TWO_LANE] every check, the loop contract included, \
                             discharged in the retry lane"
                        );
                        // Every check this run could not discharge WAS
                        // discharged, with the loop contract on, in the lane.
                        // Leaving them marked FAILURE would print "Failed
                        // Checks: ..." directly above a SUCCESSFUL verdict.
                        // Record WHERE each one was discharged rather than
                        // silently flipping it.
                        for prop in &mut result.results {
                            if prop.status == crate::property_model::CheckStatus::Failure {
                                prop.status = crate::property_model::CheckStatus::Success;
                                prop.description = std::borrow::Cow::Owned(format!(
                                    "{} [discharged in the loop-contract retry]",
                                    prop.description
                                ));
                            }
                        }
                        result.status = VerificationStatus::Success;
                        result.failed_properties = FailedProperties::None;
                        "proved".to_string()
                    }
                    lanes::TwoLaneOutcome::Inconclusive(why) => {
                        let tail: Vec<&str> = stdout
                            .lines()
                            .filter(|l| l.starts_with("VERIFICATION") || l.starts_with("error"))
                            .collect();
                        println!("[AY:LOOP_TWO_LANE] not proved: {why} (lane: {tail:?})");
                        format!("inconclusive: {why}")
                    }
                }
            }
        };
        record_retry_export(
            harness_name,
            serde_json::json!({
                "lane": "loop-contract retry (rule on, CHC, compound measures, every check)",
                "argv": child_argv,
                "env_set": {
                    "TRUST_MC_LOOP_LANE": "obligations",
                    "TRUST_MC_COMPOUND_DECREASES": "1",
                    "TRUST_MC_AY_MEMORY_LIMIT_MB": child_cap_mb,
                },
                "lane_export_dir": export_dir.as_ref().map(|d| d.display().to_string()),
                "wall_budget_ms": budget.as_millis(),
                "wall_ms": retry_start.elapsed().as_millis(),
                "outcome": outcome,
                "note": "the lane child exports its own query under lane_export_dir; \
                         source.smt2 and the rows above are this (parent) process's",
            }),
        );
    }

    /// Settle a harness whose obligation set is EMPTY. The caller has already
    /// established [`no_checks_gate_fires`]; the compiler's certificate decides
    /// between the two outcomes of [`settle_no_checks_result`].
    fn settle_no_checks(
        &self,
        binary: &Path,
        harness: &HarnessMetadata,
        result: &mut VerificationResult,
    ) {
        let certified = crate::ay_parse::vc_artifact::artifact_body_is_obligation_free(
            &crate::ay_parse::vc_artifact::vc_artifact_path_for_smt(binary),
        );
        marker_println!(self, "{}", no_checks_marker(&harness.pretty_name, certified));
        settle_no_checks_result(result, certified);
    }

    /// Run the verification process for a single harness
    pub(crate) fn check_harness(
        &self,
        binary: &Path,
        harness: &HarnessMetadata,
        unsoundness_counts: &crate::unsoundness_counts::CrateUnsoundnessCounts,
    ) -> Result<VerificationResult> {
        crate::wall_clock_watchdog::mark_harness_started(&harness.pretty_name);
        let thread_index = rayon::current_thread_index().unwrap_or_default();
        // A loop-contract retry child names every harness it checks, whatever
        // its output format; the parent accepts it only when this is the one
        // harness it retried (`loop_two_lane::lane_checked_exactly`). Read by
        // the parent and never shown, so `--quiet` does not suppress it.
        if crate::loop_two_lane::is_lane_child() {
            println!("{}", crate::loop_two_lane::lane_harness_marker(&harness.pretty_name));
        }
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
        let run_ay_started = std::time::Instant::now();
        let mut result = self.with_timer(
            || self.run_ay(binary, harness, demoted_fallback_count, deadline),
            "run_ay",
        )?;
        crate::stage_timing::record("run-ay", run_ay_started, &format!("{:?}", result.status));
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
            //
            // `chc_exact_counterexample` is the ONE case where that detection is
            // wrong in the other direction, and it is wrong for a decided row.
            // `interpret_chc_trivial_unsafe` DERIVES `error` (constraint-free
            // zero-arity closure, or an SMT-model-backed acyclic witness) and
            // then reports it through the legacy aggregate `chc.0` property
            // whenever per-property attribution finds no `error_p{N}` in the VC
            // table. `chc.0` carries class "chc", and the failure class comes
            // from the REACHABLE check's kind — so an exactly derived memory
            // safety / pointer-overflow / valid-value counterexample arrives as
            // `Other` + no non-chc violation, i.e. spelled exactly like a
            // solver that could not decide. Measured 2026-09-14 on three corpus
            // units (`expected/pointer-overflow/main.rs`,
            // `expected/valid-value-checks/non_null.rs`,
            // `kani/Overflow/pointer_overflow_fail.rs`): each printed
            // `[AY:CTREX] … (exact CHC derivation)` and
            // `[AY:UNKNOWN_QUALITY:Clean]` beside `[AY:CTREX_CAT:Unknown]`.
            //
            // The flag does NOT decide the category. It routes the row into
            // `classify_ctrex` below, which still returns EncodingGap /
            // OverApproximation when the harness carries approximations — only
            // a harness with zero unsoundness counts comes out `Genuine`. So no
            // check is weakened: a row that cannot be certified still is not.
            // Every other producer leaves the flag `false`, which is the
            // pre-existing fail-closed reading.
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
            } else if chc_failure_is_undecided(
                result.failed_properties,
                has_non_chc_violation,
                result.chc_exact_counterexample,
            ) {
                result.ctrex_category = Some(CtrexCategory::Unknown);
            } else {
                // Task #78: an OverApproximation counterexample can be SOUNDLY
                // certified Genuine when the compiler plumbed every
                // approximation's freed-var identity AND the violated
                // `error_p{N}`'s reachability is independent of every freed var.
                let category = classify_ctrex(harness, unsoundness_counts);
                let (category, recertified) =
                    self.recertify_overapprox_ctrex(category, binary, &result.results);
                let category = self.gate_genuine_on_havoc_reads(
                    category,
                    binary,
                    &result.results,
                    harness.attributes.should_panic,
                );
                // The upgrade's marker names `Genuine`: printed only when the havoc
                // gate kept it, so a refused counterexample shows no `Genuine` marker.
                if let Some(upgrade) = recertified {
                    if category == CtrexCategory::Genuine {
                        marker_println!(self, "[AY:CTREX_CAT:Genuine:certified {upgrade}]");
                    } else {
                        marker_println!(
                            self,
                            "[AY:CTREX_RECERTIFY:withdrawn] the upgrade ({upgrade}) was refused \
                             by the havoc gate"
                        );
                    }
                }
                result.ctrex_category = Some(category);
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
        // The vacuity gate (V4 here, V5 below) that failed this harness closed,
        // if one did. The loop-contract retry never overturns it
        // (`loop_two_lane::FailClosedGate`).
        let mut vacuity_gate: Option<crate::loop_two_lane::FailClosedGate> = None;
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
                    vacuity_gate = Some(crate::loop_two_lane::FailClosedGate::UnsatAssumption);
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
                    vacuity_gate = Some(crate::loop_two_lane::FailClosedGate::DeadChecks);
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
        // A proof of zero obligations is not a proof. Two outcomes, decided by
        // the compiler's obligation-free certificate
        // (`ArtifactMetadata.obligation_free_body`), per D16
        // (docs/kani-spec-engine-plan-2026-09-10.md, second step, 2026-09-13):
        //
        // * uncertified: fail closed as `VERIFICATION:- INCONCLUSIVE (no
        //   checks)`, exit 1 — an obligation may have been dropped;
        // * certified: the walk in `codegen_ay/obligation_free_walk.rs` proved
        //   every reachable statement AND terminator carries no obligation, so
        //   the harness exits 0 as it does under Kani — visibly, never as a
        //   clean pass: `[AY:VACUOUS:no-checks]`, the verdict line
        //   `SUCCESSFUL (no checks — compiler-certified obligation-free)`, the
        //   `no_checks=compiler_certified_obligation_free` proof qualifier in
        //   place of `clean`, `successful_no_checks` in the summary and a SARIF
        //   note.
        //
        // Cover-only harnesses are exempt: their covers ARE the obligation, and
        // V5 below adjudicates them.
        //
        // History, because it is the hazard this gate guards: from 886f60544
        // (2026-08-25) a certified body SKIPPED this gate, so
        // `fn h() { let _x: u8 = 3; }` printed a bare clean
        // `VERIFICATION:- SUCCESSFUL` with an empty `--sarif` report in BOTH
        // lanes — while the walk read TERMINATORS only, and lowered intrinsics
        // (`AddUnchecked`, `Offset`, `CopyNonOverlapping`, a raw deref) are
        // STATEMENTS it could not see. 2026-09-11 closed the skip and made every
        // empty set INCONCLUSIVE; the walk counts statement sites since
        // f5305896b, which is what lets a certified shape exit 0 THROUGH this
        // gate rather than around it.
        if no_checks_gate_fires(&result, harness.attributes.should_panic) {
            self.settle_no_checks(binary, harness, &mut result);
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
                vacuity_gate
                    .get_or_insert(crate::loop_two_lane::FailClosedGate::UnsatisfiableCover);
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
            vacuity_gate.get_or_insert(crate::loop_two_lane::FailClosedGate::Conformance);
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
                    "[AY:CTREX_NOT_CERTIFIED] {}: NOT a counterexample — a loop or a recursive \
                     call hit the unwind bound, so the search was truncated before it could \
                     decide this harness. Nothing in your program was disproved. Raise the bound \
                     (--unwind N, --default-unwind N, or #[kani::unwind(N)]) and re-run; if the \
                     recursion or loop has no constant bound, use --ay-chc for unbounded proofs.",
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
            marker_println!(
                self,
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

        // V7 (should_panic resting only on the anonymous `chc.0` check): fail closed.
        //
        // `chc.0` is what a CHC result falls back to when the counterexample names
        // no registered property. It says `error` was reached, not WHAT reached it,
        // so it cannot show that the failure was a panic rather than UB, an abort or
        // an unsupported construct. The CHC interpreters already classify such a
        // counterexample as `Other`; this is the invariant at the one place every
        // lane's verdict passes, so no future producer can turn an anonymous failure
        // into `SUCCESSFUL (encountered one or more panics as expected)`.
        if harness.attributes.should_panic
            && matches!(result.failed_properties, FailedProperties::PanicsOnly)
            && should_panic_rests_on_unattributed_chc_check(&result)
        {
            marker_println!(
                self,
                "[AY:SHOULD_PANIC_NOT_CERTIFIED] {}: every failing check is the anonymous \
                 `chc.0` check, which names no property, so nothing shows the failure was the \
                 panic this should_panic harness asks for. Failing closed -- nothing was verified.",
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
        // no-regression net — and never when a vacuity gate failed the run
        // closed (`FailClosedGate`). See loop_two_lane.rs for the soundness
        // argument.
        let first_run_succeeded = crate::demotion::is_effective_manual_success(
            result.status,
            harness.attributes.should_panic,
            result.failed_properties,
        );
        let eligible = !first_run_succeeded
            && crate::loop_two_lane::harness_is_eligible(
                &crate::ay_parse::vc_artifact::vc_artifact_path_for_smt(binary),
            );
        match crate::loop_two_lane::retry_decision(first_run_succeeded, eligible, vacuity_gate) {
            crate::loop_two_lane::RetryDecision::NotNeeded => {}
            crate::loop_two_lane::RetryDecision::Refused(gate) => {
                println!("{}", gate.refusal_marker());
            }
            crate::loop_two_lane::RetryDecision::Start => {
                let retry_started = std::time::Instant::now();
                self.maybe_two_lane_retry(binary, harness, &mut result, deadline);
                crate::stage_timing::record(
                    "two-lane-retry",
                    retry_started,
                    &format!("{:?}", result.status),
                );
            }
        }

        // The V4b invariant again, after the last step that can turn a verdict
        // into a success: the two-lane retry sets `status = Success` itself.
        // Every harness `check_harness` verifies (bounded, CHC, native) reaches
        // `process_output` through here, so none of them can print a clean
        // success over an empty obligation set. It cannot fire twice on one
        // harness: the gate above either failed the result closed or settled
        // it as a certified obligation-free success, which the predicate
        // recognises by its qualifier, and nothing between the two checks
        // empties `results`.
        if no_checks_gate_fires(&result, harness.attributes.should_panic) {
            self.settle_no_checks(binary, harness, &mut result);
        }

        // An off-pin `ay` accepted under --allow-unpinned-ay: every harness
        // carries the marker and no success is printed as a clean SUCCESSFUL.
        // After the two-lane retry, so a retried success is demoted too; before
        // `process_output`, which prints the verdict.
        let clean_before_demotion = crate::loop_two_lane::clean_success_before_unpinned_demotion(
            &result,
            harness.attributes.should_panic,
        );
        if let Some(marker) = crate::ay_binary::demote_for_unpinned_solver(
            &mut result,
            harness.attributes.should_panic,
        ) {
            marker_println!(self, "{marker}");
            // A lane child tells its parent the demotion was the only caveat
            // (`loop_two_lane::child_proved`). Its stdout is read by the parent
            // and never shown, so `--quiet` does not suppress it.
            if clean_before_demotion && crate::loop_two_lane::is_lane_child() {
                println!("{}", crate::loop_two_lane::UNPINNED_DEMOTION_ONLY_MARKER);
            }
        }
        // A `TRUST_MC_LOOP_LANE=properties` success is never a proof: the
        // compiler checks no loop contract in such a process, and the retry no
        // longer starts one. Demoted after the retry and the solver-pin
        // demotion, before `process_output` prints the verdict.
        if let Some(marker) = crate::loop_two_lane::demote_properties_lane_success(
            &mut result,
            harness.attributes.should_panic,
            crate::loop_two_lane::is_properties_lane_child(),
        ) {
            marker_println!(self, "{marker}");
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
                "WARNING: no concrete playback for `{}`: a loop or a recursive call hit the \
                 unwind bound, so the counterexample may depend on a truncated path and the \
                 generated test could fail to reproduce. Raise the bound and re-run.",
                harness.pretty_name
            );
        } else if self.args.concrete_playback.is_some()
            && !crate::concrete_playback::witness_is_usable(
                result.validation_status,
                result.ctrex_category.as_ref(),
                result.solver_unknown_reason.is_some(),
                !result.demotion_reasons.is_empty()
                    || classify_ctrex(harness, unsoundness_counts) != CtrexCategory::Genuine,
            )
        {
            println!(
                "WARNING: no concrete playback for `{}`: the result has no validated \
                 counterexample or cover witness for the supported encoding.",
                harness.pretty_name
            );
        } else {
            self.gen_and_add_concrete_playback(harness, &mut result)?;
        }
        Ok(result)
    }
}

/// Is a non-demoted `Failure` on the CHC lane an UNDECIDED verdict wearing a
/// counterexample's clothes?
///
/// `FailedProperties::Other` with no non-`chc` failing property is how the CHC
/// lane spells "the solver did not decide" (`call_ay`'s undecided-model arm
/// preserves exactly that shape). It is also, unavoidably, how an EXACTLY
/// DERIVED non-panic counterexample arrives when per-property attribution found
/// no `error_p{N}`: the aggregate `chc.0` property carries class "chc", and the
/// failure class is the reachable check's kind (memory safety, pointer
/// overflow, a valid-value check ⇒ `Other`).
///
/// `chc_exact_counterexample` is the positive signal that separates them, set
/// only where the driver derived `error` itself. Every other producer leaves it
/// `false`, so the default reading stays fail-closed: an unattributed failure
/// the driver cannot vouch for is UNKNOWN, never a counterexample.
pub(crate) fn chc_failure_is_undecided(
    failed_properties: FailedProperties,
    has_non_chc_violation: bool,
    chc_exact_counterexample: bool,
) -> bool {
    matches!(failed_properties, FailedProperties::Other)
        && !has_non_chc_violation
        && !chc_exact_counterexample
}

/// The memory cap for the loop-contract retry's child driver: the share of
/// the armed cap that the harness on the calling thread owns
/// (`memory_limit::current_harness_share_bytes`: the cap less the driver's
/// footprint, divided by the `--jobs` pool). `None` when no cap is armed: the
/// child then derives its own.
fn retry_child_cap() -> Option<u64> {
    crate::memory_limit::retry_child_cap_mb(crate::memory_limit::current_harness_share_bytes())
}

/// The retry lane's own row-export directory, when this process exports
/// (`TRUST_MC_CHC_ROW_EXPORT_DIR`).
#[cfg(feature = "ay-chc-native")]
fn retry_lane_export_dir(harness: &str) -> Option<std::path::PathBuf> {
    crate::call_ay::retry_lane_export_dir(harness)
}

#[cfg(not(feature = "ay-chc-native"))]
fn retry_lane_export_dir(_harness: &str) -> Option<std::path::PathBuf> {
    None
}

/// Record the retry in this harness's row export, when this process exports.
#[cfg(feature = "ay-chc-native")]
fn record_retry_export(harness: &str, record: serde_json::Value) {
    crate::call_ay::record_loop_contract_retry(harness, record);
}

#[cfg(not(feature = "ay-chc-native"))]
fn record_retry_export(_harness: &str, _record: serde_json::Value) {}

#[cfg(test)]
#[path = "harness_runner_tests.rs"]
mod tests;
