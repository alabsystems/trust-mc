// Copyright 2026 Andrew Yates, Inc.
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Native full-verification API boundary.
//!
//! This module is intentionally stricter than the CLI-oriented solver plumbing:
//! a "full" verification request means an unbounded CHC/PDR-family solve over a
//! native [`ChcVc`]. Bounded VCs are demoted to diagnostic-only reports instead
//! of being reported as full proofs, and the default engine fails closed until the in-process CHC/PDR
//! backend is wired to this boundary.
//!
//! This legacy injected-engine report API is not the publication authority in
//! [`crate::evidence`]. A caller-provided [`ChcPdrEngine`] is part of this API's
//! trusted computing base; its `Proved` report must never be converted directly
//! into certified/public evidence without the private fresh-generation and
//! replay/derivation boundary required by `crate::evidence`.

use crate::{BmcVc, ChcVc};

/// Result type for full-verification API calls.
pub type FullVerificationResult = Result<FullVerificationReport, FullVerificationError>;

/// Result type produced by CHC/PDR-family engines.
pub type ChcPdrEngineResult = Result<ChcPdrReport, FullVerificationError>;

/// The unbounded engine family required for full verification.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash)]
pub enum FullVerificationEngine {
    /// Native CHC/PDR-family solving over Horn clauses.
    #[default]
    ChcPdr,

    /// No proof engine ran; the report records diagnostic-only evidence.
    DiagnosticOnly,
}

/// Solver options shared by full-verification engines.
#[derive(Debug, Clone, Default, PartialEq, Eq, Hash)]
pub struct FullVerificationOptions {
    /// Required unbounded engine family.
    pub engine: FullVerificationEngine,

    /// Optional solve budget in milliseconds.
    pub timeout_ms: Option<u64>,
}

impl FullVerificationOptions {
    /// Creates default CHC/PDR full-verification options.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Sets the solve budget.
    #[must_use]
    pub fn with_timeout(mut self, timeout_ms: u64) -> Self {
        self.timeout_ms = Some(timeout_ms);
        self
    }
}

/// A verification problem submitted to the full-verifier boundary.
#[derive(Debug, Clone)]
pub enum FullVerificationProblem {
    /// Unbounded CHC verification condition.
    Chc(Box<ChcVc>),

    /// Bounded verification condition.
    ///
    /// This variant exists so adapters can receive an explicit failure instead
    /// of silently treating bounded evidence as a full proof.
    Bmc(Box<BmcVc>),
}

impl FullVerificationProblem {
    /// Returns the problem kind without borrowing the contained VC.
    #[must_use]
    pub const fn kind(&self) -> FullVerificationProblemKind {
        match self {
            FullVerificationProblem::Chc(_) => FullVerificationProblemKind::Chc,
            FullVerificationProblem::Bmc(_) => FullVerificationProblemKind::Bmc,
        }
    }
}

/// Stable problem-kind discriminator for diagnostics and tests.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FullVerificationProblemKind {
    /// CHC problem.
    Chc,
    /// BMC problem.
    Bmc,
}

impl std::fmt::Display for FullVerificationProblemKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FullVerificationProblemKind::Chc => f.write_str("CHC"),
            FullVerificationProblemKind::Bmc => f.write_str("BMC"),
        }
    }
}

/// A full-verification request.
#[derive(Debug, Clone)]
pub struct FullVerificationRequest {
    /// The submitted verification problem.
    pub problem: FullVerificationProblem,

    /// Solver options.
    pub options: FullVerificationOptions,
}

impl FullVerificationRequest {
    /// Creates an unbounded CHC/PDR request.
    #[must_use]
    pub fn chc(vc: ChcVc) -> Self {
        Self {
            problem: FullVerificationProblem::Chc(Box::new(vc)),
            options: FullVerificationOptions::new(),
        }
    }

    /// Creates a bounded request that full verification will classify as diagnostic-only.
    #[must_use]
    pub fn bmc(vc: BmcVc) -> Self {
        Self {
            problem: FullVerificationProblem::Bmc(Box::new(vc)),
            options: FullVerificationOptions::new(),
        }
    }

    /// Replaces the request options.
    #[must_use]
    pub fn with_options(mut self, options: FullVerificationOptions) -> Self {
        self.options = options;
        self
    }
}

/// Trait implemented by native CHC/PDR-family engines.
///
/// Implementations must not use BMC as a proof-producing fallback. Returning
/// [`ChcPdrVerdict::Unknown`] or [`FullVerificationError`] is the
/// fail-closed response when an engine cannot establish an inductive result.
pub trait ChcPdrEngine {
    /// Solves a native CHC VC with an unbounded CHC/PDR-capable engine.
    fn solve_chc_pdr(&self, vc: &ChcVc, options: &FullVerificationOptions) -> ChcPdrEngineResult;
}

/// Concrete gaps that currently prevent `trust_mc_core` from constructing the
/// production native CHC/PDR engine by itself.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ChcPdrAdapterGap {
    /// `ChcVc` to HORN SMT-LIB emission exists in `trust_mc-compiler`, but is not a
    /// `trust_mc_core` API.
    CoreVisibleChcEmitter,

    /// Native solving exists in `trust_mc-driver`, but is coupled to `KaniSession`
    /// and an SMT-file/sidecar artifact path.
    SessionFreeNativeSolver,

    /// `trust_mc_core` depends on `ay_bindings`, not the `ay::chc` facade that
    /// exposes `AdaptivePortfolio`.
    CoreAYChcFacade,
}

impl std::fmt::Display for ChcPdrAdapterGap {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ChcPdrAdapterGap::CoreVisibleChcEmitter => {
                f.write_str("trust_mc_core-visible ChcVc -> HORN SMT/native lowering")
            }
            ChcPdrAdapterGap::SessionFreeNativeSolver => {
                f.write_str("session-free ay::chc native solver adapter")
            }
            ChcPdrAdapterGap::CoreAYChcFacade => {
                f.write_str("trust_mc_core access to the ay::chc facade or injected solver")
            }
        }
    }
}

impl<T: ChcPdrEngine + ?Sized> ChcPdrEngine for &T {
    fn solve_chc_pdr(&self, vc: &ChcVc, options: &FullVerificationOptions) -> ChcPdrEngineResult {
        (**self).solve_chc_pdr(vc, options)
    }
}

impl<T: ChcPdrEngine + ?Sized> ChcPdrEngine for Box<T> {
    fn solve_chc_pdr(&self, vc: &ChcVc, options: &FullVerificationOptions) -> ChcPdrEngineResult {
        (**self).solve_chc_pdr(vc, options)
    }
}

impl<T: ChcPdrEngine + ?Sized> ChcPdrEngine for std::sync::Arc<T> {
    fn solve_chc_pdr(&self, vc: &ChcVc, options: &FullVerificationOptions) -> ChcPdrEngineResult {
        (**self).solve_chc_pdr(vc, options)
    }
}

/// Full-verifier entrypoint for native in-process adapters.
#[derive(Debug, Clone)]
pub struct NativeFullVerifier<E = MissingChcPdrEngine> {
    engine: E,
}

impl NativeFullVerifier<MissingChcPdrEngine> {
    /// Creates a verifier that fails closed until a CHC/PDR engine is supplied.
    #[must_use]
    pub const fn new() -> Self {
        Self { engine: MissingChcPdrEngine }
    }
}

impl Default for NativeFullVerifier<MissingChcPdrEngine> {
    fn default() -> Self {
        Self::new()
    }
}

impl<E> NativeFullVerifier<E> {
    /// Creates a verifier backed by a native CHC/PDR engine implementation.
    #[must_use]
    pub const fn with_chc_pdr_engine(engine: E) -> Self {
        Self { engine }
    }
}

impl<E: ChcPdrEngine> NativeFullVerifier<E> {
    /// Verifies a request, demoting bounded inputs before the engine is called.
    pub fn verify(&self, request: FullVerificationRequest) -> FullVerificationResult {
        match request.problem {
            FullVerificationProblem::Chc(vc) => {
                let report = self.engine.solve_chc_pdr(&vc, &request.options)?;
                report.check_consistency()?;
                Ok(FullVerificationReport::from(report))
            }
            FullVerificationProblem::Bmc(_) => {
                Ok(FullVerificationReport::diagnostic_only(FullVerificationDiagnostic::new(
                    FullVerificationDiagnosticKind::BmcSuccessDemoted,
                    FullVerificationProblemKind::Bmc,
                    "bounded model-checking success is diagnostic-only and cannot establish an \
                     unbounded full proof",
                )))
            }
        }
    }
}

/// Default fail-closed engine used before the in-process backend is connected.
#[derive(Debug, Clone, Copy, Default)]
pub struct MissingChcPdrEngine;

impl MissingChcPdrEngine {
    /// Adapter work required before the default engine can become proof-producing.
    pub const ADAPTER_GAPS: &'static [ChcPdrAdapterGap] = &[
        ChcPdrAdapterGap::CoreVisibleChcEmitter,
        ChcPdrAdapterGap::SessionFreeNativeSolver,
        ChcPdrAdapterGap::CoreAYChcFacade,
    ];
}

impl ChcPdrEngine for MissingChcPdrEngine {
    fn solve_chc_pdr(&self, _vc: &ChcVc, _options: &FullVerificationOptions) -> ChcPdrEngineResult {
        Err(FullVerificationError::NotYetWired {
            component: "native CHC/PDR engine",
            reason: "native ay::chc solving exists in trust_mc-driver behind KaniSession/SMT-file \
                     plumbing, while trust_mc_core only owns ChcVc and ay_bindings; TODO wire a \
                     ChcVc lowering layer and a session-free ay::chc adapter before reporting \
                     proof-producing full verification"
                .into(),
            gaps: Self::ADAPTER_GAPS,
        })
    }
}

/// A CHC/PDR engine report before full-verification policy projection.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ChcPdrReport {
    /// Solver verdict from the CHC/PDR-family engine.
    pub verdict: ChcPdrVerdict,

    /// Stable problem statistics from the submitted CHC system.
    pub stats: ChcPdrStats,
}

impl ChcPdrReport {
    /// Creates a CHC/PDR report.
    #[must_use]
    pub const fn new(verdict: ChcPdrVerdict, stats: ChcPdrStats) -> Self {
        Self { verdict, stats }
    }

    /// Creates a proof-producing CHC/PDR report.
    #[must_use]
    pub fn proved(evidence: ChcPdrProofEvidence) -> Self {
        let stats = evidence.stats;
        Self { verdict: ChcPdrVerdict::Proved(evidence), stats }
    }

    /// Creates a reachable-error CHC/PDR report.
    #[must_use]
    pub const fn counterexample(
        stats: ChcPdrStats,
        evidence: ChcPdrCounterexampleEvidence,
    ) -> Self {
        Self { verdict: ChcPdrVerdict::Counterexample(evidence), stats }
    }

    /// Creates an inconclusive CHC/PDR report.
    #[must_use]
    pub const fn unknown(stats: ChcPdrStats, reason: UnknownReason) -> Self {
        Self { verdict: ChcPdrVerdict::Unknown(reason), stats }
    }

    /// Checks report-level proof evidence invariants before policy projection.
    ///
    /// This is intentionally lightweight: it does not replay a proof, but it
    /// rejects internally inconsistent proof-producing reports before they can be
    /// surfaced as full verification.
    pub fn check_consistency(&self) -> Result<(), FullVerificationError> {
        if let ChcPdrVerdict::Proved(evidence) = &self.verdict {
            evidence.check_consistency(self.stats)?;
        }

        Ok(())
    }
}

/// Stable CHC/PDR problem statistics.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash)]
pub struct ChcPdrStats {
    /// Number of CHC relations/predicates in the solved system.
    pub relation_count: usize,

    /// Number of Horn clauses/rules in the solved system.
    pub clause_count: usize,
}

impl ChcPdrStats {
    /// Captures stable statistics from a native CHC VC.
    #[must_use]
    pub fn from_vc(vc: &ChcVc) -> Self {
        Self { relation_count: vc.relations.len(), clause_count: vc.rules.len() }
    }
}

/// Verdicts produced by unbounded CHC/PDR-family engines.
#[derive(Debug, Clone, PartialEq, Eq)]
#[allow(clippy::large_enum_variant)]
pub enum ChcPdrVerdict {
    /// A trusted injected engine reports that error is unreachable.
    ///
    /// This is not publication authority; see the module-level trust-boundary note.
    Proved(ChcPdrProofEvidence),

    /// Error is reachable.
    Counterexample(ChcPdrCounterexampleEvidence),

    /// The engine could not decide the query.
    Unknown(UnknownReason),
}

/// Report evidence accepted from a trusted injected CHC/PDR-family engine.
///
/// This type is distinct from `crate::evidence::ChcPdrProofEvidence` and does
/// not grant certified/public evidence authority.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ChcPdrProofEvidence {
    /// Kind of unbounded CHC/PDR proof.
    pub kind: ChcPdrProofKind,

    /// CHC system statistics covered by this proof.
    pub stats: ChcPdrStats,

    /// Engine-authored metadata for later private replay/derivation checks.
    pub metadata: FullProofEvidenceMetadata,

    /// Number of invariant formulas reported by the engine.
    pub invariant_count: usize,

    /// Candidate artifacts available for private replay/checking.
    pub artifacts: Vec<FullVerificationArtifact>,
}

impl ChcPdrProofEvidence {
    /// Creates CHC validity evidence for an unreachable error query.
    #[must_use]
    pub fn chc_validity(stats: ChcPdrStats) -> Self {
        Self {
            kind: ChcPdrProofKind::ChcValidity,
            stats,
            metadata: FullProofEvidenceMetadata::default(),
            invariant_count: 0,
            artifacts: Vec::new(),
        }
    }

    /// Creates PDR invariant proof evidence.
    #[must_use]
    pub fn pdr_invariant(stats: ChcPdrStats, invariant_count: usize) -> Self {
        Self {
            kind: ChcPdrProofKind::PdrInvariant,
            stats,
            metadata: FullProofEvidenceMetadata::default(),
            invariant_count,
            artifacts: Vec::new(),
        }
    }

    /// Attaches proof evidence metadata.
    #[must_use]
    pub fn with_metadata(mut self, metadata: FullProofEvidenceMetadata) -> Self {
        self.metadata = metadata;
        self
    }

    /// Attaches a solver transcript hash to the proof metadata.
    #[must_use]
    pub fn with_transcript_hash(mut self, hash: EvidenceHash) -> Self {
        self.metadata.transcript_hashes.push(hash);
        self
    }

    /// Attaches a proof replay log hash to the proof metadata.
    #[must_use]
    pub fn with_replay_hash(mut self, hash: EvidenceHash) -> Self {
        self.metadata.replay_hashes.push(hash);
        self
    }

    /// Attaches a candidate replay artifact.
    #[must_use]
    pub fn with_artifact(mut self, artifact: FullVerificationArtifact) -> Self {
        self.artifacts.push(artifact);
        self
    }

    fn check_consistency(&self, report_stats: ChcPdrStats) -> Result<(), FullVerificationError> {
        if self.stats != report_stats {
            return Err(FullVerificationError::InvalidProofEvidence {
                reason: format!(
                    "proof evidence stats {:?} do not match CHC/PDR report stats {:?}",
                    self.stats, report_stats
                ),
            });
        }

        match self.kind {
            ChcPdrProofKind::ChcValidity if self.invariant_count != 0 => {
                return Err(FullVerificationError::InvalidProofEvidence {
                    reason: format!(
                        "CHC validity proof reported {} invariant formula(s)",
                        self.invariant_count
                    ),
                });
            }
            ChcPdrProofKind::PdrInvariant if self.invariant_count == 0 => {
                return Err(FullVerificationError::InvalidProofEvidence {
                    reason: "PDR invariant proof reported zero invariant formulas".into(),
                });
            }
            _ => {}
        }

        for artifact in &self.artifacts {
            if artifact.label.trim().is_empty() {
                return Err(FullVerificationError::InvalidProofEvidence {
                    reason: format!("{:?} artifact has an empty label", artifact.kind),
                });
            }
        }

        check_transcript_digest_consistency(&self.metadata, &self.artifacts)?;
        check_replay_log_digest_consistency(&self.metadata, &self.artifacts)?;
        check_normalized_input_digest_consistency(&self.metadata, &self.artifacts)?;

        Ok(())
    }
}

fn check_transcript_digest_consistency(
    metadata: &FullProofEvidenceMetadata,
    artifacts: &[FullVerificationArtifact],
) -> Result<(), FullVerificationError> {
    let transcript_artifact_digests =
        artifact_digests(artifacts, FullVerificationArtifactKind::SolverTranscript);

    for hash in &metadata.transcript_hashes {
        if !transcript_artifact_digests.contains(&hash) {
            return Err(FullVerificationError::InvalidProofEvidence {
                reason: format!(
                    "metadata transcript hash {}:{} has no matching solver transcript artifact",
                    hash.algorithm, hash.hex
                ),
            });
        }
    }

    for digest in transcript_artifact_digests {
        if !metadata.transcript_hashes.iter().any(|hash| hash == digest) {
            return Err(FullVerificationError::InvalidProofEvidence {
                reason: format!(
                    "solver transcript artifact digest {}:{} is absent from proof metadata",
                    digest.algorithm, digest.hex
                ),
            });
        }
    }

    Ok(())
}

fn check_replay_log_digest_consistency(
    metadata: &FullProofEvidenceMetadata,
    artifacts: &[FullVerificationArtifact],
) -> Result<(), FullVerificationError> {
    let replay_artifact_digests =
        artifact_digests(artifacts, FullVerificationArtifactKind::ReplayLog);

    for hash in &metadata.replay_hashes {
        if !replay_artifact_digests.contains(&hash) {
            return Err(FullVerificationError::InvalidProofEvidence {
                reason: format!(
                    "metadata replay hash {}:{} has no matching replay log artifact",
                    hash.algorithm, hash.hex
                ),
            });
        }
    }

    for digest in replay_artifact_digests {
        if !metadata.replay_hashes.iter().any(|hash| hash == digest) {
            return Err(FullVerificationError::InvalidProofEvidence {
                reason: format!(
                    "replay log artifact digest {}:{} is absent from proof metadata",
                    digest.algorithm, digest.hex
                ),
            });
        }
    }

    Ok(())
}

fn check_normalized_input_digest_consistency(
    metadata: &FullProofEvidenceMetadata,
    artifacts: &[FullVerificationArtifact],
) -> Result<(), FullVerificationError> {
    let normalized_input_digests =
        artifact_digests(artifacts, FullVerificationArtifactKind::NormalizedInput);

    if let Some(hash) = &metadata.normalized_input_hash {
        if !normalized_input_digests.is_empty() && !normalized_input_digests.contains(&hash) {
            return Err(FullVerificationError::InvalidProofEvidence {
                reason: format!(
                    "metadata normalized input hash {}:{} does not match a normalized input artifact",
                    hash.algorithm, hash.hex
                ),
            });
        }
    } else if let Some(digest) = normalized_input_digests.first() {
        return Err(FullVerificationError::InvalidProofEvidence {
            reason: format!(
                "normalized input artifact digest {}:{} is absent from proof metadata",
                digest.algorithm, digest.hex
            ),
        });
    }

    Ok(())
}

fn artifact_digests(
    artifacts: &[FullVerificationArtifact],
    kind: FullVerificationArtifactKind,
) -> Vec<&EvidenceHash> {
    artifacts
        .iter()
        .filter(|artifact| artifact.kind == kind)
        .filter_map(|artifact| artifact.digest.as_ref())
        .collect()
}

/// Proof kinds that are strong enough for full verification.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ChcPdrProofKind {
    /// The CHC query was proved unreachable/valid by an unbounded CHC engine.
    ChcValidity,

    /// A PDR-style inductive invariant proves the queried target unreachable.
    PdrInvariant,
}

/// Counterexample evidence from a CHC/PDR-family engine.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ChcPdrCounterexampleEvidence {
    /// Number of counterexample transition steps.
    pub step_count: usize,

    /// Optional engine summary.
    pub summary: Option<String>,

    /// Evidence artifacts available for diagnostics or publication.
    pub artifacts: Vec<FullVerificationArtifact>,
}

impl ChcPdrCounterexampleEvidence {
    /// Creates counterexample evidence with a transition-step count.
    #[must_use]
    pub fn new(step_count: usize) -> Self {
        Self { step_count, summary: None, artifacts: Vec::new() }
    }

    /// Sets a human-readable summary.
    #[must_use]
    pub fn with_summary(mut self, summary: impl Into<String>) -> Self {
        self.summary = Some(summary.into());
        self
    }

    /// Attaches a diagnostic/publication artifact.
    #[must_use]
    pub fn with_artifact(mut self, artifact: FullVerificationArtifact) -> Self {
        self.artifacts.push(artifact);
        self
    }
}

/// Evidence artifact descriptor for full-verification reports.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FullVerificationArtifact {
    /// Artifact kind.
    pub kind: FullVerificationArtifactKind,

    /// Stable artifact label or path supplied by the engine adapter.
    pub label: String,

    /// Optional digest of the artifact content.
    pub digest: Option<EvidenceHash>,
}

impl FullVerificationArtifact {
    /// Creates an evidence artifact descriptor.
    #[must_use]
    pub fn new(kind: FullVerificationArtifactKind, label: impl Into<String>) -> Self {
        Self { kind, label: label.into(), digest: None }
    }

    /// Creates a solver transcript artifact and records its digest.
    #[must_use]
    pub fn solver_transcript(label: impl Into<String>, digest: EvidenceHash) -> Self {
        Self {
            kind: FullVerificationArtifactKind::SolverTranscript,
            label: label.into(),
            digest: Some(digest),
        }
    }

    /// Creates a replay log artifact and records its digest.
    #[must_use]
    pub fn replay_log(label: impl Into<String>, digest: EvidenceHash) -> Self {
        Self {
            kind: FullVerificationArtifactKind::ReplayLog,
            label: label.into(),
            digest: Some(digest),
        }
    }

    /// Attaches a digest to the artifact descriptor.
    #[must_use]
    pub fn with_digest(mut self, digest: EvidenceHash) -> Self {
        self.digest = Some(digest);
        self
    }
}

/// Proof evidence metadata carried by proof-producing full-verifier reports.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct FullProofEvidenceMetadata {
    /// Engine or adapter label that produced the proof evidence.
    pub producer: Option<String>,

    /// Digest of the normalized CHC/PDR input, when available.
    pub normalized_input_hash: Option<EvidenceHash>,

    /// Digests of solver transcripts that support the verdict.
    pub transcript_hashes: Vec<EvidenceHash>,

    /// Digests of replay/checking logs that validate the proof evidence.
    pub replay_hashes: Vec<EvidenceHash>,
}

impl FullProofEvidenceMetadata {
    /// Sets the producer label.
    #[must_use]
    pub fn with_producer(mut self, producer: impl Into<String>) -> Self {
        self.producer = Some(producer.into());
        self
    }

    /// Sets the normalized input digest.
    #[must_use]
    pub fn with_normalized_input_hash(mut self, hash: EvidenceHash) -> Self {
        self.normalized_input_hash = Some(hash);
        self
    }

    /// Adds a solver transcript digest.
    #[must_use]
    pub fn with_transcript_hash(mut self, hash: EvidenceHash) -> Self {
        self.transcript_hashes.push(hash);
        self
    }

    /// Adds a proof replay log digest.
    #[must_use]
    pub fn with_replay_hash(mut self, hash: EvidenceHash) -> Self {
        self.replay_hashes.push(hash);
        self
    }
}

/// Stable evidence digest descriptor.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct EvidenceHash {
    /// Digest algorithm.
    pub algorithm: EvidenceHashAlgorithm,

    /// Lowercase hexadecimal digest.
    pub hex: String,
}

impl EvidenceHash {
    /// Creates a validated SHA-256 evidence digest from lowercase or uppercase hex.
    pub fn sha256(hex: impl Into<String>) -> Result<Self, EvidenceHashError> {
        let hex = hex.into().to_ascii_lowercase();
        if hex.len() != 64 {
            return Err(EvidenceHashError::InvalidLength {
                algorithm: EvidenceHashAlgorithm::Sha256,
                expected: 64,
                actual: hex.len(),
            });
        }
        if !hex.bytes().all(|byte| byte.is_ascii_hexdigit()) {
            return Err(EvidenceHashError::InvalidHex { algorithm: EvidenceHashAlgorithm::Sha256 });
        }

        Ok(Self { algorithm: EvidenceHashAlgorithm::Sha256, hex })
    }
}

/// Invalid evidence digest metadata.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum EvidenceHashError {
    /// The hex digest length did not match the algorithm.
    InvalidLength {
        /// Digest algorithm.
        algorithm: EvidenceHashAlgorithm,
        /// Expected hex length.
        expected: usize,
        /// Actual hex length.
        actual: usize,
    },

    /// The digest contained a non-hex character.
    InvalidHex {
        /// Digest algorithm.
        algorithm: EvidenceHashAlgorithm,
    },
}

impl std::fmt::Display for EvidenceHashError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            EvidenceHashError::InvalidLength { algorithm, expected, actual } => {
                write!(
                    f,
                    "invalid {algorithm} evidence hash length: expected {expected}, got {actual}"
                )
            }
            EvidenceHashError::InvalidHex { algorithm } => {
                write!(f, "invalid {algorithm} evidence hash: digest must be hexadecimal")
            }
        }
    }
}

impl std::error::Error for EvidenceHashError {}

/// Evidence digest algorithms accepted by the full-verifier API.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum EvidenceHashAlgorithm {
    /// SHA-256 digest over a transcript or normalized proof artifact.
    Sha256,
}

impl std::fmt::Display for EvidenceHashAlgorithm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            EvidenceHashAlgorithm::Sha256 => f.write_str("SHA-256"),
        }
    }
}

/// Artifact kinds emitted by full-verification engines.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FullVerificationArtifactKind {
    /// Normalized CHC/PDR engine input.
    NormalizedInput,

    /// Solver transcript.
    SolverTranscript,

    /// PDR invariant model.
    PdrInvariantModel,

    /// Proof replay/checking log.
    ReplayLog,

    /// Counterexample trace.
    CounterexampleTrace,

    /// Unknown/timeout diagnostic trace.
    DiagnosticTrace,
}

/// A full-verification report.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FullVerificationReport {
    /// Engine family that produced the verdict.
    pub engine: FullVerificationEngine,

    /// Full-verification verdict.
    pub verdict: FullVerificationVerdict,
}

impl FullVerificationReport {
    /// Creates a report.
    #[must_use]
    pub const fn new(engine: FullVerificationEngine, verdict: FullVerificationVerdict) -> Self {
        Self { engine, verdict }
    }

    /// Creates a diagnostic-only report.
    #[must_use]
    pub const fn diagnostic_only(diagnostic: FullVerificationDiagnostic) -> Self {
        Self {
            engine: FullVerificationEngine::DiagnosticOnly,
            verdict: FullVerificationVerdict::DiagnosticOnly { diagnostic },
        }
    }
}

impl From<ChcPdrReport> for FullVerificationReport {
    fn from(report: ChcPdrReport) -> Self {
        let verdict = match report.verdict {
            ChcPdrVerdict::Proved(evidence) => {
                FullVerificationVerdict::Proved { evidence: FullProofEvidence::ChcPdr(evidence) }
            }
            ChcPdrVerdict::Counterexample(evidence) => {
                let summary = evidence.summary.or_else(|| {
                    Some(format!("CHC/PDR counterexample with {} step(s)", evidence.step_count))
                });
                FullVerificationVerdict::Counterexample { summary }
            }
            ChcPdrVerdict::Unknown(reason) => FullVerificationVerdict::Unknown { reason },
        };

        Self { engine: FullVerificationEngine::ChcPdr, verdict }
    }
}

/// Verdicts admitted by the full-verifier API.
#[derive(Debug, Clone, PartialEq, Eq)]
#[allow(clippy::large_enum_variant)]
pub enum FullVerificationVerdict {
    /// A trusted injected engine reports the target unreachable.
    ///
    /// This report is not certified publication authority.
    Proved { evidence: FullProofEvidence },

    /// The target is reachable.
    Counterexample { summary: Option<String> },

    /// The engine could not decide the query.
    Unknown { reason: UnknownReason },

    /// Evidence was useful diagnostically but is not a full proof.
    DiagnosticOnly { diagnostic: FullVerificationDiagnostic },
}

/// Evidence reported by the legacy trusted-engine full-verifier API.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FullProofEvidence {
    /// Proof-grade evidence from an unbounded CHC/PDR-family engine.
    ChcPdr(ChcPdrProofEvidence),
}

/// Diagnostic evidence that the full-verifier API intentionally does not treat as proof.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FullVerificationDiagnostic {
    /// Diagnostic classification.
    pub kind: FullVerificationDiagnosticKind,

    /// Problem shape that produced the diagnostic.
    pub problem: FullVerificationProblemKind,

    /// Human-readable reason.
    pub summary: String,

    /// Diagnostic artifacts.
    pub artifacts: Vec<FullVerificationArtifact>,
}

impl FullVerificationDiagnostic {
    /// Creates a diagnostic-only evidence record.
    #[must_use]
    pub fn new(
        kind: FullVerificationDiagnosticKind,
        problem: FullVerificationProblemKind,
        summary: impl Into<String>,
    ) -> Self {
        Self { kind, problem, summary: summary.into(), artifacts: Vec::new() }
    }

    /// Attaches a diagnostic artifact.
    #[must_use]
    pub fn with_artifact(mut self, artifact: FullVerificationArtifact) -> Self {
        self.artifacts.push(artifact);
        self
    }
}

/// Diagnostic-only classifications.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FullVerificationDiagnosticKind {
    /// BMC reported bounded success, which is not an unbounded proof.
    BmcSuccessDemoted,
}

/// Reasons for an inconclusive full-verification verdict.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UnknownReason {
    /// Solver returned unknown.
    SolverReturnedUnknown,
    /// Solver exhausted its budget.
    Timeout,
    /// Engine intentionally demoted a suspect proof or counterexample.
    Demoted(String),
}

/// Fail-closed full-verification API errors.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FullVerificationError {
    /// The submitted problem shape cannot produce a full proof.
    UnsupportedProblem {
        /// Rejected problem kind.
        problem: FullVerificationProblemKind,
        /// Rejection reason.
        reason: String,
    },

    /// Required production wiring does not exist yet.
    NotYetWired {
        /// Missing component.
        component: &'static str,
        /// Context for the missing wiring.
        reason: String,
        /// Precise adapter gaps to close before this path may return proofs.
        gaps: &'static [ChcPdrAdapterGap],
    },

    /// A proof-producing CHC/PDR report was internally inconsistent.
    InvalidProofEvidence {
        /// Rejection reason.
        reason: String,
    },
}

impl std::fmt::Display for FullVerificationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FullVerificationError::UnsupportedProblem { problem, reason } => {
                write!(f, "unsupported full-verification problem {problem}: {reason}")
            }
            FullVerificationError::NotYetWired { component, reason, gaps } => {
                write!(f, "{component} is not yet wired: {reason}")?;
                if !gaps.is_empty() {
                    write!(f, " (missing: ")?;
                    for (idx, gap) in gaps.iter().enumerate() {
                        if idx > 0 {
                            write!(f, "; ")?;
                        }
                        write!(f, "{gap}")?;
                    }
                    write!(f, ")")?;
                }
                Ok(())
            }
            FullVerificationError::InvalidProofEvidence { reason } => {
                write!(f, "invalid CHC/PDR proof evidence: {reason}")
            }
        }
    }
}

impl std::error::Error for FullVerificationError {}

#[cfg(test)]
mod tests {
    use std::cell::Cell;
    use std::rc::Rc;

    use super::*;
    use crate::{RelationApp, RelationDecl, Rule};
    use ay_bindings::{Expr, Sort};

    #[test]
    fn default_verifier_returns_not_yet_wired_for_chc() {
        let err = NativeFullVerifier::new()
            .verify(FullVerificationRequest::chc(ChcVc::new()))
            .expect_err("default full verifier must fail closed");

        assert!(matches!(
            err,
            FullVerificationError::NotYetWired {
                component: "native CHC/PDR engine",
                gaps: MissingChcPdrEngine::ADAPTER_GAPS,
                ..
            }
        ));
        assert!(err.to_string().contains("session-free ay::chc native solver adapter"));
    }

    #[test]
    fn bmc_shaped_success_is_diagnostic_only_before_engine_is_called() {
        let calls = Rc::new(Cell::new(0));
        let engine = CountingEngine { calls: Rc::clone(&calls) };
        let verifier = NativeFullVerifier::with_chc_pdr_engine(engine);

        let report = verifier
            .verify(FullVerificationRequest::bmc(BmcVc::new()))
            .expect("BMC-shaped success is reported as diagnostic-only");

        assert_eq!(calls.get(), 0);
        assert_eq!(report.engine, FullVerificationEngine::DiagnosticOnly);
        assert_eq!(
            report.verdict,
            FullVerificationVerdict::DiagnosticOnly {
                diagnostic: FullVerificationDiagnostic::new(
                    FullVerificationDiagnosticKind::BmcSuccessDemoted,
                    FullVerificationProblemKind::Bmc,
                    "bounded model-checking success is diagnostic-only and cannot establish an \
                     unbounded full proof",
                ),
            }
        );
    }

    #[test]
    fn chc_request_delegates_to_chc_pdr_engine() {
        let calls = Rc::new(Cell::new(0));
        let engine = CountingEngine { calls: Rc::clone(&calls) };
        let verifier = NativeFullVerifier::with_chc_pdr_engine(engine);

        let report = verifier
            .verify(FullVerificationRequest::chc(minimal_unbounded_chc_vc()))
            .expect("CHC request should call the native engine");

        assert_eq!(calls.get(), 1);
        assert_eq!(report.engine, FullVerificationEngine::ChcPdr);
        assert_eq!(
            report.verdict,
            FullVerificationVerdict::Unknown { reason: UnknownReason::SolverReturnedUnknown }
        );
    }

    #[test]
    fn chc_pdr_proof_evidence_satisfies_full_verification() {
        let vc = minimal_unbounded_chc_vc();
        let stats = ChcPdrStats::from_vc(&vc);
        let transcript_hash = EvidenceHash::sha256(
            "70bbcad3a0a304ea235147560832e6777694afe59a5dba58cd3bcd4906578c54",
        )
        .expect("valid SHA-256 transcript hash");
        let replay_hash = EvidenceHash::sha256(
            "6ef5bbad67f4bb3c22273702ac65abf74e30cd6729e3b2719b203a5e1020bf5c",
        )
        .expect("valid SHA-256 replay hash");
        let metadata = FullProofEvidenceMetadata::default()
            .with_producer("unit-test-chc-pdr")
            .with_normalized_input_hash(
                EvidenceHash::sha256(
                    "da644b0a7e8937c10c5c3aabe4609716f5d695c8c1491ac814bbcf2392ec3868",
                )
                .expect("valid SHA-256 input hash"),
            )
            .with_transcript_hash(transcript_hash.clone())
            .with_replay_hash(replay_hash.clone());
        let evidence = ChcPdrProofEvidence::pdr_invariant(stats, 1)
            .with_metadata(metadata)
            .with_artifact(FullVerificationArtifact::solver_transcript(
                "minimal-unbounded-pdr-transcript",
                transcript_hash.clone(),
            ))
            .with_artifact(FullVerificationArtifact::replay_log(
                "minimal-unbounded-pdr-replay",
                replay_hash.clone(),
            ))
            .with_artifact(FullVerificationArtifact::new(
                FullVerificationArtifactKind::PdrInvariantModel,
                "loop(x) => x >= 0",
            ));
        let verifier =
            NativeFullVerifier::with_chc_pdr_engine(ProvingEngine { evidence: evidence.clone() });

        let report = verifier
            .verify(FullVerificationRequest::chc(vc))
            .expect("CHC/PDR proof evidence should satisfy full verification");

        assert_eq!(report.engine, FullVerificationEngine::ChcPdr);
        assert_eq!(stats, ChcPdrStats { relation_count: 2, clause_count: 3 });
        assert_eq!(
            evidence.metadata.transcript_hashes,
            vec![EvidenceHash {
                algorithm: EvidenceHashAlgorithm::Sha256,
                hex: transcript_hash.hex.clone(),
            }]
        );
        assert_eq!(
            evidence.metadata.replay_hashes,
            vec![EvidenceHash {
                algorithm: EvidenceHashAlgorithm::Sha256,
                hex: replay_hash.hex.clone(),
            }]
        );
        assert_eq!(
            report.verdict,
            FullVerificationVerdict::Proved { evidence: FullProofEvidence::ChcPdr(evidence) }
        );
    }

    #[test]
    fn proved_report_with_mismatched_stats_fails_closed() {
        let vc = minimal_unbounded_chc_vc();
        let report_stats = ChcPdrStats::from_vc(&vc);
        let evidence = ChcPdrProofEvidence::chc_validity(ChcPdrStats::default());
        let report = ChcPdrReport::new(ChcPdrVerdict::Proved(evidence), report_stats);
        let verifier = NativeFullVerifier::with_chc_pdr_engine(ReportEngine { report });

        let err = verifier
            .verify(FullVerificationRequest::chc(vc))
            .expect_err("mismatched proof statistics must not produce a full proof");

        assert!(matches!(err, FullVerificationError::InvalidProofEvidence { .. }));
        assert!(err.to_string().contains("do not match CHC/PDR report stats"));
    }

    #[test]
    fn pdr_proof_with_zero_invariants_fails_closed() {
        let vc = minimal_unbounded_chc_vc();
        let stats = ChcPdrStats::from_vc(&vc);
        let evidence = ChcPdrProofEvidence::pdr_invariant(stats, 0);
        let verifier = NativeFullVerifier::with_chc_pdr_engine(ReportEngine {
            report: ChcPdrReport::proved(evidence),
        });

        let err = verifier
            .verify(FullVerificationRequest::chc(vc))
            .expect_err("PDR proof evidence needs at least one invariant");

        assert!(matches!(err, FullVerificationError::InvalidProofEvidence { .. }));
        assert!(err.to_string().contains("zero invariant formulas"));
    }

    #[test]
    fn transcript_metadata_must_match_solver_transcript_artifacts() {
        let vc = minimal_unbounded_chc_vc();
        let stats = ChcPdrStats::from_vc(&vc);
        let metadata_hash = EvidenceHash::sha256(
            "70bbcad3a0a304ea235147560832e6777694afe59a5dba58cd3bcd4906578c54",
        )
        .expect("valid metadata transcript hash");
        let artifact_hash = EvidenceHash::sha256(
            "e0dc39d9c5f2eb3ea09252dc316205a76e012d6c3a5622b978012659f29a3c73",
        )
        .expect("valid artifact transcript hash");
        let evidence = ChcPdrProofEvidence::pdr_invariant(stats, 1)
            .with_transcript_hash(metadata_hash)
            .with_artifact(FullVerificationArtifact::solver_transcript(
                "mismatched-transcript",
                artifact_hash,
            ));
        let verifier = NativeFullVerifier::with_chc_pdr_engine(ReportEngine {
            report: ChcPdrReport::proved(evidence),
        });

        let err = verifier
            .verify(FullVerificationRequest::chc(vc))
            .expect_err("mismatched transcript digests must not produce a full proof");

        assert!(matches!(err, FullVerificationError::InvalidProofEvidence { .. }));
        assert!(err.to_string().contains("no matching solver transcript artifact"));
    }

    #[test]
    fn replay_metadata_must_match_replay_log_artifacts() {
        let vc = minimal_unbounded_chc_vc();
        let stats = ChcPdrStats::from_vc(&vc);
        let metadata_hash = EvidenceHash::sha256(
            "6ef5bbad67f4bb3c22273702ac65abf74e30cd6729e3b2719b203a5e1020bf5c",
        )
        .expect("valid metadata replay hash");
        let artifact_hash = EvidenceHash::sha256(
            "3c40bfb9af2713c0ec4c9e3a86c2f37239c252d69bbf545e4c401f4512fb10ad",
        )
        .expect("valid artifact replay hash");
        let evidence = ChcPdrProofEvidence::pdr_invariant(stats, 1)
            .with_replay_hash(metadata_hash)
            .with_artifact(FullVerificationArtifact::replay_log(
                "mismatched-replay",
                artifact_hash,
            ));
        let verifier = NativeFullVerifier::with_chc_pdr_engine(ReportEngine {
            report: ChcPdrReport::proved(evidence),
        });

        let err = verifier
            .verify(FullVerificationRequest::chc(vc))
            .expect_err("mismatched replay digests must not produce a full proof");

        assert!(matches!(err, FullVerificationError::InvalidProofEvidence { .. }));
        assert!(err.to_string().contains("no matching replay log artifact"));
    }

    #[test]
    fn sha256_evidence_hashes_validate_transcript_digests() {
        let hash = EvidenceHash::sha256(
            "E0DC39D9C5F2EB3EA09252DC316205A76E012D6C3A5622B978012659F29A3C73",
        )
        .expect("valid uppercase SHA-256 digest");

        assert_eq!(hash.algorithm, EvidenceHashAlgorithm::Sha256);
        assert_eq!(hash.hex, "e0dc39d9c5f2eb3ea09252dc316205a76e012d6c3a5622b978012659f29a3c73");
        assert!(matches!(
            EvidenceHash::sha256("not-a-sha256"),
            Err(EvidenceHashError::InvalidLength {
                algorithm: EvidenceHashAlgorithm::Sha256,
                expected: 64,
                actual: 12,
            })
        ));
    }

    fn minimal_unbounded_chc_vc() -> ChcVc {
        let mut vc = ChcVc::new();
        vc.add_relation(RelationDecl::new("loop", vec![Sort::int()]));
        vc.add_relation(RelationDecl::nullary("error"));
        vc.query = crate::ChcQuery::new().with_target("error");

        let x = vc.declare_var("x", Sort::int());
        let x_next = vc.declare_var("x_next", Sort::int());

        vc.add_rule(Rule::init(
            Expr::eq(x.clone(), Expr::int_const(0)),
            RelationApp::new("loop", vec![x.clone()]),
        ));
        vc.add_rule(Rule::transition(
            RelationApp::new("loop", vec![x.clone()]),
            None,
            Expr::eq(x_next.clone(), x.clone().int_add(Expr::int_const(1))),
            RelationApp::new("loop", vec![x_next]),
        ));
        vc.add_rule(Rule::new(
            crate::RuleBody::new(
                Some(RelationApp::new("loop", vec![x.clone()])),
                vec![x.int_lt(Expr::int_const(0))],
            ),
            RelationApp::nullary("error"),
        ));

        vc
    }

    #[derive(Debug)]
    struct CountingEngine {
        calls: Rc<Cell<usize>>,
    }

    impl ChcPdrEngine for CountingEngine {
        fn solve_chc_pdr(
            &self,
            _vc: &ChcVc,
            options: &FullVerificationOptions,
        ) -> ChcPdrEngineResult {
            self.calls.set(self.calls.get() + 1);
            assert_eq!(options.engine, FullVerificationEngine::ChcPdr);
            Ok(ChcPdrReport::unknown(ChcPdrStats::default(), UnknownReason::SolverReturnedUnknown))
        }
    }

    #[derive(Debug)]
    struct ProvingEngine {
        evidence: ChcPdrProofEvidence,
    }

    impl ChcPdrEngine for ProvingEngine {
        fn solve_chc_pdr(
            &self,
            _vc: &ChcVc,
            options: &FullVerificationOptions,
        ) -> ChcPdrEngineResult {
            assert_eq!(options.engine, FullVerificationEngine::ChcPdr);
            Ok(ChcPdrReport::proved(self.evidence.clone()))
        }
    }

    #[derive(Debug)]
    struct ReportEngine {
        report: ChcPdrReport,
    }

    impl ChcPdrEngine for ReportEngine {
        fn solve_chc_pdr(
            &self,
            _vc: &ChcVc,
            options: &FullVerificationOptions,
        ) -> ChcPdrEngineResult {
            assert_eq!(options.engine, FullVerificationEngine::ChcPdr);
            Ok(self.report.clone())
        }
    }
}
