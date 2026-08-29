// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Native driver facade for solving trust-mc verification artifacts.
//!
//! This module defines the public solve boundary for Pipeline v2 native
//! integration. It solves native SMT-LIB BMC payloads with the in-process AY
//! executor and keeps unsupported proof modes fail-closed.

#[cfg(feature = "native-trust-ir-bundle")]
use std::collections::BTreeSet;
use std::error::Error;
use std::fmt;
#[cfg(any(feature = "ay-chc-native", feature = "ay-direct"))]
use std::sync::mpsc;
#[cfg(any(feature = "ay-chc-native", feature = "ay-direct"))]
use std::thread;
use std::time::Duration;

use serde::de::{Error as _, SeqAccess, Visitor};
use serde::{Deserialize, Deserializer, Serialize};

const SMTLIB_BMC_PAYLOAD_VERSION: u32 = 1;
const SMTLIB_BMC_PAYLOAD_FORMAT: &str = "trust_mc.native.smtlib-bmc";
const DEFAULT_TYPED_CHC_TIMEOUT: Duration = Duration::from_secs(120);
const MAX_NATIVE_PROOF_ROLE_ARTIFACTS: usize = 8;
const MAX_NATIVE_PROOF_RESPONSE_ARTIFACTS: usize = 16;
const MAX_NATIVE_PROOF_DIAGNOSTICS: usize = 64;

fn deserialize_bounded_native_vec<'de, D, T, const MAX: usize>(
    deserializer: D,
    description: &'static str,
) -> Result<Vec<T>, D::Error>
where
    D: Deserializer<'de>,
    T: Deserialize<'de>,
{
    struct BoundedNativeVecVisitor<T, const MAX: usize> {
        description: &'static str,
        marker: std::marker::PhantomData<fn() -> T>,
    }

    impl<'de, T, const MAX: usize> Visitor<'de> for BoundedNativeVecVisitor<T, MAX>
    where
        T: Deserialize<'de>,
    {
        type Value = Vec<T>;

        fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(formatter, "at most {MAX} {}", self.description)
        }

        fn visit_seq<A>(self, mut sequence: A) -> Result<Self::Value, A::Error>
        where
            A: SeqAccess<'de>,
        {
            if sequence.size_hint().is_some_and(|size| size > MAX) {
                return Err(A::Error::custom(format_args!(
                    "{} exceeds the {MAX}-entry limit",
                    self.description
                )));
            }
            let mut values = Vec::with_capacity(sequence.size_hint().unwrap_or(0).min(MAX));
            while let Some(value) = sequence.next_element()? {
                if values.len() == MAX {
                    return Err(A::Error::custom(format_args!(
                        "{} exceeds the {MAX}-entry limit",
                        self.description
                    )));
                }
                values.push(value);
            }
            Ok(values)
        }
    }

    deserializer.deserialize_seq(BoundedNativeVecVisitor::<T, MAX> {
        description,
        marker: std::marker::PhantomData,
    })
}

fn deserialize_bounded_native_role_artifacts<'de, D>(
    deserializer: D,
) -> Result<Vec<NativeTypedProofArtifactRef>, D::Error>
where
    D: Deserializer<'de>,
{
    deserialize_bounded_native_vec::<_, _, MAX_NATIVE_PROOF_ROLE_ARTIFACTS>(
        deserializer,
        "native proof role artifacts",
    )
}

fn deserialize_bounded_native_response_artifacts<'de, D>(
    deserializer: D,
) -> Result<Vec<NativeTypedProofArtifactRef>, D::Error>
where
    D: Deserializer<'de>,
{
    deserialize_bounded_native_vec::<_, _, MAX_NATIVE_PROOF_RESPONSE_ARTIFACTS>(
        deserializer,
        "native proof response artifacts",
    )
}

fn deserialize_bounded_native_diagnostics<'de, D>(deserializer: D) -> Result<Vec<String>, D::Error>
where
    D: Deserializer<'de>,
{
    deserialize_bounded_native_vec::<_, _, MAX_NATIVE_PROOF_DIAGNOSTICS>(
        deserializer,
        "native proof diagnostics",
    )
}

// Trust: pub(crate) so the in-crate differential soundness oracle
// (`crate::soundness_oracle`) can reach the real `lower_obligation`.
#[cfg(feature = "ay-chc-native")]
pub(crate) mod bounded_unroll;
#[cfg(feature = "ay-chc-native")]
pub(crate) mod typed_chc_ay;

/// Result alias for native driver facade operations.
pub type NativeSolveResult<T> = Result<T, NativeSolveError>;

/// Kind of encoded verification condition accepted by the driver facade.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum NativeVcKind {
    /// Bounded model checking artifact.
    Bmc,
    /// Constrained Horn Clause artifact.
    Chc,
}

/// Proof mode recorded in native solver provenance.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
#[non_exhaustive]
pub enum NativeProofMode {
    /// Ordinary bounded model checking.
    #[default]
    Bmc,
    /// BMC over a finite acyclic transition system.
    ///
    /// This is complete only when the producer proved that the explored state
    /// graph is finite and acyclic.
    FiniteAcyclicBmc,
    /// Constrained Horn Clause solving.
    Chc,
    /// Property-directed reachability / IC3.
    PdrIc3,
}

impl NativeProofMode {
    /// Returns true when this mode is ordinary depth-bounded evidence.
    pub fn is_bounded(self) -> bool {
        matches!(self, Self::Bmc)
    }

    /// Returns true when BMC is complete because the state graph is finite and acyclic.
    pub fn is_finite_acyclic_bmc(self) -> bool {
        matches!(self, Self::FiniteAcyclicBmc)
    }
}

/// Provenance carried from encoding through solving.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct NativeProofProvenance {
    /// Proof mode used or requested.
    pub proof_mode: NativeProofMode,
    /// BMC depth for bounded and finite-acyclic BMC.
    pub bmc_depth: Option<u32>,
    /// Whether a producer proved that the transition system is finite and acyclic.
    pub finite_acyclic: bool,
    /// Name of the component that produced or solved the artifact.
    pub producer: String,
}

impl NativeProofProvenance {
    /// Create provenance for an ordinary bounded BMC solve.
    pub fn bmc(depth: u32) -> Self {
        Self {
            proof_mode: NativeProofMode::Bmc,
            bmc_depth: Some(depth),
            finite_acyclic: false,
            producer: String::from("trust-mc-driver-native"),
        }
    }

    /// Create provenance for exhaustive finite acyclic BMC.
    pub fn finite_acyclic_bmc(depth: u32) -> Self {
        Self {
            proof_mode: NativeProofMode::FiniteAcyclicBmc,
            bmc_depth: Some(depth),
            finite_acyclic: true,
            producer: String::from("trust-mc-driver-native"),
        }
    }

    /// Create provenance for CHC/PDR-style unbounded solving.
    pub fn unbounded(proof_mode: NativeProofMode) -> Self {
        Self {
            proof_mode,
            bmc_depth: None,
            finite_acyclic: false,
            producer: String::from("trust-mc-driver-native"),
        }
    }
}

/// Opaque encoded artifact accepted by the native solve facade.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct NativeEncodedArtifact {
    /// Stable identifier for the obligation being solved.
    pub obligation_id: String,
    /// Display name of the function or harness.
    pub function_name: String,
    /// Artifact kind.
    pub kind: NativeVcKind,
    /// Opaque artifact payload.
    pub payload: Vec<u8>,
    /// Encoding provenance.
    pub provenance: NativeProofProvenance,
}

impl NativeEncodedArtifact {
    /// Construct a new opaque native artifact.
    pub fn new(
        obligation_id: impl Into<String>,
        function_name: impl Into<String>,
        kind: NativeVcKind,
        payload: Vec<u8>,
        provenance: NativeProofProvenance,
    ) -> Self {
        Self {
            obligation_id: obligation_id.into(),
            function_name: function_name.into(),
            kind,
            payload,
            provenance,
        }
    }
}

/// Request to solve one native trust-mc artifact.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct NativeSolveRequest {
    /// Artifact to solve.
    pub artifact: NativeEncodedArtifact,
    /// Optional wall-clock timeout for the solve.
    pub timeout: Option<Duration>,
    /// Whether a proof certificate should be produced when supported.
    pub produce_proof_certificate: bool,
}

impl NativeSolveRequest {
    /// Construct a native solve request.
    pub fn new(artifact: NativeEncodedArtifact) -> Self {
        Self { artifact, timeout: None, produce_proof_certificate: false }
    }

    /// Set a wall-clock timeout.
    pub fn with_timeout(mut self, timeout: Duration) -> Self {
        self.timeout = Some(timeout);
        self
    }

    /// Request proof-certificate production.
    pub fn with_proof_certificate(mut self, produce: bool) -> Self {
        self.produce_proof_certificate = produce;
        self
    }
}

/// Native solver verdict.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum NativeSolverVerdict {
    /// The property was proved.
    Proved,
    /// The property was refuted.
    Failed,
    /// The solver could not conclude.
    Unknown { reason: String },
    /// The solve exceeded its timeout.
    Timeout,
}

/// Successful native solve response.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct NativeSolvedArtifact {
    /// Obligation identifier copied from the request artifact.
    pub obligation_id: String,
    /// Solver verdict.
    pub verdict: NativeSolverVerdict,
    /// Final proof provenance.
    pub provenance: NativeProofProvenance,
    /// Optional proof certificate bytes.
    pub proof_certificate: Option<Vec<u8>>,
    /// Diagnostic messages captured during solving.
    pub diagnostics: Vec<String>,
}

/// Typed route selected for a MIR-derived CHC/PDR solve.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum TypedChcPdrRoute {
    /// The typed query target has no deriving Horn rule.
    TriviallySafe,
    /// Route through the native PDR proof engine.
    PdrProof,
}

/// Canonical normalized input derived from one typed CHC/PDR obligation.
///
/// The route is selected by the driver from the validated obligation.  The
/// normalized input and both hashes are the exact values consumed by native
/// full verification; callers can therefore bind a returned proof to the
/// pre-solve request without trusting proof- or cache-derived bytes.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct NativeTypedChcPdrNormalizedInput {
    /// Route selected from the typed obligation shape.
    pub route: TypedChcPdrRoute,
    /// Canonical input passed to the selected proof route.
    pub normalized_input: String,
    /// SHA-256 digest of `normalized_input.as_bytes()`.
    pub normalized_input_hash: trust_mc_core::EvidenceHash,
    /// SHA-256 digest of the versioned typed-obligation identity envelope.
    pub obligation_set_hash: trust_mc_core::EvidenceHash,
}

struct PreparedTypedChcPdrInput {
    normalized: NativeTypedChcPdrNormalizedInput,
    #[cfg(feature = "ay-chc-native")]
    problem: Option<ay_chc::ChcProblem>,
    /// Exactness accounting of the `ChcVc` -> `ay_chc::ChcProblem` lowering
    /// that produced `problem`; `None` on the trivially-safe route (nothing
    /// was lowered). Consumed by refutation-witness minting.
    #[cfg(feature = "ay-chc-native")]
    lowering: Option<typed_chc_ay::TypedChcLoweringAccounting>,
}

/// Non-serializable authority minted only by an exact in-process CHC-validity
/// derivation. This type is intentionally not `Clone`: cloning the surrounding
/// public response drops authority instead of duplicating a capability.
#[derive(Debug, PartialEq, Eq)]
struct PrivateChcValiditySeal {
    derivation: PrivateChcValidityDerivation,
    binding: trust_mc_core::EvidenceHash,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PrivateChcValidityDerivation {
    #[cfg(feature = "native-trust-ir-bundle")]
    NativeBundleStructural,
    #[cfg(feature = "native-trust-ir-bundle")]
    NativeBundleAcyclicDirectSmt,
    ExactDirectStructuralReplay,
    ExactDirectAcyclicDirectSmtReplay,
}

impl PrivateChcValidityDerivation {
    const fn label(self) -> &'static str {
        match self {
            #[cfg(feature = "native-trust-ir-bundle")]
            Self::NativeBundleStructural => "native-bundle-structural",
            #[cfg(feature = "native-trust-ir-bundle")]
            Self::NativeBundleAcyclicDirectSmt => "native-bundle-acyclic-direct-smt",
            Self::ExactDirectStructuralReplay => "exact-direct-structural-replay",
            Self::ExactDirectAcyclicDirectSmtReplay => "exact-direct-acyclic-direct-smt-replay",
        }
    }

    const fn authority_domain(self) -> &'static str {
        match self {
            #[cfg(feature = "native-trust-ir-bundle")]
            Self::NativeBundleStructural | Self::NativeBundleAcyclicDirectSmt => {
                "trusted-native-bundle-translation-plus-exact-derivation-not-serializable"
            }
            Self::ExactDirectStructuralReplay | Self::ExactDirectAcyclicDirectSmtReplay => {
                "fresh-exact-typed-obligation-plus-independent-validity-replay-not-serializable"
            }
        }
    }
}

/// Exact replay inputs retained after a fresh consumer re-lowered and checked a
/// PDR invariant. Every field is derived independently from the live exact typed
/// obligation, never from a serialized transport record.
#[derive(Debug, PartialEq, Eq)]
struct PrivatePdrInvariantReplayBinding {
    exact_obligation_set_hash: trust_mc_core::EvidenceHash,
    fresh_problem_hash: trust_mc_core::EvidenceHash,
    typed_problem_digest: trust_mc_core::EvidenceHash,
    invariant_model_digest: trust_mc_core::EvidenceHash,
    invariant_model_byte_len: u64,
}

/// Non-serializable authority minted only after strict parsing and full clause
/// validation of the unique retained invariant against a freshly lowered CHC
/// problem. Like the CHC-validity seal, this type deliberately is not `Clone`.
#[derive(Debug, PartialEq, Eq)]
struct PrivatePdrInvariantSeal {
    replay: PrivatePdrInvariantReplayBinding,
    binding: trust_mc_core::EvidenceHash,
}

#[derive(Debug, PartialEq, Eq)]
enum PrivateNativeProofSeal {
    ChcValidity(PrivateChcValiditySeal),
    PdrInvariant(Box<PrivatePdrInvariantSeal>),
}

/// Full-verification response for a typed MIR-derived CHC/PDR obligation.
#[derive(Debug, PartialEq, Eq)]
#[non_exhaustive]
pub struct TypedChcPdrFullVerification {
    /// Route selected from the typed obligation shape.
    pub route: TypedChcPdrRoute,
    /// Deterministic cache key covering verifier/solver identity and typed problem inputs.
    pub cache_key: trust_mc_core::FullVerificationCacheKey,
    /// Deterministic artifact directory selected from the cache key.
    pub artifact_directory: String,
    /// Typed solver outcome.
    pub outcome: trust_mc_core::ChcPdrSolveOutcome,
    /// Full-verification evidence verdict.
    pub verdict: trust_mc_core::FullVerificationVerdict,
    /// In-process authority is intentionally private and non-serializable.
    private_native_proof_seal: Option<PrivateNativeProofSeal>,
}

/// Public response cloning is diagnostic-only. The private proof capability is
/// affine: callers that need authority must retain the original live response.
impl Clone for TypedChcPdrFullVerification {
    fn clone(&self) -> Self {
        Self {
            route: self.route,
            cache_key: self.cache_key.clone(),
            artifact_directory: self.artifact_directory.clone(),
            outcome: self.outcome.clone(),
            verdict: self.verdict.clone(),
            private_native_proof_seal: None,
        }
    }
}

/// Stable proof status exported for typed native CHC/PDR transport.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum NativeTypedProofStatus {
    /// The live producer reported an opaque-authorized proof. This serialized
    /// tag alone is diagnostic and grants no authority.
    Proved,
    /// The obligation was refuted by a verified counterexample.
    Refuted,
    /// The backend could not decide the obligation.
    Unknown,
}

/// Proof strength exported for typed native CHC/PDR transport.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum NativeTypedProofStrength {
    /// Unbounded CHC validity evidence proves the query unreachable.
    ChcValidity,
    /// PDR/IC3 inductive invariant evidence proves the query unreachable.
    PdrInvariant,
}

/// Digest-backed artifact reference exported for typed native CHC/PDR transport.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub struct NativeTypedProofArtifactRef {
    /// Artifact kind as emitted by trust-mc proof evidence.
    pub kind: trust_mc_core::FullVerificationArtifactKind,
    /// Stable artifact URI/label.
    pub uri: String,
    /// Content digest, when available.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub digest: Option<trust_mc_core::EvidenceHash>,
    /// Artifact byte length, when trust-mc hashed concrete bytes directly.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub byte_len: Option<u64>,
    /// Exact bounded bytes and producer-authored proof relationships.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub materialization: Option<trust_mc_core::FullVerificationArtifactMaterialization>,
}

impl NativeTypedProofArtifactRef {
    /// Return exact bytes only when the transport descriptor still matches them.
    #[must_use]
    pub fn materialized_bytes(&self) -> Option<&[u8]> {
        let materialization = self.materialization.as_ref()?;
        if self.digest.as_ref()
            != Some(&trust_mc_core::EvidenceHash::sha256_bytes(materialization.bytes()))
            || self.byte_len != Some(materialization.byte_len())
        {
            return None;
        }
        Some(materialization.bytes())
    }

    /// Return the validated retained byte length.
    #[must_use]
    pub fn materialized_byte_len(&self) -> Option<u64> {
        self.materialized_bytes()?;
        self.materialization.as_ref().map(|materialization| materialization.byte_len())
    }

    /// Return the producer-authored content-addressed proof binding.
    #[must_use]
    pub fn proof_binding_id(&self) -> Option<&str> {
        self.materialized_bytes()?;
        self.materialization
            .as_ref()?
            .proof_binding_id()
            .map(trust_mc_core::ProofArtifactBindingId::as_str)
    }

    /// Return typed references to exact artifacts consumed or checked.
    #[must_use]
    pub fn referenced_artifacts(&self) -> &[trust_mc_core::FullVerificationArtifactReference] {
        if self.materialized_bytes().is_none() {
            return &[];
        }
        self.materialization
            .as_ref()
            .map_or(&[], |materialization| materialization.referenced_artifacts())
    }
}

/// Structured diagnostic snapshot of a native proof transport.
///
/// This serialized record is never a proof capability: callers can forge or
/// reconstruct every field. Authority is carried only by the opaque,
/// non-serializable [`AuthorizedNativeTypedChcPdrProof`] returned from a live
/// sealed verification response.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub struct NativeTypedChcPdrProofTransport {
    /// Transport schema version.
    pub schema_version: u32,
    /// Producing verification suite, copied from native trust_ir metadata.
    pub suite: String,
    /// trust-mc backend route that produced the evidence.
    pub backend: String,
    /// Native trust_ir request id.
    pub request_id: u32,
    /// Native trust_ir proof obligation id when the request binds exactly one proof.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub proof_id: Option<u32>,
    /// trust_mc-native obligation/proof id.
    pub native_id: String,
    /// Solver/proof status.
    pub proof_status: NativeTypedProofStatus,
    /// Diagnostic strength label copied from the live opaque-authorized result.
    pub proof_strength: NativeTypedProofStrength,
    /// Solver transcript artifacts with digest-backed URIs.
    #[serde(default, deserialize_with = "deserialize_bounded_native_role_artifacts")]
    pub solver_artifacts: Vec<NativeTypedProofArtifactRef>,
    /// Replay artifacts with digest-backed URIs.
    #[serde(deserialize_with = "deserialize_bounded_native_role_artifacts")]
    pub replay_artifacts: Vec<NativeTypedProofArtifactRef>,
    /// Proof-check artifacts with digest-backed URIs.
    #[serde(deserialize_with = "deserialize_bounded_native_role_artifacts")]
    pub check_artifacts: Vec<NativeTypedProofArtifactRef>,
    /// All response artifacts emitted for this proof, including typed problems
    /// and invariant/counterexample artifacts.
    #[serde(
        default,
        skip_serializing_if = "Vec::is_empty",
        deserialize_with = "deserialize_bounded_native_response_artifacts"
    )]
    pub response_artifacts: Vec<NativeTypedProofArtifactRef>,
    /// Replay/check status attached to the digest-backed proof artifacts.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub replay_check_status: Option<trust_mc_core::ProofReplayCheckStatus>,
    /// Typed solver diagnostics associated with the solve.
    #[serde(deserialize_with = "deserialize_bounded_native_diagnostics")]
    pub diagnostics: Vec<String>,
}

impl NativeTypedChcPdrProofTransport {
    pub const SCHEMA_VERSION: u32 = 1;
}

/// Opaque borrowed authority for one exact typed CHC/PDR proof.
///
/// Fields are private and this type is not serializable. It can be constructed
/// only after the verification's private seal has been recomputed successfully:
/// either at the validated native-bundle boundary or after a fresh exact
/// CHC-validity/PDR consumer replay. It proves the exact typed obligation, not an
/// external source program; a compiler consumer must retain its own private
/// source-to-obligation binding before promoting a source result.
#[derive(Debug)]
#[non_exhaustive]
pub struct AuthorizedNativeTypedChcPdrProof<'a> {
    verification: &'a TypedChcPdrFullVerification,
    candidate: trust_mc_core::ValidatedChcPdrCandidateEvidence<'a>,
}

impl AuthorizedNativeTypedChcPdrProof<'_> {
    /// Return the structurally validated public candidate bound by this authority.
    ///
    /// The candidate alone remains non-authoritative; retain this opaque wrapper
    /// across the private consumer decision.
    #[must_use]
    pub fn candidate(&self) -> trust_mc_core::ValidatedChcPdrCandidateEvidence<'_> {
        self.candidate
    }

    /// Produce a serializable diagnostic snapshot from this live authority.
    ///
    /// Deserializing the snapshot does not reconstruct this wrapper or its seal.
    #[must_use]
    pub fn transport_record(&self) -> NativeTypedChcPdrProofTransport {
        let metadata = self
            .candidate
            .native_metadata
            .expect("validated native typed CHC/PDR candidate always carries metadata");
        NativeTypedChcPdrProofTransport {
            schema_version: NativeTypedChcPdrProofTransport::SCHEMA_VERSION,
            suite: metadata.producer.clone(),
            backend: native_typed_backend_label(
                self.verification.route,
                &metadata.verification_mode,
            ),
            request_id: metadata.native_request_id,
            proof_id: single_native_proof_id(&metadata.proof_obligation_ids),
            native_id: self.candidate.proof.obligation.obligation_id.clone(),
            proof_status: NativeTypedProofStatus::Proved,
            proof_strength: native_typed_proof_strength(self.candidate.proof_kind),
            solver_artifacts: native_typed_artifact_refs(
                self.candidate.proof,
                trust_mc_core::FullVerificationArtifactKind::SolverTranscript,
            ),
            replay_artifacts: native_typed_artifact_refs(
                self.candidate.proof,
                trust_mc_core::FullVerificationArtifactKind::ReplayLog,
            ),
            check_artifacts: native_typed_artifact_refs(
                self.candidate.proof,
                trust_mc_core::FullVerificationArtifactKind::CheckedProofReport,
            ),
            response_artifacts: native_typed_all_artifact_refs(self.candidate.proof),
            replay_check_status: self.candidate.proof.metadata.replay_check_status,
            diagnostics: self.verification.outcome.diagnostics.clone(),
        }
    }
}

impl TypedChcPdrFullVerification {
    /// Attach exact-module authority only at the fresh native-bundle translation boundary.
    ///
    /// The generic typed solver cannot call this: validity of a submitted CHC
    /// does not establish that the CHC completely represents its source program.
    #[cfg(feature = "native-trust-ir-bundle")]
    fn with_private_native_bundle_authority(
        mut self,
        translated: &trust_mc_trust_bmc::NativeTrustMcChcPdrObligation,
        options: &trust_mc_core::ChcPdrSolveOptions,
    ) -> Self {
        let Some(prepared) =
            private_exact_typed_prepared_input(&self, &translated.obligation, options)
        else {
            return self;
        };
        let Ok(candidate) = trust_mc_core::validated_native_typed_chc_pdr_candidate(&self.verdict)
        else {
            return self;
        };
        self.private_native_proof_seal = match candidate.proof_kind {
            trust_mc_core::ChcPdrProofKind::ChcValidity => private_native_bundle_derivation(&self)
                .and_then(|derivation| {
                    private_chc_validity_binding(&self, derivation).map(|binding| {
                        PrivateNativeProofSeal::ChcValidity(PrivateChcValiditySeal {
                            derivation,
                            binding,
                        })
                    })
                }),
            trust_mc_core::ChcPdrProofKind::PdrInvariant => {
                // A translated whole-function TrustIr CHC is N:1 with respect
                // to public obligations. Freshly validating its invariant proves
                // that whole CHC, but cannot identify which source row is a
                // member of the error/query derivation. Keep bundle PDR evidence
                // diagnostic-only until translation emits an exact rederived
                // public-obligation -> instruction/error-rule membership receipt.
                let _ = prepared;
                None
            }
        };
        self
    }

    /// Attach CHC-level PDR authority after a fresh independent replay of the
    /// exact submitted typed obligation.
    ///
    /// This does not establish that the CHC represents a source program. The
    /// compiler adapter must retain its own private source-to-obligation binding
    /// before promoting a source-level result.
    #[cfg(feature = "ay-chc-native")]
    fn with_private_exact_typed_replay_authority(
        mut self,
        obligation: &trust_mc_core::MirChcPdrObligation,
        options: &trust_mc_core::ChcPdrSolveOptions,
    ) -> Self {
        let Some(prepared) = private_exact_typed_prepared_input(&self, obligation, options) else {
            return self;
        };
        let Ok(candidate) = trust_mc_core::validated_native_typed_chc_pdr_candidate(&self.verdict)
        else {
            return self;
        };
        self.private_native_proof_seal = match candidate.proof_kind {
            trust_mc_core::ChcPdrProofKind::ChcValidity => {
                private_exact_chc_validity_replay_seal(&self, prepared, options)
                    .map(PrivateNativeProofSeal::ChcValidity)
            }
            trust_mc_core::ChcPdrProofKind::PdrInvariant => {
                private_pdr_invariant_replay_seal(&self, prepared, options)
                    .map(Box::new)
                    .map(PrivateNativeProofSeal::PdrInvariant)
            }
        };
        self
    }

    /// Validate the non-serializable authority and return its bound candidate.
    fn privately_authorized_native_candidate(
        &self,
    ) -> NativeSolveResult<trust_mc_core::ValidatedChcPdrCandidateEvidence<'_>> {
        let candidate = trust_mc_core::validated_native_typed_chc_pdr_candidate(&self.verdict)
            .map_err(|rejection| NativeSolveError::ProofGradeRejected { rejection })?;
        let Some(seal) = &self.private_native_proof_seal else {
            return Err(private_native_proof_rejection(
                "missing private in-process native typed CHC/PDR proof authority",
            ));
        };
        let binding_matches = match (candidate.proof_kind, seal) {
            (
                trust_mc_core::ChcPdrProofKind::ChcValidity,
                PrivateNativeProofSeal::ChcValidity(seal),
            ) => private_chc_validity_binding(self, seal.derivation)
                .is_some_and(|binding| binding == seal.binding),
            (
                trust_mc_core::ChcPdrProofKind::PdrInvariant,
                PrivateNativeProofSeal::PdrInvariant(seal),
            ) => private_pdr_invariant_binding(self, &seal.replay)
                .is_some_and(|binding| binding == seal.binding),
            _ => false,
        };
        if !binding_matches {
            return Err(private_native_proof_rejection(
                "private native typed CHC/PDR proof authority no longer matches the verification response",
            ));
        }
        Ok(candidate)
    }

    /// Borrow opaque, non-serializable exact-module authority from this live response.
    pub fn authorized_native_proof(
        &self,
    ) -> NativeSolveResult<AuthorizedNativeTypedChcPdrProof<'_>> {
        let candidate = self.privately_authorized_native_candidate()?;
        Ok(AuthorizedNativeTypedChcPdrProof { verification: self, candidate })
    }

    /// Snapshot privately authorized native typed CHC/PDR evidence for diagnostics.
    ///
    /// Public candidate bytes never grant authority. This succeeds only for the
    /// live response returned by an exact in-process structural/exhaustive
    /// derivation or a fresh independently replayed PDR invariant, after
    /// recomputing its mutation-bound private seal.
    /// The returned record is never a capability; only the live borrowed
    /// [`AuthorizedNativeTypedChcPdrProof`] carries authority. Deserialized
    /// caller-provided records remain diagnostic input.
    pub fn native_proof_transport_record(
        &self,
    ) -> NativeSolveResult<NativeTypedChcPdrProofTransport> {
        Ok(self.authorized_native_proof()?.transport_record())
    }
}

fn private_native_proof_rejection(reason: &str) -> NativeSolveError {
    NativeSolveError::ProofGradeRejected {
        rejection: trust_mc_core::ProofEvidenceRejection {
            problem_kind: Some(trust_mc_core::FullVerificationProblemKind::ChcPdr),
            reasons: vec![reason.to_string()],
        },
    }
}

fn private_chc_validity_binding(
    verification: &TypedChcPdrFullVerification,
    derivation: PrivateChcValidityDerivation,
) -> Option<trust_mc_core::EvidenceHash> {
    let candidate =
        trust_mc_core::validated_native_typed_chc_pdr_candidate(&verification.verdict).ok()?;
    if candidate.proof_kind != trust_mc_core::ChcPdrProofKind::ChcValidity
        || candidate.proof.metadata.cache_key.as_ref() != Some(&verification.cache_key.key)
        || candidate.proof.obligation.normalized_input_hash
            != verification.cache_key.parts.normalized_input_hash
        || verification.cache_key.validate().is_err()
        || verification.artifact_directory != typed_artifact_directory(&verification.cache_key)
        || candidate.proof.obligation.obligation_id != verification.outcome.obligation_id
        || candidate.proof.stats != verification.outcome.stats
    {
        return None;
    }
    let trust_mc_core::ChcPdrSolveStatus::Unknown { reason } = &verification.outcome.status else {
        return None;
    };
    if reason != trust_mc_core::CHC_VALIDITY_FRESH_CONSUMER_REPLAY_REQUIRED {
        return None;
    }

    let mut typed_problem_artifacts = candidate.proof.artifacts.iter().filter(|artifact| {
        artifact.kind == trust_mc_core::FullVerificationArtifactKind::TypedChcProblem
    });
    let typed_problem = typed_problem_artifacts.next()?;
    if typed_problem_artifacts.next().is_some() || typed_problem.materialized_bytes().is_none() {
        return None;
    }
    let typed_problem_digest = typed_problem.digest.as_ref()?;

    let route = match verification.route {
        TypedChcPdrRoute::TriviallySafe => "trivially-safe",
        TypedChcPdrRoute::PdrProof => "pdr-proof",
    };
    let binding_envelope = serde_json::json!({
        "schema": "trust_mc.private-chc-validity-authority/v1",
        "domain": derivation.authority_domain(),
        "derivation": derivation.label(),
        "route": route,
        "cache_key": &verification.cache_key,
        "artifact_directory": &verification.artifact_directory,
        "outcome": {
            "obligation_id": &verification.outcome.obligation_id,
            "candidate_status": "unknown",
            "reason": reason,
            "stats": {
                "relation_count": verification.outcome.stats.relation_count,
                "clause_count": verification.outcome.stats.clause_count,
            },
            "diagnostics": &verification.outcome.diagnostics,
        },
        "typed_problem_digest": typed_problem_digest,
        "candidate_verdict": &verification.verdict,
    });
    serde_json::to_vec(&binding_envelope)
        .ok()
        .map(|bytes| trust_mc_core::EvidenceHash::sha256_bytes(&bytes))
}

#[cfg(feature = "native-trust-ir-bundle")]
fn private_native_bundle_derivation(
    verification: &TypedChcPdrFullVerification,
) -> Option<PrivateChcValidityDerivation> {
    match verification.route {
        TypedChcPdrRoute::TriviallySafe => {
            Some(PrivateChcValidityDerivation::NativeBundleStructural)
        }
        TypedChcPdrRoute::PdrProof => {
            Some(PrivateChcValidityDerivation::NativeBundleAcyclicDirectSmt)
        }
    }
}

#[cfg(feature = "ay-chc-native")]
fn private_exact_typed_prepared_input(
    verification: &TypedChcPdrFullVerification,
    obligation: &trust_mc_core::MirChcPdrObligation,
    options: &trust_mc_core::ChcPdrSolveOptions,
) -> Option<PreparedTypedChcPdrInput> {
    let trace = std::env::var_os("TRUST_SEAL_TRACE").is_some();
    let prepared = match prepare_validated_typed_chc_pdr_input(obligation) {
        Ok(prepared) => prepared,
        Err(error) => {
            if trace {
                eprintln!(
                    "[SEAL_TRACE] exact typed-input preparation failed before replay: {error:?}"
                );
            }
            return None;
        }
    };
    let normalized = &prepared.normalized;
    let candidate = match trust_mc_core::validated_native_typed_chc_pdr_candidate(
        &verification.verdict,
    ) {
        Ok(candidate) => candidate,
        Err(error) => {
            if trace {
                eprintln!("[SEAL_TRACE] typed CHC/PDR candidate validation failed: {error:?}");
            }
            return None;
        }
    };
    let expected_cache_key = typed_full_verification_cache_key(obligation, options, normalized);
    let expected_typed_problem =
        typed_chc_problem_artifact_bytes(obligation, &normalized.normalized_input);
    let mut typed_problem_artifacts = candidate.proof.artifacts.iter().filter(|artifact| {
        artifact.kind == trust_mc_core::FullVerificationArtifactKind::TypedChcProblem
    });
    let typed_problem = typed_problem_artifacts.next()?;
    if typed_problem_artifacts.next().is_some()
        || typed_problem.materialized_bytes()? != expected_typed_problem.as_slice()
        || normalized.route != verification.route
        || normalized.normalized_input != candidate.proof.obligation.normalized_input
        || normalized.normalized_input_hash != candidate.proof.obligation.normalized_input_hash
        || normalized.obligation_set_hash != verification.cache_key.parts.obligation_set_hash
        || expected_cache_key != verification.cache_key
        || verification.cache_key.validate().is_err()
        || verification.artifact_directory != typed_artifact_directory(&expected_cache_key)
        || candidate.proof.metadata.cache_key.as_ref() != Some(&expected_cache_key.key)
        || obligation.native_metadata.as_ref() != candidate.native_metadata
        || obligation.obligation_id != candidate.proof.obligation.obligation_id
        || obligation.stats() != candidate.proof.stats
        || verification.outcome.obligation_id != obligation.obligation_id
        || verification.outcome.stats != obligation.stats()
    {
        return None;
    }
    Some(prepared)
}

#[cfg(feature = "ay-chc-native")]
fn private_exact_chc_validity_replay_seal(
    verification: &TypedChcPdrFullVerification,
    prepared: PreparedTypedChcPdrInput,
    options: &trust_mc_core::ChcPdrSolveOptions,
) -> Option<PrivateChcValiditySeal> {
    let candidate =
        trust_mc_core::validated_native_typed_chc_pdr_candidate(&verification.verdict).ok()?;
    if candidate.proof_kind != trust_mc_core::ChcPdrProofKind::ChcValidity {
        return None;
    }
    let trust_mc_core::ChcPdrSolveStatus::Unknown { reason } = &verification.outcome.status else {
        return None;
    };
    if reason != trust_mc_core::CHC_VALIDITY_FRESH_CONSUMER_REPLAY_REQUIRED {
        return None;
    }

    // Re-establish the CHC-level claim from the freshly lowered exact request,
    // independently of the candidate's transcript. A structural candidate is
    // accepted only when fresh route selection still finds no rule deriving the
    // query. An acyclic direct-SMT candidate is accepted only after a second
    // complete decision over the fresh problem reaches Safe. The latter retains
    // the production complete-encoding guard: a reduced one-predicate sub-VC can
    // never mint exact-direct authority.
    let derivation = match prepared.normalized.route {
        TypedChcPdrRoute::TriviallySafe if prepared.problem.is_none() => {
            PrivateChcValidityDerivation::ExactDirectStructuralReplay
        }
        TypedChcPdrRoute::PdrProof => {
            let problem = prepared.problem?;
            if problem.predicates().len() < 2 {
                return None;
            }
            let replay_timeout = effective_typed_chc_timeout(options);
            let replay_watchdog = replay_timeout.saturating_add(Duration::from_secs(2));
            let decision = run_native_solve_within_deadline(replay_watchdog, move || {
                crate::direct_smt_cex::acyclic_direct_smt_decision(&problem)
            });
            if !matches!(decision, Some(crate::direct_smt_cex::AcyclicDecision::Safe)) {
                return None;
            }
            PrivateChcValidityDerivation::ExactDirectAcyclicDirectSmtReplay
        }
        _ => return None,
    };
    let binding = private_chc_validity_binding(verification, derivation)?;
    Some(PrivateChcValiditySeal { derivation, binding })
}

#[cfg(feature = "ay-chc-native")]
fn private_pdr_invariant_replay_seal(
    verification: &TypedChcPdrFullVerification,
    prepared: PreparedTypedChcPdrInput,
    options: &trust_mc_core::ChcPdrSolveOptions,
) -> Option<PrivatePdrInvariantSeal> {
    if verification.route != TypedChcPdrRoute::PdrProof {
        return None;
    }
    let candidate =
        trust_mc_core::validated_native_typed_chc_pdr_candidate(&verification.verdict).ok()?;
    if candidate.proof_kind != trust_mc_core::ChcPdrProofKind::PdrInvariant {
        return None;
    }
    let trust_mc_core::ChcPdrSolveStatus::Unknown { reason } = &verification.outcome.status else {
        return None;
    };
    if reason != trust_mc_core::PDR_INVARIANT_FRESH_CONSUMER_REPLAY_REQUIRED {
        return None;
    }

    // The prepared problem was freshly lowered from the exact retained
    // `MirChcPdrObligation` after the solve completed. It is deliberately not
    // the solver's retained problem or a deserialized normalized-input string.
    let problem = prepared.problem?;
    let mut invariant_artifacts = candidate.proof.artifacts.iter().filter(|artifact| {
        artifact.kind == trust_mc_core::FullVerificationArtifactKind::PdrInvariantModel
    });
    let invariant_artifact = invariant_artifacts.next()?;
    if invariant_artifacts.next().is_some() {
        return None;
    }
    let invariant_bytes = invariant_artifact.materialized_bytes()?;
    let invariant_model_digest = invariant_artifact.digest.clone()?;
    if invariant_model_digest != trust_mc_core::EvidenceHash::sha256_bytes(invariant_bytes) {
        return None;
    }
    let invariant_model_byte_len = invariant_artifact.byte_len?;
    if invariant_model_byte_len != u64::try_from(invariant_bytes.len()).ok()? {
        return None;
    }

    // Strict parsing independently checks schema, canonical bytes, complete
    // predicate coverage, and the exact normalized hash of this fresh problem.
    let model = ay_chc::parse_qf_invariant_model_artifact(&problem, invariant_bytes).ok()?;
    let replay_timeout = effective_typed_chc_timeout(options);
    let replay_watchdog = replay_timeout.saturating_add(Duration::from_secs(2));
    let validation_problem = problem.clone();
    let validated = run_native_solve_within_deadline(replay_watchdog, move || {
        let config = ay_encode::invoke::EncodeConfig::new()
            .with_engine(ay_encode::invoke::Engine::Pdr)
            .with_proof_mode(ay_encode::invoke::ProofMode::Strict)
            .with_timeout(replay_timeout)
            .to_pdr_config();
        ay_chc::engines::validate_external_invariant_model(&validation_problem, &model, &config)
    });
    if !matches!(validated, Some(Ok(true))) {
        return None;
    }

    let typed_problem = candidate.proof.artifacts.iter().find(|artifact| {
        artifact.kind == trust_mc_core::FullVerificationArtifactKind::TypedChcProblem
    })?;
    let replay = PrivatePdrInvariantReplayBinding {
        exact_obligation_set_hash: prepared.normalized.obligation_set_hash,
        fresh_problem_hash: prepared.normalized.normalized_input_hash,
        typed_problem_digest: typed_problem.digest.clone()?,
        invariant_model_digest,
        invariant_model_byte_len,
    };
    let binding = private_pdr_invariant_binding(verification, &replay)?;
    Some(PrivatePdrInvariantSeal { replay, binding })
}

fn private_pdr_invariant_binding(
    verification: &TypedChcPdrFullVerification,
    replay: &PrivatePdrInvariantReplayBinding,
) -> Option<trust_mc_core::EvidenceHash> {
    let candidate =
        trust_mc_core::validated_native_typed_chc_pdr_candidate(&verification.verdict).ok()?;
    if candidate.proof_kind != trust_mc_core::ChcPdrProofKind::PdrInvariant
        || verification.route != TypedChcPdrRoute::PdrProof
        || verification.cache_key.validate().is_err()
        || verification.artifact_directory != typed_artifact_directory(&verification.cache_key)
        || candidate.proof.metadata.cache_key.as_ref() != Some(&verification.cache_key.key)
        || candidate.proof.obligation.normalized_input_hash != replay.fresh_problem_hash
        || verification.cache_key.parts.normalized_input_hash != replay.fresh_problem_hash
        || verification.cache_key.parts.obligation_set_hash != replay.exact_obligation_set_hash
        || candidate.proof.obligation.obligation_id != verification.outcome.obligation_id
        || candidate.proof.stats != verification.outcome.stats
    {
        return None;
    }
    let trust_mc_core::ChcPdrSolveStatus::Unknown { reason } = &verification.outcome.status else {
        return None;
    };
    if reason != trust_mc_core::PDR_INVARIANT_FRESH_CONSUMER_REPLAY_REQUIRED {
        return None;
    }

    let mut typed_problem_artifacts = candidate.proof.artifacts.iter().filter(|artifact| {
        artifact.kind == trust_mc_core::FullVerificationArtifactKind::TypedChcProblem
    });
    let typed_problem = typed_problem_artifacts.next()?;
    if typed_problem_artifacts.next().is_some()
        || typed_problem.digest.as_ref() != Some(&replay.typed_problem_digest)
        || typed_problem.materialized_bytes().is_none()
    {
        return None;
    }
    let mut invariant_artifacts = candidate.proof.artifacts.iter().filter(|artifact| {
        artifact.kind == trust_mc_core::FullVerificationArtifactKind::PdrInvariantModel
    });
    let invariant = invariant_artifacts.next()?;
    if invariant_artifacts.next().is_some()
        || invariant.digest.as_ref() != Some(&replay.invariant_model_digest)
        || invariant.byte_len != Some(replay.invariant_model_byte_len)
        || invariant.materialized_bytes().is_none()
    {
        return None;
    }

    let binding_envelope = serde_json::json!({
        "schema": "trust_mc.private-pdr-invariant-replay-authority/v1",
        "domain": "fresh-exact-typed-obligation-plus-independent-strict-invariant-replay-not-serializable",
        "route": "pdr-proof",
        "cache_key": &verification.cache_key,
        "artifact_directory": &verification.artifact_directory,
        "exact_obligation_set_hash": &replay.exact_obligation_set_hash,
        "fresh_problem_hash": &replay.fresh_problem_hash,
        "typed_problem_digest": &replay.typed_problem_digest,
        "invariant_model_digest": &replay.invariant_model_digest,
        "invariant_model_byte_len": replay.invariant_model_byte_len,
        "outcome": {
            "obligation_id": &verification.outcome.obligation_id,
            "candidate_status": "unknown",
            "reason": reason,
            "stats": {
                "relation_count": verification.outcome.stats.relation_count,
                "clause_count": verification.outcome.stats.clause_count,
            },
            "diagnostics": &verification.outcome.diagnostics,
        },
        // This includes the exact bounded materialized bytes and all producer
        // proof bindings, so any response/artifact mutation changes the seal.
        "candidate_verdict": &verification.verdict,
    });
    serde_json::to_vec(&binding_envelope)
        .ok()
        .map(|bytes| trust_mc_core::EvidenceHash::sha256_bytes(&bytes))
}

fn native_typed_proof_strength(
    proof_kind: trust_mc_core::ChcPdrProofKind,
) -> NativeTypedProofStrength {
    match proof_kind {
        trust_mc_core::ChcPdrProofKind::ChcValidity => NativeTypedProofStrength::ChcValidity,
        trust_mc_core::ChcPdrProofKind::PdrInvariant => NativeTypedProofStrength::PdrInvariant,
    }
}

fn native_typed_backend_label(route: TypedChcPdrRoute, verification_mode: &str) -> String {
    let route = match route {
        TypedChcPdrRoute::TriviallySafe => "trivial-safe",
        TypedChcPdrRoute::PdrProof => "pdr-proof",
    };
    format!("trust_mc::typed-chc-pdr::{verification_mode}::{route}")
}

fn single_native_proof_id(proof_obligation_ids: &[u32]) -> Option<u32> {
    match proof_obligation_ids {
        [only] => Some(*only),
        _ => None,
    }
}

fn native_typed_artifact_refs(
    proof: &trust_mc_core::ChcPdrProofEvidence,
    kind: trust_mc_core::FullVerificationArtifactKind,
) -> Vec<NativeTypedProofArtifactRef> {
    proof
        .artifacts
        .iter()
        .filter(|artifact| artifact.kind == kind)
        .map(native_typed_artifact_ref)
        .collect()
}

fn native_typed_all_artifact_refs(
    proof: &trust_mc_core::ChcPdrProofEvidence,
) -> Vec<NativeTypedProofArtifactRef> {
    proof.artifacts.iter().map(native_typed_artifact_ref).collect()
}

fn native_typed_artifact_ref(
    artifact: &trust_mc_core::FullVerificationArtifact,
) -> NativeTypedProofArtifactRef {
    NativeTypedProofArtifactRef {
        kind: artifact.kind,
        uri: artifact.label.clone(),
        digest: artifact.digest.clone(),
        byte_len: artifact.byte_len,
        materialization: artifact.materialization().cloned(),
    }
}

#[cfg(feature = "ay-chc-native")]
fn ay_chc_proof_run_artifact_descriptor(
    artifact: &ay_chc::ChcProofRunArtifact,
) -> serde_json::Value {
    serde_json::json!({
        "schema": artifact.schema(),
        "role": artifact.role(),
        "digest": artifact.digest().to_json_value(),
    })
}

/// Library-only runner for typed MIR-derived CHC/PDR obligations.
///
/// This is the stable embedding surface for compiler integrations such as
/// tRust. It depends only on owned `trust-mc_core` problem objects and the native
/// AY CHC/PDR engine, so callers can enable `trust-mc-driver/native-typed-chc-pdr`
/// without linking the rustc-private `trust-mc-compiler` crate or spawning the CLI.
#[derive(Debug, Clone, Default)]
#[non_exhaustive]
pub struct NativeTypedChcPdrRunner {
    options: trust_mc_core::ChcPdrSolveOptions,
}

impl NativeTypedChcPdrRunner {
    /// Construct a runner with trust_mc's default typed CHC/PDR options.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Construct a runner with explicit typed CHC/PDR options.
    #[must_use]
    pub fn with_options(options: trust_mc_core::ChcPdrSolveOptions) -> Self {
        Self { options }
    }

    /// Return the options applied to obligations solved through this runner.
    #[must_use]
    pub fn options(&self) -> &trust_mc_core::ChcPdrSolveOptions {
        &self.options
    }

    /// Solve one typed CHC/PDR obligation and return the typed solver outcome.
    pub fn solve(
        &self,
        obligation: trust_mc_core::MirChcPdrObligation,
    ) -> NativeSolveResult<trust_mc_core::ChcPdrSolveOutcome> {
        solve_typed_chc_pdr(
            trust_mc_core::ChcPdrSolveRequest::new(obligation).with_options(self.options.clone()),
        )
    }

    /// Solve one typed CHC/PDR obligation and return a content-bound candidate.
    ///
    /// This generic source-unbound API never mints private replay authority,
    /// even when the exact submitted CHC is proved.
    pub fn solve_full_verification(
        &self,
        obligation: trust_mc_core::MirChcPdrObligation,
    ) -> NativeSolveResult<TypedChcPdrFullVerification> {
        solve_typed_chc_pdr_full_verification(
            trust_mc_core::ChcPdrSolveRequest::new(obligation).with_options(self.options.clone()),
        )
    }

    /// Solve one exact typed CHC/PDR obligation and independently replay its
    /// proof candidate before returning it.
    ///
    /// The ordinary public candidate remains reject-only. This path freshly
    /// re-lowers the retained typed obligation. A
    /// `ChcValidity` candidate must repeat its structural or complete acyclic
    /// direct-SMT derivation over that fresh problem. A `PdrInvariant` candidate
    /// must strictly parse its one materialized QF model and validate every Horn
    /// clause in a fresh solver. A successful replay installs an affine,
    /// non-serializable CHC-level authority retrievable through
    /// [`TypedChcPdrFullVerification::authorized_native_proof`]. It does not
    /// attest source-to-CHC completeness; a compiler consumer must independently
    /// bind the exact source claim to this exact obligation.
    #[cfg(feature = "ay-chc-native")]
    pub fn solve_full_verification_with_fresh_exact_replay(
        &self,
        obligation: trust_mc_core::MirChcPdrObligation,
    ) -> NativeSolveResult<TypedChcPdrFullVerification> {
        let exact_obligation = obligation.clone();
        let verification = self.solve_full_verification(obligation)?;
        Ok(verification.with_private_exact_typed_replay_authority(&exact_obligation, &self.options))
    }

    /// Require private native-bundle authority for a typed CHC/PDR obligation.
    ///
    /// A generic typed obligation cannot carry that authority, so this strict
    /// compatibility entry point rejects source-unbound candidates. Compiler
    /// integrations must use [`NativeTrustIrChcPdrRunner`] and retain the opaque
    /// authority borrowed from its live response.
    pub fn solve_native_proof_grade(
        &self,
        obligation: trust_mc_core::MirChcPdrObligation,
    ) -> NativeSolveResult<TypedChcPdrFullVerification> {
        solve_typed_chc_pdr_native_proof_grade(
            trust_mc_core::ChcPdrSolveRequest::new(obligation).with_options(self.options.clone()),
        )
    }
}

/// Bundle-level exact-module result for native trust_ir CHC/PDR verification.
#[cfg(feature = "native-trust-ir-bundle")]
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct NativeTrustIrChcPdrBundleEvidence {
    /// One live opaque-authority result per typed native trust-mc CHC/PDR
    /// request that produced an exact-module proof.
    pub obligations: Vec<NativeTrustIrChcPdrEvidence>,
    /// Trust (T3, per-obligation transport delivery): one honest per-request
    /// outcome for every typed native trust-mc CHC/PDR request whose solve ran
    /// but did NOT yield private exact-module authority (ay-chc unknown,
    /// refutation, candidate-admission rejection, or unsupported shape).
    ///
    /// SOUNDNESS INVARIANT: a `not_proved` row NEVER carries proof evidence —
    /// it only lets the consumer replace its generic bundle-level unsupported
    /// stamp with the failing request's own fail-closed reason. Requests that
    /// prove still populate `obligations` with the full digest-backed evidence
    /// chain (digests, transcripts, replay) unchanged; no verdict may flip to
    /// proved except one whose own request produced a privately sealed
    /// exact-module derivation that the existing validation accepts.
    pub not_proved: Vec<NativeTrustIrChcPdrNotProved>,
    /// One witnessed refutation per typed native trust-mc CHC/PDR request the
    /// solver `Refuted { witness: Some(_) }`.
    ///
    /// SOUNDNESS INVARIANT: a `refuted` row carries NO proof authority in
    /// either direction — it never enters the sealed proof-transport path, and
    /// the carried witness is producer data the consumer MUST independently
    /// revalidate (recompute the encoded-formula digest from its own fresh
    /// translation of its own retained bundle, recompute the
    /// semantic-configuration digest from its own engine configuration,
    /// require the all-zero exact-encoding concreteness attestation, and
    /// accept only machine-check kinds it recognizes) before surfacing a
    /// Failed verdict. A witnessless `Refuted` stays in `not_proved`.
    pub refuted: Vec<NativeTrustIrChcPdrRefuted>,
}

/// Witnessed refutation for one typed native trust_ir trust-mc CHC/PDR request.
///
/// `verification.outcome.status` is `Refuted { witness: Some(_) }` and
/// `verification.verdict` is `Failed` carrying the materialized counterexample
/// artifact the witness payload is bound to. Refutation-only: nothing in this
/// row can mint proof credit (there is no sealed transport record on it), and
/// consumers fail closed on any witness field they cannot recompute or any
/// machine-check kind they do not recognize.
#[cfg(feature = "native-trust-ir-bundle")]
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct NativeTrustIrChcPdrRefuted {
    /// Typed obligation translated from the native trust_ir bundle. Its
    /// `obligation.obligation_id` is the canonical native obligation id the
    /// consumer keys per-row outcomes by.
    pub translated: trust_mc_trust_bmc::NativeTrustMcChcPdrObligation,
    /// Full-verification result whose outcome carries the refutation witness.
    pub verification: TypedChcPdrFullVerification,
}

/// Honest per-request not-proved outcome for one typed native trust_ir
/// trust-mc CHC/PDR request (T3 per-obligation transport delivery).
///
/// Carries NO proof evidence and NO counterexample artifact: it neither proves
/// nor refutes the obligation. It exists only so the consumer can surface the
/// row's OWN root cause instead of the former whole-bundle `?`-propagation,
/// which discarded proved siblings and stamped every obligation of the
/// function with one generic bundle-level reason.
#[cfg(feature = "native-trust-ir-bundle")]
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct NativeTrustIrChcPdrNotProved {
    /// Typed obligation translated from the native trust_ir bundle. Its
    /// `obligation.obligation_id` is the canonical native obligation id the
    /// consumer keys per-row reasons by.
    pub translated: trust_mc_trust_bmc::NativeTrustMcChcPdrObligation,
    /// Stable fail-closed reason the solve did not produce exact-module authority.
    pub reason: String,
}

/// Live exact-module evidence for one typed native trust_ir trust-mc CHC/PDR request.
#[cfg(feature = "native-trust-ir-bundle")]
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct NativeTrustIrChcPdrEvidence {
    /// Typed obligation translated from the native trust_ir bundle.
    pub translated: trust_mc_trust_bmc::NativeTrustMcChcPdrObligation,
    /// Full-verification result returned by trust_mc's native typed CHC/PDR runner.
    pub verification: TypedChcPdrFullVerification,
    /// Stable transport record with request/proof id binding and digest-backed artifacts.
    pub transport: NativeTypedChcPdrProofTransport,
}

/// Library runner that accepts native trust_ir bundles directly.
///
/// This is the first-class tRust embedding surface for native bundle input:
/// callers pass a `trust_ir::NativeVerificationBundle`, trust-mc selects typed
/// `NativeVerificationRequest::TrustMc` CHC/PDR requests through `trust-mc-trust-bmc`,
/// validates the complete module, applies the strict proof-authority preflight,
/// solves each fresh translation, and returns the translated obligation with a
/// live mutation-bound exact-module capability. This does not establish a
/// source-program correspondence; callers own that separate private binding.
#[cfg(feature = "native-trust-ir-bundle")]
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct NativeTrustIrChcPdrRunner {
    typed_runner: NativeTypedChcPdrRunner,
    translate_options: trust_mc_trust_bmc::TranslateOptions,
}

#[cfg(feature = "native-trust-ir-bundle")]
impl Default for NativeTrustIrChcPdrRunner {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(feature = "native-trust-ir-bundle")]
impl NativeTrustIrChcPdrRunner {
    /// Construct a bundle runner with default translation and solve options.
    #[must_use]
    pub fn new() -> Self {
        Self {
            typed_runner: NativeTypedChcPdrRunner::new(),
            translate_options: trust_mc_trust_bmc::TranslateOptions::default(),
        }
    }

    /// Construct a bundle runner with explicit typed CHC/PDR solve options.
    #[must_use]
    pub fn with_solve_options(options: trust_mc_core::ChcPdrSolveOptions) -> Self {
        Self {
            typed_runner: NativeTypedChcPdrRunner::with_options(options),
            translate_options: trust_mc_trust_bmc::TranslateOptions::default(),
        }
    }

    /// Replace the trust_ir-to-CHC translation options.
    ///
    /// Diagnostic translation accepts every option combination. The proof-grade
    /// bundle entry point rejects any option that disables a safety obligation;
    /// `logic` and `timeout_ms` may still be customized because they do not omit
    /// generated checks.
    #[must_use]
    pub fn with_translate_options(mut self, options: trust_mc_trust_bmc::TranslateOptions) -> Self {
        self.translate_options = options;
        self
    }

    /// Return the typed CHC/PDR solve options used by this runner.
    #[must_use]
    pub fn solve_options(&self) -> &trust_mc_core::ChcPdrSolveOptions {
        self.typed_runner.options()
    }

    /// Return the trust_ir translation options used by this runner.
    #[must_use]
    pub fn translate_options(&self) -> &trust_mc_trust_bmc::TranslateOptions {
        &self.translate_options
    }

    /// Translate typed trust-mc CHC/PDR requests from a native trust_ir bundle.
    pub fn translate_obligations(
        &self,
        bundle: &trust_ir::NativeVerificationBundle,
    ) -> NativeSolveResult<Vec<trust_mc_trust_bmc::NativeTrustMcChcPdrObligation>> {
        trust_mc_trust_bmc::trust_mc_chc_pdr_obligations_from_native_bundle(
            bundle,
            &self.translate_options,
        )
        .map_err(native_trust_ir_bundle_error)
    }

    /// Translate and solve all typed trust-mc CHC/PDR requests in a native trust_ir bundle.
    ///
    /// This method is strict: every result in `obligations` passed full TrustIr
    /// module validation, the conservative proof-authority preflight, fresh
    /// translation, and private seal recomputation. The diagnostic transport is
    /// cross-checked against request/proof/native ids before being returned.
    ///
    /// Trust (T3, per-obligation transport delivery): the solve is NOT
    /// all-or-nothing. A request whose solve ran but did not yield private
    /// exact-module authority (ay-chc unknown, refutation, candidate-admission
    /// rejection, or unsupported shape) is collected into
    /// [`NativeTrustIrChcPdrBundleEvidence::not_proved`] instead of discarding
    /// the whole bundle, so sibling requests that proved keep their sealed live
    /// response. A bundle where NO request proves still returns
    /// `Ok` with an empty `obligations` set and a fully populated `not_proved`
    /// map. Structural errors stay fatal (fail-closed `Err`): bundle
    /// translation failures, invalid solve inputs, and any transport-record or
    /// transport-binding failure after private authorization indicate corruption or
    /// internal inconsistency — never solver inconclusiveness — and must fail
    /// the bundle.
    ///
    /// SOUNDNESS INVARIANT: `not_proved` rows never produce proof evidence; no
    /// verdict may flip to proved except one whose own request produced a
    /// privately sealed exact-module derivation that recomputes successfully.
    pub fn solve_bundle_native_proof_grade(
        &self,
        bundle: &trust_ir::NativeVerificationBundle,
    ) -> NativeSolveResult<NativeTrustIrChcPdrBundleEvidence> {
        self.solve_bundle_native_proof_grade_inner(bundle, None)
    }

    /// Translate and solve a bundle produced at the audited live source-lowering seam.
    ///
    /// This is the only proof-grade entry point that can admit source-generated
    /// `Inst::Assume`, `Inst::PtrMetadata`, and `ProofAnnotation::Wrapping`
    /// constructs. The authority is non-cloneable, non-serializable, and must
    /// still authorize this exact valid bundle. Its issuer is a safe semantic-TCB
    /// seam, so the surrounding constellation must also gate
    /// `SourceGenerationAuthority::mint_from_live_lowering` to the audited live
    /// producer call site; this API cannot by itself prove that the issuer's
    /// source-origin contract was honored. Replay, subprocess, cache, and
    /// ordinary library callers must use
    /// [`Self::solve_bundle_native_proof_grade`], which remains fail-closed for
    /// those constructs.
    pub fn solve_bundle_native_proof_grade_with_source_authority(
        &self,
        bundle: &trust_ir::NativeVerificationBundle,
        authority: &trust_ir::SourceGenerationAuthority,
    ) -> NativeSolveResult<NativeTrustIrChcPdrBundleEvidence> {
        self.solve_bundle_native_proof_grade_inner(bundle, Some(authority))
    }

    fn solve_bundle_native_proof_grade_inner(
        &self,
        bundle: &trust_ir::NativeVerificationBundle,
        authority: Option<&trust_ir::SourceGenerationAuthority>,
    ) -> NativeSolveResult<NativeTrustIrChcPdrBundleEvidence> {
        let disabled_checks = disabled_native_bundle_safety_checks(&self.translate_options);
        if !disabled_checks.is_empty() {
            return Err(NativeSolveError::InvalidInput {
                field: "translate_options".to_string(),
                detail: format!(
                    "native bundle proof authority requires the full safety profile; disabled: {}",
                    disabled_checks.join(", ")
                ),
            });
        }
        validate_native_bundle_proof_authority_input(bundle, authority)?;
        let translated = self.translate_obligations(bundle)?;
        let mut obligations = Vec::with_capacity(translated.len());
        let mut not_proved = Vec::new();
        let mut refuted = Vec::new();

        for translated in translated {
            let verification = match self
                .typed_runner
                .solve_full_verification(translated.obligation.clone())
            {
                Ok(verification) => verification
                    .with_private_native_bundle_authority(&translated, self.typed_runner.options()),
                Err(error) if native_solve_error_is_per_request_not_proved(&error) => {
                    not_proved.push(NativeTrustIrChcPdrNotProved {
                        reason: error.to_string(),
                        translated,
                    });
                    continue;
                }
                Err(error) => return Err(error),
            };
            // Trust (refutation transport): a witnessed refutation is NOT a
            // proof — it never enters the sealed-transport path below (whose
            // record exists only for proof authority). It is delivered as its
            // own typed row so the consumer can independently revalidate the
            // witness (recomputed digests, concreteness, recognized
            // machine-check kind) and, only then, surface a Failed verdict.
            //
            // SCOPE: only the bounded-unroll lane's witnesses ride this
            // channel today. Its mint is additionally guarded by the
            // trust-ir-stage GROUNDING gate (`bounded_unroll`), which the
            // other witness kinds minted on this path do not yet carry —
            // their `ChcVc`-production stage may contain translation havoc
            // the lowering accounting does not cover, so they keep today's
            // honest not_proved delivery byte-for-byte. Widening this match
            // requires extending the grounding gate to those mints first.
            // A witnessless `Refuted` stays on the not_proved path exactly as
            // before: with nothing certifying the encoding's concreteness it
            // neither proves nor refutes.
            if matches!(
                &verification.outcome.status,
                trust_mc_core::ChcPdrSolveStatus::Refuted { witness: Some(witness) }
                    if matches!(
                        witness.verification,
                        trust_mc_core::ChcPdrCexVerification::BoundedUnrollDirectSmtModel { .. }
                    )
            ) {
                refuted.push(NativeTrustIrChcPdrRefuted { translated, verification });
                continue;
            }
            // Minting was attempted only after fresh translation from this exact
            // validated bundle. A non-authoritative/undecided response is an
            // honest per-request not-proved result; only a successfully sealed
            // response may cross the exact-module consumer boundary. A source
            // claim still requires the compiler consumer's private binding.
            let transport = match verification.native_proof_transport_record() {
                Ok(transport) => transport,
                Err(error) if native_solve_error_is_per_request_not_proved(&error) => {
                    not_proved.push(NativeTrustIrChcPdrNotProved {
                        reason: error.to_string(),
                        translated,
                    });
                    continue;
                }
                Err(error) => return Err(error),
            };
            validate_native_trust_ir_transport_binding(&translated, &transport)?;
            obligations.push(NativeTrustIrChcPdrEvidence { translated, verification, transport });
        }

        Ok(NativeTrustIrChcPdrBundleEvidence { obligations, not_proved, refuted })
    }
}

/// The classification of one rejected `Alloca`: a short greppable bucket token
/// plus a human-readable expansion.
#[cfg(feature = "native-trust-ir-bundle")]
struct AllocaRejectionReason {
    /// `<lane1>/<lane2>`, or a single token when the instruction never reached
    /// the two-lane predicate at all.
    kind: String,
    detail: String,
}

/// Why the guarded `Inst::Alloca` admission arm did not take this instruction.
///
/// DIAGNOSTIC ONLY — it decides nothing. It reproduces, in order, the three ways
/// the guard can fail:
///
///  1. the arm's own pattern requires `count: None`, so an ARRAY alloca never
///     reaches the predicate;
///  2. likewise `align: None`, a caller-asserted alignment the translator
///     ignores entirely;
///  3. otherwise the arm called `single_cell_alloca_is_admissible` and it said
///     no — ask it for both lanes' first blocking condition.
///
/// (3) re-runs the same pure predicate on the same inputs, so it always agrees
/// with the guard that just rejected.
#[cfg(feature = "native-trust-ir-bundle")]
/// Admit `Inst::Borrow`/`BorrowMut` at the proof-authority input gate (R70).
///
/// DEFAULT-OFF. Flag-off is byte-identical to the post-merge fail-closed predicate,
/// so the default lane and every `ProofAuthorityAttackShape` pin are untouched and
/// one gate run can A/B it. The soundness argument lives at the arm, not here.
///
/// Read once per process, not per instruction.
fn admit_transparent_borrow_instructions() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var_os("TRUST_ADMIT_BORROW_INST").is_some())
}

// The cfg below was originally attached to this function; R70's insertion of
// `admit_transparent_borrow_instructions` between the attribute and its target
// silently re-pointed it, leaving this function compiled without its optional
// deps (`trust_ir`, `trust-mc-trust-bmc`) — a build break on default features.
#[cfg(feature = "native-trust-ir-bundle")]
fn alloca_rejection_reason(
    module: &trust_ir::Module,
    function: &trust_ir::Function,
    result: Option<trust_ir::value::ValueId>,
    ty: &trust_ir::ty::Ty,
    has_count: bool,
    has_align: bool,
) -> AllocaRejectionReason {
    if has_count {
        return AllocaRejectionReason {
            kind: "alloca_count_some".to_string(),
            detail: "array alloca: the extent is a runtime value, not an internally bound one"
                .to_string(),
        };
    }
    if has_align {
        return AllocaRejectionReason {
            kind: "alloca_align_some".to_string(),
            detail: "caller-asserted alignment on the alloca; the translator models no alignment"
                .to_string(),
        };
    }
    let Some(result) = result else {
        return AllocaRejectionReason {
            kind: "alloca_no_result".to_string(),
            detail: "the alloca binds no result value, so there is no cell pointer to gate"
                .to_string(),
        };
    };
    match trust_mc_trust_bmc::single_cell_alloca_rejection(module, function, result, ty) {
        Some(rejection) => AllocaRejectionReason {
            kind: rejection.kind(),
            detail: rejection.to_string(),
        },
        // Unreachable while the guard and this call agree; reported rather than
        // asserted so a diagnostic can never abort a verification run.
        None => AllocaRejectionReason {
            kind: "admissible_but_rejected".to_string(),
            detail: "the admission predicate accepts this cell; the guard rejected it for another \
                     reason (report this)"
                .to_string(),
        },
    }
}

/// Validate the exact TrustIr semantics that the proof-grade translator is
/// currently capable of preserving without importing unauthenticated source
/// claims.
///
/// Diagnostic translation intentionally remains broader. This gate is only for
/// the proof-grade exact-bundle/CHC authority path: every construct rejected
/// here has a known translation lane that can omit a safety edge or import a
/// public claim. Keeping the checks together makes additions auditable and
/// ensures a future relaxation has to ship with an exact semantic derivation.
#[cfg(feature = "native-trust-ir-bundle")]
fn validate_native_bundle_proof_authority_input(
    bundle: &trust_ir::NativeVerificationBundle,
    authority: Option<&trust_ir::SourceGenerationAuthority>,
) -> NativeSolveResult<()> {
    // The capability is necessary but deliberately not sufficient for proof
    // authority: it relaxes only the three source-generated constructs whose
    // CHC semantics are modeled below. Every other public semantic shortcut
    // remains rejected even for the exact live bundle.
    let source_generation_authorized = authority.is_some_and(|a| a.authorizes_bundle(bundle));
    let module_report = trust_ir_build::validate_module_report(&bundle.module);
    if !module_report.is_ok() {
        let detail = module_report
            .errors()
            .iter()
            .take(8)
            .map(ToString::to_string)
            .collect::<Vec<_>>()
            .join("; ");
        return Err(native_bundle_proof_authority_input_error(
            "module",
            format!("full TrustIr module validation failed: {detail}"),
        ));
    }
    match &bundle.module.target_info {
        Some(target) if target.pointer_size == 8 => {}
        Some(target) => {
            return Err(native_bundle_proof_authority_input_error(
                "module.target_info.pointer_size",
                format!(
                    "proof-grade CHC translation currently models 64-bit pointers, but target `{}` declares {}-byte pointers",
                    target.triple, target.pointer_size
                ),
            ));
        }
        None => {
            return Err(native_bundle_proof_authority_input_error(
                "module.target_info",
                "proof-grade CHC translation requires an explicit 64-bit target profile"
                    .to_string(),
            ));
        }
    }

    let mut pending = Vec::new();
    for request in &bundle.requests {
        if let trust_ir::NativeVerificationRequest::TrustMc(request) = request {
            pending.push(request.function);
        }
    }
    let mut visited = BTreeSet::new();

    while let Some(function_id) = pending.pop() {
        if !visited.insert(function_id.index()) {
            continue;
        }
        let Some(function) = bundle.module.function_by_id(function_id) else {
            return Err(native_bundle_proof_authority_input_error(
                "module.functions",
                format!("requested or reachable function #{} is missing", function_id.index()),
            ));
        };

        for block in &function.blocks {
            for (instruction_index, node) in block.body.iter().enumerate() {
                let location = format!(
                    "function `{}` block #{} instruction {}",
                    function.name,
                    block.id.index(),
                    instruction_index
                );

                // `FreshSymbolicHavoc` is deliberately a public, forgeable
                // semantic marker rather than an authority token. It selects
                // the already-sound CHC interpretation of `Undef` as one
                // stable, unconstrained value. That interpretation can only
                // enlarge the error set, so admitting the exact pair is sound
                // even after serialization. The marker grants no permission
                // to narrow the value with `Assume`, pointer metadata, or any
                // other source-authority-gated construct.
                let fresh_symbolic_havoc = node
                    .proofs
                    .iter()
                    .any(|proof| matches!(proof, trust_ir::ProofAnnotation::FreshSymbolicHavoc));
                if fresh_symbolic_havoc && !matches!(&node.inst, trust_ir::Inst::Undef { .. }) {
                    return Err(native_bundle_proof_authority_input_error(
                        "module.functions.proof_annotations",
                        format!(
                            "{location} carries FreshSymbolicHavoc on a non-Undef instruction; the marker grants no proof authority"
                        ),
                    ));
                }

                if !source_generation_authorized
                    && node
                        .proofs
                        .iter()
                        .any(|proof| matches!(proof, trust_ir::ProofAnnotation::Wrapping))
                {
                    return Err(native_bundle_proof_authority_input_error(
                        "module.functions.proof_annotations",
                        format!(
                            "{location} carries public Wrapping semantics that suppress an overflow obligation"
                        ),
                    ));
                }

                // `ValidBorrow` on a Load/Store is admitted only under the exact
                // live-lowering authority: the stamp is minted by the same audited
                // producer whose `Assume`/`PtrMetadata`/`Wrapping` claims are
                // admitted below, and derives from rustc's reference typing (a
                // deref through a borrow-checked `&`/`&mut`). The CHC model takes
                // no value from it — the loaded value stays fresh havoc — it only
                // discharges the access's bounds-model refusal. Everything else
                // carrying the stamp (or any replayed/serialized bundle) stays
                // fail-closed on the private borrow-authority requirement.
                if node
                    .proofs
                    .iter()
                    .any(|proof| matches!(proof, trust_ir::ProofAnnotation::ValidBorrow))
                    && !(source_generation_authorized
                        && matches!(
                            &node.inst,
                            trust_ir::Inst::Load { .. } | trust_ir::Inst::Store { .. }
                        ))
                {
                    return Err(native_bundle_proof_authority_input_error(
                        "module.functions.proof_annotations",
                        format!(
                            "{location} carries public ValidBorrow semantics; private borrow-authority replay is required"
                        ),
                    ));
                }

                match &node.inst {
                    // A stamped `Undef` is modeled by `translate_chc` as a
                    // stable fresh symbol with no value constraint. The stamp
                    // does not authenticate facts about that symbol: the
                    // `Assume` and pointer-metadata arms below remain gated by
                    // their independent exact source-generation authority.
                    trust_ir::Inst::Undef { .. } if fresh_symbolic_havoc => {}
                    trust_ir::Inst::Undef { .. } => {
                        return Err(native_bundle_proof_authority_input_error(
                            "module.functions.instructions",
                            format!(
                                "{location} executes Undef, which is TrustIr undefined behavior but is diagnostic havoc in the CHC translator"
                            ),
                        ));
                    }
                    trust_ir::Inst::Assume { .. } if source_generation_authorized => {}
                    trust_ir::Inst::Assume { .. } => {
                        return Err(native_bundle_proof_authority_input_error(
                            "module.functions.instructions",
                            format!(
                                "{location} imports an unauthenticated Assume; source-generation authority is required"
                            ),
                        ));
                    }
                    // Opt-in, default-off (`TRUST_ADMIT_BORROW_INST`). Borrow and
                    // BorrowMut are transparent aliases in the CHC translator: they
                    // import no fact, never create a stack root, and inherit provenance
                    // only from an already tracked referent. Every later load or store
                    // remains independently gated by exact stack/provenance modeling or
                    // an authorized ValidBorrow annotation. GEP remains fail-closed
                    // below because its separate `valid_ref_ptrs` path needs a distinct
                    // authority argument.
                    trust_ir::Inst::Borrow { .. } | trust_ir::Inst::BorrowMut { .. }
                        if admit_transparent_borrow_instructions() => {}
                    trust_ir::Inst::Borrow { .. } | trust_ir::Inst::BorrowMut { .. } => {
                        return Err(native_bundle_proof_authority_input_error(
                            "module.functions.instructions",
                            format!(
                                "{location} imports borrow-checker validity without a private borrow-authority capability"
                            ),
                        ));
                    }
                    trust_ir::Inst::ExtractElement { .. } => {
                        return Err(native_bundle_proof_authority_input_error(
                            "module.functions.instructions",
                            format!(
                                "{location} uses ExtractElement without an internally bound bounds derivation"
                            ),
                        ));
                    }
                    trust_ir::Inst::GEP { .. } => {
                        return Err(native_bundle_proof_authority_input_error(
                            "module.functions.instructions",
                            format!(
                                "{location} uses GEP without authenticated allocation/provenance and index bounds"
                            ),
                        ));
                    }
                    // `PtrData` rides the same audited live-lowering authority as
                    // `PtrMetadata`: it reads the data lane of a pointer-like
                    // value (asserting nothing about it), and `translate_chc`
                    // models it exactly — `ptr_parts` data when tracked, else the
                    // value itself — with no error rule.
                    trust_ir::Inst::PtrMetadata { .. } | trust_ir::Inst::PtrData { .. }
                        if source_generation_authorized => {}
                    trust_ir::Inst::PtrData { .. }
                    | trust_ir::Inst::PtrMetadata { .. }
                    | trust_ir::Inst::PtrFromParts { .. } => {
                        return Err(native_bundle_proof_authority_input_error(
                            "module.functions.instructions",
                            format!(
                                "{location} uses pointer-part semantics without an authenticated provenance and metadata-validity derivation"
                            ),
                        ));
                    }
                    // A fixed-size, metadata-less scalar or aggregate stack cell
                    // has an exact proof-grade lane when the translator either
                    // leaves it opaque (loads are fresh havoc) or proves its
                    // precise cell pointer never escapes, every direct access
                    // keeps the exact cell type, and every load is initialized by
                    // an earlier same-block store. This is default-on because the
                    // safety predicate is structural and fail closed; it imports
                    // no public proof annotation or source claim.
                    trust_ir::Inst::Alloca { ty, count: None, align: None }
                        if node.results.first().copied().is_some_and(|result| {
                            trust_mc_trust_bmc::single_cell_alloca_is_admissible(
                                &bundle.module,
                                function,
                                result,
                                ty,
                            )
                        }) => {}
                    // Preserve the fail-closed fallback while naming the exact
                    // structural admission condition that rejected this alloca.
                    trust_ir::Inst::Alloca { ty, count, align } => {
                        // MEASUREMENT (2026-08-23): this arm holds the single
                        // largest block of unknown rows on ny-cert, so it names
                        // WHICH condition of the admissible arm above failed.
                        // Purely diagnostic: `alloca_rejection_reason` reads the
                        // module and returns strings, and the admission verdict
                        // is still decided entirely by the guard on the arm
                        // above, so the set of admitted Allocas is unchanged
                        // whether or not the trace is enabled.
                        let reason = alloca_rejection_reason(
                            &bundle.module,
                            function,
                            node.results.first().copied(),
                            ty,
                            count.is_some(),
                            align.is_some(),
                        );
                        if std::env::var_os("TRUST_ALLOCA_REJECT_TRACE").is_some() {
                            eprintln!(
                                "[ALLOCA_REJECT] kind={} fn=`{}` block=#{} instr={} ty={} detail={{{}}}",
                                reason.kind,
                                function.name,
                                block.id.index(),
                                instruction_index,
                                ty,
                                reason.detail
                            );
                        }
                        return Err(native_bundle_proof_authority_input_error(
                            "module.functions.instructions",
                            format!(
                                "{location} uses Alloca without an internally bound extent, pointee-type, and alignment derivation (ty={ty}, reason={})",
                                reason.kind
                             ),
                        ));
                    }
                    trust_ir::Inst::DialectOp(_) => {
                        return Err(native_bundle_proof_authority_input_error(
                            "module.functions.instructions",
                            format!(
                                "{location} uses a public dialect operation without a private producer-semantics capability"
                            ),
                        ));
                    }
                    // Beyond integer Trunc/ZExt/SExt, the ONLY other admitted casts
                    // are the exact pointer bit-identity shapes enumerated by
                    // `trust_mc_trust_bmc::proof_grade_cast_is_admissible` (kept in
                    // lockstep with the translator's value-preserving legs): thin
                    // pointer identities, single-pointer-newtype wrap/unwrap, the
                    // usize<->NonNull `fmt::Arguments` packing, same-type fat
                    // reinterprets, fat->thin data-lane, and thin `PtrToInt`.
                    trust_ir::Inst::Cast { op, src_ty, dst_ty, .. }
                        if (!matches!(
                            op,
                            trust_ir::inst::CastOp::Trunc
                                | trust_ir::inst::CastOp::ZExt
                                | trust_ir::inst::CastOp::SExt
                        ) || !src_ty.is_integer()
                            || !dst_ty.is_integer())
                            && !trust_mc_trust_bmc::proof_grade_cast_is_admissible(
                                &bundle.module,
                                *op,
                                src_ty,
                                dst_ty,
                            ) =>
                    {
                        return Err(native_bundle_proof_authority_input_error(
                            "module.functions.instructions",
                            format!(
                                "{location} uses cast {op:?} from {src_ty} to {dst_ty}; proof authority currently admits only modeled integer Trunc/ZExt/SExt casts and exact pointer bit-identity casts"
                            ),
                        ));
                    }
                    trust_ir::Inst::Call { callee, .. } => {
                        let Some(callee_function) = bundle.module.function_by_id(*callee) else {
                            return Err(native_bundle_proof_authority_input_error(
                                "module.functions.instructions",
                                format!("{location} references missing callee #{}", callee.index()),
                            ));
                        };
                        if is_name_only_wrapping_intrinsic(&callee_function.name) {
                            return Err(native_bundle_proof_authority_input_error(
                                "module.functions.instructions",
                                format!(
                                    "{location} calls `{}`; name-only wrapping-intrinsic substitution is diagnostic-only",
                                    callee_function.name
                                ),
                            ));
                        }
                        pending.push(*callee);
                    }
                    _ => {}
                }
            }
        }
    }

    Ok(())
}

#[cfg(feature = "native-trust-ir-bundle")]
fn native_bundle_proof_authority_input_error(
    field_suffix: &str,
    detail: String,
) -> NativeSolveError {
    NativeSolveError::InvalidInput {
        field: format!("native_trust_ir_bundle.{field_suffix}"),
        detail,
    }
}

#[cfg(feature = "native-trust-ir-bundle")]
fn is_name_only_wrapping_intrinsic(name: &str) -> bool {
    matches!(name.rsplit("::").next(), Some("wrapping_add" | "wrapping_sub" | "wrapping_mul"))
}

#[cfg(feature = "native-trust-ir-bundle")]
fn disabled_native_bundle_safety_checks(
    options: &trust_mc_trust_bmc::TranslateOptions,
) -> Vec<&'static str> {
    // Exhaustive destructuring is intentional: adding any translation option
    // forces this proof-semantics audit to be revisited at compile time.
    let trust_mc_trust_bmc::TranslateOptions {
        check_signed_overflow,
        check_unsigned_overflow,
        check_div_by_zero,
        check_memory_bounds,
        logic: _,
        timeout_ms: _,
        // AUDITED, deliberately NOT reported as a disabled check.
        //
        // This list names options that WEAKEN the proof by switching a safety
        // check off. `narrow_to_target_block` switches nothing off: it scopes an
        // unsupported construct's unconditional error rule to the obligations
        // that construct can actually reach (entry ->* site ->* target), instead
        // of letting one unmodeled construct sink every obligation in the
        // function. The exclusion fires only when the site is PROVABLY off every
        // entry->target path; site == target, an unknown terminator, an absent
        // block, or unprovable reachability in either direction all keep the
        // rule. It can therefore only drop a rule irrelevant to the obligation
        // being asked about — never mask a violation, never mint a proof.
        narrow_to_target_block: _,
        // AUDITED, deliberately NOT reported as a disabled check.
        //
        // The call-summary census is purely observational: it appends one row
        // per `Inst::Call` site to `ChcTranslationOutput::call_summary_census`
        // saying whether the modular summary succeeded and, when it did not,
        // which labelled exit declined. It emits no rule, suppresses no rule,
        // and is read by no verdict, gate or acceptance check. Turning it on
        // cannot weaken a proof; turning it off cannot strengthen one.
        collect_call_summary_census: _,
    } = options;
    let mut disabled = Vec::new();
    if !*check_signed_overflow {
        disabled.push("check_signed_overflow");
    }
    if !*check_unsigned_overflow {
        disabled.push("check_unsigned_overflow");
    }
    if !*check_div_by_zero {
        disabled.push("check_div_by_zero");
    }
    if !*check_memory_bounds {
        disabled.push("check_memory_bounds");
    }
    disabled
}

/// Classify one per-request native proof-grade solve error (Trust T3).
///
/// `true` = an honest per-request "the solver did not prove this request"
/// outcome, collected into
/// [`NativeTrustIrChcPdrBundleEvidence::not_proved`] instead of failing the
/// whole bundle:
/// - [`NativeSolveError::ProofGradeRejected`]: the solve ran and returned a
///   verdict, but proof-grade admission refused it (ay-chc unknown,
///   refutation/counterexample, diagnostic-only or metadata-free evidence).
/// - [`NativeSolveError::SolverFailed`]: the native solver failed on this
///   validated request only.
/// - [`NativeSolveError::Unsupported`]: this request's shape cannot be solved
///   on this path (e.g. a native-metadata obligation with no Horn rule
///   deriving its query target, or an option combination the native path does
///   not implement) — fail-closed per request, honestly reported per row.
///
/// `false` = structural, whole-bundle `Err` (fail-closed):
/// - [`NativeSolveError::InvalidInput`]: a malformed request/obligation or a
///   binding mismatch indicates corruption, not solver inconclusiveness.
///
/// Collected rows never carry proof evidence, so this classification can only
/// change diagnostics — never a proof verdict. The match is deliberately
/// exhaustive: adding a `NativeSolveError` variant must force an explicit
/// collect-vs-fatal decision here (fail-closed by construction).
#[cfg(feature = "native-trust-ir-bundle")]
fn native_solve_error_is_per_request_not_proved(error: &NativeSolveError) -> bool {
    match error {
        NativeSolveError::ProofGradeRejected { .. }
        | NativeSolveError::SolverFailed { .. }
        | NativeSolveError::Unsupported(_) => true,
        NativeSolveError::InvalidInput { .. } => false,
    }
}

#[cfg(feature = "native-trust-ir-bundle")]
fn native_trust_ir_bundle_error(
    error: trust_mc_trust_bmc::NativeTrustMcBundleError,
) -> NativeSolveError {
    NativeSolveError::InvalidInput {
        field: String::from("native_trust_ir_bundle"),
        detail: error.to_string(),
    }
}

#[cfg(feature = "native-trust-ir-bundle")]
fn validate_native_trust_ir_transport_binding(
    translated: &trust_mc_trust_bmc::NativeTrustMcChcPdrObligation,
    transport: &NativeTypedChcPdrProofTransport,
) -> NativeSolveResult<()> {
    if transport.native_id != translated.obligation.obligation_id {
        return Err(NativeSolveError::InvalidInput {
            field: String::from("native_trust_ir_bundle.evidence.native_id"),
            detail: format!(
                "transport native id `{}` does not match translated obligation id `{}`",
                transport.native_id, translated.obligation.obligation_id
            ),
        });
    }
    if transport.request_id != translated.request_id.index() {
        return Err(NativeSolveError::InvalidInput {
            field: String::from("native_trust_ir_bundle.evidence.request_id"),
            detail: format!(
                "transport request id {} does not match translated request id {}",
                transport.request_id,
                translated.request_id.index()
            ),
        });
    }

    let expected_proof_id = match translated.obligations.as_slice() {
        [only] => Some(only.index()),
        _ => None,
    };
    if transport.proof_id != expected_proof_id {
        return Err(NativeSolveError::InvalidInput {
            field: String::from("native_trust_ir_bundle.evidence.proof_id"),
            detail: format!(
                "transport proof id {:?} does not match translated proof ids {:?}",
                transport.proof_id,
                translated.obligations.iter().map(|id| id.index()).collect::<Vec<_>>()
            ),
        });
    }

    Ok(())
}

/// Native facade operation that failed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum NativeOperation {
    /// Solving a native trust-mc artifact.
    Solve,
}

impl NativeOperation {
    fn as_str(self) -> &'static str {
        match self {
            Self::Solve => "solve",
        }
    }
}

/// Structured unsupported-operation payload.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct NativeSolveUnsupported {
    /// Operation that is not implemented yet.
    pub operation: NativeOperation,
    /// Stable machine-readable reason.
    pub reason: String,
    /// Human-readable detail.
    pub detail: String,
}

/// Errors returned by the native driver facade.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum NativeSolveError {
    /// The API shape exists, but the implementation is not lifted yet.
    Unsupported(NativeSolveUnsupported),
    /// Request validation failed before solving.
    InvalidInput { field: String, detail: String },
    /// The native solver failed after request validation.
    SolverFailed { reason: String },
    /// The solver returned a verdict, but it was not admissible as native proof-grade evidence.
    ProofGradeRejected { rejection: trust_mc_core::ProofEvidenceRejection },
}

impl fmt::Display for NativeSolveError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Unsupported(unsupported) => write!(
                f,
                "native {} is unsupported: {} ({})",
                unsupported.operation.as_str(),
                unsupported.reason,
                unsupported.detail
            ),
            Self::InvalidInput { field, detail } => {
                write!(f, "invalid native solve input `{field}`: {detail}")
            }
            Self::SolverFailed { reason } => write!(f, "native solver failed: {reason}"),
            Self::ProofGradeRejected { rejection } => {
                write!(f, "native proof-grade evidence rejected: {rejection}")
            }
        }
    }
}

impl Error for NativeSolveError {}

#[derive(Debug, Deserialize)]
struct SmtLibBmcPayload {
    format: String,
    version: u32,
    kind: String,
    obligation_id: String,
    function_name: String,
    script: String,
    provenance: SmtLibBmcProvenance,
}

#[derive(Debug, Deserialize)]
struct SmtLibBmcProvenance {
    proof_mode: String,
    bmc_depth: Option<u32>,
    finite_acyclic: bool,
    producer: String,
}

/// Solve a native trust-mc verification artifact.
///
/// SMT-LIB BMC payloads produced by the native compiler API are solved with the
/// in-process AY executor. CHC/PDR and proof-certificate production remain
/// explicitly unsupported through this boundary.
pub fn solve_native(request: NativeSolveRequest) -> NativeSolveResult<NativeSolvedArtifact> {
    validate_solve_request(&request)?;
    if request.produce_proof_certificate {
        return Err(NativeSolveError::Unsupported(NativeSolveUnsupported {
            operation: NativeOperation::Solve,
            reason: String::from("proof_certificate_not_supported"),
            detail: String::from(
                "native SMT-LIB BMC solving does not yet export proof certificates",
            ),
        }));
    }

    match request.artifact.kind {
        NativeVcKind::Bmc => solve_smtlib_bmc(request),
        NativeVcKind::Chc => Err(NativeSolveError::Unsupported(NativeSolveUnsupported {
            operation: NativeOperation::Solve,
            reason: String::from("chc_native_payload_not_supported"),
            detail: String::from("the native driver currently solves only SMT-LIB BMC payloads"),
        })),
    }
}

/// Solve a typed MIR-derived CHC/PDR obligation.
///
/// This is the direct library boundary for tRust-style callers that already
/// have a typed `trust-mc_core::ChcVc`. It deliberately does not require or produce
/// caller-supplied SMT-LIB proof metadata. The typed VC is validated, lowered to
/// the native ay-chc problem API, and solved with a verified native CHC/PDR
/// engine.
pub fn solve_typed_chc_pdr(
    request: trust_mc_core::ChcPdrSolveRequest,
) -> NativeSolveResult<trust_mc_core::ChcPdrSolveOutcome> {
    request.obligation.validate().map_err(|err| NativeSolveError::InvalidInput {
        field: String::from("request.obligation"),
        detail: err.to_string(),
    })?;

    if request.options.produce_proof_certificate {
        return Err(NativeSolveError::Unsupported(NativeSolveUnsupported {
            operation: NativeOperation::Solve,
            reason: String::from("proof_certificate_not_supported"),
            detail: String::from(
                "typed CHC/PDR solving does not yet export standalone proof certificates",
            ),
        }));
    }

    if typed_chc_pdr_route(&request.obligation) == TypedChcPdrRoute::TriviallySafe {
        return Ok(typed_trivial_safe_outcome(&request.obligation));
    }

    solve_typed_chc_pdr_with_ay(request)
}

/// Derive the exact normalized input used by native typed CHC/PDR verification.
///
/// This is intentionally fallible: non-trivial obligations are lowered through
/// the same typed AY lowering path as the solver, and unsupported typed input is
/// rejected instead of being assigned a synthetic or proof-derived identity.
/// Route selection is internal so consumers cannot accidentally normalize for a
/// route different from the one production verification will use.
pub fn normalized_typed_chc_pdr_input(
    obligation: &trust_mc_core::MirChcPdrObligation,
) -> NativeSolveResult<NativeTypedChcPdrNormalizedInput> {
    obligation.validate().map_err(|err| NativeSolveError::InvalidInput {
        field: String::from("request.obligation"),
        detail: err.to_string(),
    })?;

    Ok(prepare_validated_typed_chc_pdr_input(obligation)?.normalized)
}

/// Canonical semantic-configuration serialization for one typed CHC/PDR solve.
///
/// This is the deterministic byte string whose SHA-256 is bound into a
/// [`trust_mc_core::ChcPdrRefutationWitness`]. It covers exactly the
/// configuration that selects the solve's semantics: the requested engine, the
/// selected route, and the identity of the exact-or-reject typed lowering
/// discipline. Resource-only options (timeout, artifact/certificate
/// production) are deliberately excluded: they cannot change what the encoded
/// formula means or what a counterexample refutes.
///
/// The function is public so consumers can recompute the digest independently
/// from their OWN engine selection and their OWN
/// [`normalized_typed_chc_pdr_input`]-derived route, instead of trusting a
/// producer-supplied digest.
#[must_use]
pub fn typed_chc_pdr_semantic_config(
    engine: trust_mc_core::ChcPdrEngine,
    route: TypedChcPdrRoute,
) -> String {
    format!(
        "{{\"schema\":\"trust_mc.typed-chc-pdr-semantic-config/v1\",\"engine\":\"{engine:?}\",\
         \"route\":\"{route:?}\",\"typed_lowering\":\"typed-chc-ay/exact-or-reject/v1\"}}"
    )
}

/// Lowercase-hex SHA-256 of [`typed_chc_pdr_semantic_config`].
#[must_use]
pub fn typed_chc_pdr_semantic_config_sha256(
    engine: trust_mc_core::ChcPdrEngine,
    route: TypedChcPdrRoute,
) -> String {
    trust_mc_core::EvidenceHash::sha256_bytes(
        typed_chc_pdr_semantic_config(engine, route).as_bytes(),
    )
    .value
}

#[cfg(feature = "ay-chc-native")]
const MAX_REFUTATION_REPLAY_PAYLOAD_BYTES: usize = 16 * 1024 * 1024;
#[cfg(feature = "ay-chc-native")]
const MAX_REFUTATION_REPLAY_RELATIONS: usize = 65_536;
#[cfg(feature = "ay-chc-native")]
const MAX_REFUTATION_REPLAY_RULES: usize = 262_144;

#[cfg(feature = "ay-chc-native")]
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct DirectSmtRefutationReplayPayload {
    schema: String,
    source: String,
    #[serde(default)]
    unroll_k: Option<u32>,
    derivation_clause_indices: Vec<u64>,
    witness_model: serde_json::Value,
}

/// Independently replay a direct-SMT typed-CHC refutation against a freshly
/// lowered copy of the consumer's retained obligation.
///
/// This is the refutation-side authority boundary for compiler consumers.  It
/// does not accept the producer's verification class, digests, concreteness
/// attestation, JSON shape, trace, or model by assertion.  It validates the
/// retained typed obligation, re-runs the exact-or-reject lowering, recomputes
/// the normalized-input and semantic-configuration digests, requires exact
/// zero-loss accounting, rebuilds the exact acyclic problem (including the
/// declared bounded unroll when present), and SMT-checks the supplied total,
/// sort-exact model on the supplied clause trace.  Any unsupported class,
/// malformed or extra payload field, budget breach, path mismatch, model
/// mismatch, or undecided replay returns an error; callers must keep the row
/// Unknown.
///
/// This API deliberately declines `AyChcReplayVerified`: its current payload
/// contains only a debug rendering, not the typed trace needed for independent
/// consumer replay.
#[cfg(feature = "ay-chc-native")]
pub fn independently_replay_typed_chc_pdr_refutation_witness(
    obligation: &trust_mc_core::MirChcPdrObligation,
    expected_engine: trust_mc_core::ChcPdrEngine,
    witness: &trust_mc_core::ChcPdrRefutationWitness,
) -> NativeSolveResult<String> {
    let reject = |detail: String| NativeSolveError::InvalidInput {
        field: "refutation_witness".to_string(),
        detail,
    };
    obligation.validate().map_err(|error| NativeSolveError::InvalidInput {
        field: "obligation".to_string(),
        detail: error.to_string(),
    })?;
    if witness.obligation_id != obligation.obligation_id {
        return Err(reject(format!(
            "witness obligation `{}` differs from retained obligation `{}`",
            witness.obligation_id, obligation.obligation_id
        )));
    }
    if !witness.concreteness.is_exact_with_zero_counts() {
        return Err(reject(
            "witness does not carry an all-zero exact-encoding attestation".to_string(),
        ));
    }
    if witness.counterexample_json.len() > MAX_REFUTATION_REPLAY_PAYLOAD_BYTES {
        return Err(reject(format!(
            "counterexample payload has {} bytes, above the replay budget",
            witness.counterexample_json.len()
        )));
    }
    if obligation.vc.relations.len() > MAX_REFUTATION_REPLAY_RELATIONS
        || obligation.vc.rules.len() > MAX_REFUTATION_REPLAY_RULES
    {
        return Err(reject(format!(
            "retained obligation has {} relations and {} rules, above the replay budget",
            obligation.vc.relations.len(),
            obligation.vc.rules.len()
        )));
    }

    let prepared = prepare_validated_typed_chc_pdr_input(obligation)?;
    if prepared.normalized.route != TypedChcPdrRoute::PdrProof {
        return Err(reject(
            "retained obligation does not select the typed CHC/PDR route".to_string(),
        ));
    }
    if witness.encoded_formula_sha256 != prepared.normalized.normalized_input_hash.value {
        return Err(reject(
            "encoded-formula digest differs from the fresh exact lowering".to_string(),
        ));
    }
    let semantic_config =
        typed_chc_pdr_semantic_config_sha256(expected_engine, prepared.normalized.route);
    if witness.semantic_config_sha256 != semantic_config {
        return Err(reject(
            "semantic-configuration digest differs from the consumer configuration".to_string(),
        ));
    }
    if !prepared.lowering.is_some_and(typed_chc_ay::TypedChcLoweringAccounting::is_exact) {
        return Err(reject(
            "fresh typed lowering did not retain exact all-zero accounting".to_string(),
        ));
    }
    let problem = prepared
        .problem
        .ok_or_else(|| reject("fresh typed lowering retained no CHC problem".to_string()))?;

    let payload: DirectSmtRefutationReplayPayload =
        serde_json::from_str(&witness.counterexample_json).map_err(|error| {
            reject(format!("counterexample payload does not match the strict JSON schema: {error}"))
        })?;
    if payload.schema != "trust_mc.typed-chc-pdr-counterexample/v1" {
        return Err(reject(format!("unsupported counterexample schema `{}`", payload.schema)));
    }
    let direct_witness = crate::direct_smt_cex::AcyclicUnsafeWitness {
        model: payload.witness_model,
        derivation_clause_indices: payload.derivation_clause_indices,
    };

    let (replay_problem, summary) = match witness.verification {
        trust_mc_core::ChcPdrCexVerification::DirectSmtModel => {
            if payload.source != "direct-smt-acyclic-error-derivation" || payload.unroll_k.is_some()
            {
                return Err(reject(
                    "direct-SMT payload source or unroll budget does not match its proof class"
                        .to_string(),
                ));
            }
            if problem.has_cycles() {
                return Err(reject(
                    "direct-SMT proof class was attached to a cyclic fresh problem".to_string(),
                ));
            }
            (problem, "fresh direct-SMT acyclic derivation and exact model replay".to_string())
        }
        trust_mc_core::ChcPdrCexVerification::BoundedUnrollDirectSmtModel { k } => {
            let k = u32::try_from(k)
                .map_err(|_| reject(format!("bounded-unroll budget {k} is not representable")))?;
            if !bounded_unroll::BOUNDED_UNROLL_K_LADDER.contains(&k) {
                return Err(reject(format!(
                    "bounded-unroll budget {k} is outside the exact production ladder"
                )));
            }
            if payload.source != "direct-smt-bounded-unroll-error-derivation"
                || payload.unroll_k != Some(k)
            {
                return Err(reject(
                    "bounded-unroll payload source or budget does not match its proof class"
                        .to_string(),
                ));
            }
            if obligation.kind != trust_mc_core::MirObligationKind::Assertion
                || !obligation
                    .native_metadata
                    .as_ref()
                    .is_some_and(|metadata| metadata.structural_reachability_complete)
                || fail_closed_lowering_sites(obligation) != 0
            {
                return Err(reject(
                    "retained obligation is outside the exact bounded-unroll refutation lane"
                        .to_string(),
                ));
            }
            let unrolled = bounded_unroll::bounded_unroll_chc_for_refutation(&problem, k)
                .ok_or_else(|| {
                    reject(
                        "fresh problem cannot be rebuilt as the declared exact bounded unroll"
                            .to_string(),
                    )
                })?;
            (
                unrolled.problem,
                format!("fresh k={k} bounded-unroll derivation and exact model replay"),
            )
        }
        ref other => {
            return Err(reject(format!(
                "counterexample verification kind {other:?} has no independent replay surface"
            )));
        }
    };

    crate::direct_smt_cex::replay_acyclic_direct_smt_witness(&replay_problem, &direct_witness)
        .map_err(reject)?;
    Ok(summary)
}

/// Mint a refutation witness for a typed CHC/PDR `Refuted` verdict, or `None`
/// when the concreteness condition does not hold.
///
/// The witness is attached ONLY when the real lowering accounting reports an
/// exact encoding (zero translation drops, zero havocs of any kind, zero
/// Undef-diagnostic havocs). Sound-havoc is deliberately NOT excluded from the
/// gate: sound over-approximation is sound for proofs but makes refutations
/// potentially spurious, so any nonzero count suppresses the witness and the
/// outcome degrades to today's witnessless `Refuted`.
#[cfg(feature = "ay-chc-native")]
fn typed_chc_pdr_refutation_witness(
    obligation_id: &str,
    normalized_input_hash: &trust_mc_core::EvidenceHash,
    engine: trust_mc_core::ChcPdrEngine,
    route: TypedChcPdrRoute,
    counterexample: &serde_json::Value,
    verification: trust_mc_core::ChcPdrCexVerification,
    lowering: Option<typed_chc_ay::TypedChcLoweringAccounting>,
) -> Option<Box<trust_mc_core::ChcPdrRefutationWitness>> {
    // No accounting means nothing was lowered on this route; refutations
    // cannot occur there, but stay fail-closed regardless.
    let lowering = lowering?;
    if !lowering.is_exact() {
        return None;
    }
    Some(Box::new(trust_mc_core::ChcPdrRefutationWitness::new(
        obligation_id,
        normalized_input_hash.value.clone(),
        typed_chc_pdr_semantic_config_sha256(engine, route),
        counterexample.to_string(),
        verification,
        trust_mc_core::ChcPdrEncodingConcreteness::ExactEncoding {
            translation_drops: lowering.translation_drops,
            havocs: lowering.havocs,
            undef_diagnostic_havocs: lowering.undef_diagnostic_havocs,
        },
    )))
}

/// Bounded-unroll REFUTATION-ONLY escalation for cyclic typed CHC problems.
///
/// Runs only when every proof-seeking lane has already ended Unknown on this
/// obligation (the caller invokes it from the `VerifiedChcResult::Unknown`
/// arm), and only for the L0 safety class (`MirObligationKind::Assertion` —
/// panic-freedom / overflow / bounds), never for invariant/protocol
/// obligations. It climbs `BOUNDED_UNROLL_K_LADDER`, building the acyclic
/// k-bounded under-approximation of `problem` and asking the existing
/// direct-SMT composer for a concrete derivation of the query target.
///
/// SOUNDNESS (load-bearing, in order):
/// - Refutation-only BY TYPE: the only success value this function can build
///   is `Refuted { witness }` + `FullVerificationVerdict::Failed`. A `Safe`
///   decision on a truncated unroll means nothing (deeper traces are
///   unrepresented) and is deliberately indistinguishable from `Inconclusive`
///   here: both fall through to the next rung / `None`.
/// - A found witness is REAL: every unrolled clause is one original clause
///   with predicates renamed per level, so the satisfiable derivation
///   projects (by erasing levels) onto a derivation of the ORIGINAL problem.
///   That is why the minted witness binds `normalized_input_hash` of the
///   ORIGINAL problem — the digest the consumer independently recomputes.
/// - Same fail-closed gates as the existing refutation arms: a nonzero
///   fail-closed-lowering-site count discards the model (the derivation may
///   pass through an admission-failure error rule, not a program trap), and
///   witness minting requires the exact all-zero lowering accounting
///   (`typed_chc_pdr_refutation_witness` declines otherwise).
/// - The provenance rides the witness payload itself
///   (`ChcPdrCexVerification::BoundedUnrollDirectSmtModel { k }` plus the
///   `unroll_k` field of the counterexample artifact), never a detachable
///   transport flag, so consumers that do not recognize the class fail closed.
#[cfg(feature = "ay-chc-native")]
#[allow(clippy::too_many_arguments)] // mirrors the sibling lane helpers' seams
fn try_bounded_unroll_refutation_lane(
    problem: &ay_chc::ChcProblem,
    request: &trust_mc_core::ChcPdrSolveRequest,
    stats: trust_mc_core::ChcPdrStats,
    normalized_input_hash: &trust_mc_core::EvidenceHash,
    route: TypedChcPdrRoute,
    cache_key: &trust_mc_core::FullVerificationCacheKey,
    artifact_directory: &str,
    lowering: Option<typed_chc_ay::TypedChcLoweringAccounting>,
    watchdog_ceiling: Duration,
) -> Option<TypedChcPdrFullVerification> {
    try_bounded_unroll_refutation_lane_with_ladder(
        problem,
        request,
        stats,
        normalized_input_hash,
        route,
        cache_key,
        artifact_directory,
        lowering,
        watchdog_ceiling,
        &bounded_unroll::BOUNDED_UNROLL_K_LADDER,
    )
}

/// Ladder-parameterized body of [`try_bounded_unroll_refutation_lane`], split
/// out so tests can pin the beyond-budget behavior (a violation deeper than
/// every rung must stay Unknown) without paying for the production ladder's
/// deepest unroll. Production always passes `BOUNDED_UNROLL_K_LADDER`.
#[cfg(feature = "ay-chc-native")]
#[allow(clippy::too_many_arguments)] // mirrors the sibling lane helpers' seams
fn try_bounded_unroll_refutation_lane_with_ladder(
    problem: &ay_chc::ChcProblem,
    request: &trust_mc_core::ChcPdrSolveRequest,
    stats: trust_mc_core::ChcPdrStats,
    normalized_input_hash: &trust_mc_core::EvidenceHash,
    route: TypedChcPdrRoute,
    cache_key: &trust_mc_core::FullVerificationCacheKey,
    artifact_directory: &str,
    lowering: Option<typed_chc_ay::TypedChcLoweringAccounting>,
    watchdog_ceiling: Duration,
    ladder: &[u32],
) -> Option<TypedChcPdrFullVerification> {
    // L0 safety obligations only. Invariant/protocol/termination classes are
    // not the panic-reachability question this lane answers.
    if request.obligation.kind != trust_mc_core::MirObligationKind::Assertion {
        return None;
    }
    // Only the native-bundle translator's complete-by-construction lowering
    // (`trust_mc_chc_pdr_obligations_from_native_bundle`, which stamps this
    // marker) is in this lane's modeled domain: its per-site error edges and
    // grounded relational encoding are what the grounding gate and the
    // level-erasure projection argument reason about. A control-only
    // structural reachability CHC — e.g. the compiler's whole-CFG
    // default-function admission formula (nullary block relations, no data
    // constraints) — is a sound over-approximation for PROOFS whose
    // derivations are mere control-feasibility, so a refutation minted from
    // it would be spurious. The marker itself is diagnostic (forgeable), but
    // it is only the eligibility gate here: the consumer independently
    // recomputes the encoded-formula digest from its OWN fresh native-bundle
    // translation (which stamps the marker itself), so a forged marker on a
    // foreign encoding fails that digest binding downstream.
    if !request
        .obligation
        .native_metadata
        .as_ref()
        .is_some_and(|metadata| metadata.structural_reachability_complete)
    {
        return None;
    }
    // Witness minting below requires the exact accounting anyway; decline
    // before paying for any solve.
    if !lowering.is_some_and(typed_chc_ay::TypedChcLoweringAccounting::is_exact) {
        return None;
    }
    // A derivation that may pass through a fail-closed lowering error rule is
    // an admission failure, not a program trap (same gate as the direct and
    // PDR refutation arms).
    if fail_closed_lowering_sites(&request.obligation) > 0 {
        return None;
    }
    if !problem.has_cycles() {
        return None;
    }

    // One shared wall-clock budget across the whole ladder, so escalation
    // rungs cannot multiply the caller's ceiling.
    let lane_deadline = std::time::Instant::now().checked_add(watchdog_ceiling)?;
    for &k in ladder {
        let remaining = lane_deadline.saturating_duration_since(std::time::Instant::now());
        if remaining.is_zero() {
            return None;
        }
        let unrolled = bounded_unroll::bounded_unroll_chc_for_refutation(problem, k)?;
        // Bind the provenance to the budget the unroll actually represents,
        // not the ladder rung requested.
        let k = unrolled.k;
        let decision_problem = unrolled.problem;
        let decision = run_native_solve_within_deadline(remaining, move || {
            crate::direct_smt_cex::acyclic_direct_smt_decision(&decision_problem)
        })?;
        let direct_witness = match decision {
            crate::direct_smt_cex::AcyclicDecision::Unsafe(witness) => witness,
            // `Safe` on a k-truncated under-approximation proves NOTHING about
            // deeper traces; `Inconclusive` decided nothing. Both only mean
            // "no witness at this budget" — climb the ladder.
            crate::direct_smt_cex::AcyclicDecision::Safe
            | crate::direct_smt_cex::AcyclicDecision::Inconclusive => continue,
        };

        let counterexample = serde_json::json!({
            "schema": "trust_mc.typed-chc-pdr-counterexample/v1",
            "source": "direct-smt-bounded-unroll-error-derivation",
            "unroll_k": k,
            "derivation_clause_indices": direct_witness.derivation_clause_indices,
            "witness_model": direct_witness.model,
        });
        // Bind the witness to the ORIGINAL problem's normalized input: the
        // unrolled derivation projects onto the original problem (see the
        // module docs), and the original digest is what the consumer
        // independently recomputes from its own retained request.
        let witness = typed_chc_pdr_refutation_witness(
            &request.obligation.obligation_id,
            normalized_input_hash,
            request.options.engine,
            route,
            &counterexample,
            trust_mc_core::ChcPdrCexVerification::BoundedUnrollDirectSmtModel { k: u64::from(k) },
            lowering,
        )?;
        let outcome = trust_mc_core::ChcPdrSolveOutcome::refuted_with_witness(
            request.obligation.obligation_id.clone(),
            witness,
            stats,
        )
        .with_diagnostic(format!(
            "direct SMT confirmed a satisfiable typed query fact on a k={k} bounded unroll; \
             refuted obligation via an error derivation that projects onto the original \
             cyclic problem"
        ));
        let verdict = trust_mc_core::FullVerificationVerdict::Failed {
            counterexample_artifacts: vec![trust_mc_core::FullVerificationArtifact::from_bytes(
                trust_mc_core::FullVerificationArtifactKind::CounterexampleTrace,
                format!(
                    "trust_mc://typed-chc/{}/counterexample.json",
                    request.obligation.obligation_id
                ),
                &json_bytes(&counterexample),
            )],
        };
        return Some(TypedChcPdrFullVerification {
            route,
            cache_key: cache_key.clone(),
            artifact_directory: artifact_directory.to_string(),
            outcome,
            verdict,
            private_native_proof_seal: None,
        });
    }
    None
}

fn prepare_validated_typed_chc_pdr_input(
    obligation: &trust_mc_core::MirChcPdrObligation,
) -> NativeSolveResult<PreparedTypedChcPdrInput> {
    let route = typed_chc_pdr_route(obligation);
    prepare_validated_typed_chc_pdr_input_for_route(obligation, route)
}

fn trivial_typed_chc_pdr_normalized_input(
    obligation: &trust_mc_core::MirChcPdrObligation,
) -> NativeSolveResult<String> {
    String::from_utf8(typed_obligation_set_bytes(obligation, TypedChcPdrRoute::TriviallySafe))
        .map_err(|err| NativeSolveError::SolverFailed {
            reason: format!(
                "typed CHC/PDR obligation normalization produced non-UTF-8 JSON: {err}"
            ),
        })
}

fn typed_chc_pdr_route(obligation: &trust_mc_core::MirChcPdrObligation) -> TypedChcPdrRoute {
    if obligation.is_trivially_safe() {
        TypedChcPdrRoute::TriviallySafe
    } else {
        TypedChcPdrRoute::PdrProof
    }
}

#[cfg(feature = "ay-chc-native")]
fn prepare_validated_typed_chc_pdr_input_for_route(
    obligation: &trust_mc_core::MirChcPdrObligation,
    route: TypedChcPdrRoute,
) -> NativeSolveResult<PreparedTypedChcPdrInput> {
    let (normalized_input, problem, lowering) = match route {
        TypedChcPdrRoute::TriviallySafe => {
            (trivial_typed_chc_pdr_normalized_input(obligation)?, None, None)
        }
        TypedChcPdrRoute::PdrProof => {
            let (problem, lowering) = typed_chc_ay::lower_obligation_with_accounting(obligation)?;
            let normalized_input = ay_encode::normalized_chc_input(&problem);
            (normalized_input, Some(problem), Some(lowering))
        }
    };
    Ok(PreparedTypedChcPdrInput {
        normalized: native_typed_chc_pdr_normalized_input(obligation, route, normalized_input),
        problem,
        lowering,
    })
}

#[cfg(not(feature = "ay-chc-native"))]
fn prepare_validated_typed_chc_pdr_input_for_route(
    obligation: &trust_mc_core::MirChcPdrObligation,
    route: TypedChcPdrRoute,
) -> NativeSolveResult<PreparedTypedChcPdrInput> {
    match route {
        TypedChcPdrRoute::TriviallySafe => Ok(PreparedTypedChcPdrInput {
            normalized: native_typed_chc_pdr_normalized_input(
                obligation,
                route,
                trivial_typed_chc_pdr_normalized_input(obligation)?,
            ),
        }),
        TypedChcPdrRoute::PdrProof => Err(NativeSolveError::Unsupported(NativeSolveUnsupported {
            operation: NativeOperation::Solve,
            reason: String::from("ay_chc_native_feature_disabled"),
            detail: String::from("typed CHC/PDR normalization requires the ay-chc-native feature"),
        })),
    }
}

/// Solve a typed MIR-derived CHC/PDR obligation and return full-verification evidence.
///
/// This is the driver-native proof boundary for callers that already hold typed
/// MIR/trust_ir obligations. Route selection uses the typed `ChcVc` query target and
/// Horn rule heads, not SMT-LIB classification or text scraping.
pub fn solve_typed_chc_pdr_full_verification(
    request: trust_mc_core::ChcPdrSolveRequest,
) -> NativeSolveResult<TypedChcPdrFullVerification> {
    request.obligation.validate().map_err(|err| NativeSolveError::InvalidInput {
        field: String::from("request.obligation"),
        detail: err.to_string(),
    })?;

    if request.options.produce_proof_certificate {
        return Err(NativeSolveError::Unsupported(NativeSolveUnsupported {
            operation: NativeOperation::Solve,
            reason: String::from("proof_certificate_not_supported"),
            detail: String::from(
                "typed CHC/PDR solving does not yet export standalone proof certificates",
            ),
        }));
    }

    // Prepare once: the returned identity and the exact lowered problem remain
    // coupled through the solve, so evidence cannot describe a different
    // lowering than the one the engine consumed.
    let prepared = prepare_validated_typed_chc_pdr_input(&request.obligation)?;
    let normalized = &prepared.normalized;

    // DEBUG (env-gated): dump the typed CHC + classification so the real
    // modulo_unreachable / ?-payload obligations can be inspected offline.
    if let Ok(dump_path) = std::env::var("TRUST_MC_DUMP_CHC") {
        use std::io::Write as _;
        let oid = request.obligation.obligation_id.clone();
        let trivial = normalized.route == TypedChcPdrRoute::TriviallySafe;
        let has_meta = request.obligation.native_metadata.is_some();
        let qt = request.obligation.query_target();
        let norm = &normalized.normalized_input;
        if let Ok(mut f) = std::fs::OpenOptions::new().create(true).append(true).open(&dump_path) {
            let _ = writeln!(
                f,
                "===== obligation_id={oid} trivially_safe={trivial} has_native_metadata={has_meta} query_target={qt} =====\n{norm}\n"
            );
        }
    }

    if normalized.route == TypedChcPdrRoute::TriviallySafe {
        // A trivially-safe CHC (no rule derives the query target) is credited
        // ONLY when we can certify that "no error rule" means "provably no
        // panic path", not "assertion dropped / translator under-approximated".
        //
        // - Metadata-FREE obligation: the historical typed trivially-safe lane
        //   (hand-built / router-internal), credited as before.
        // - Metadata-BEARING obligation carrying the diagnostic
        //   `structural_reachability_complete` producer claim: eligible to emit
        //   a reject-only candidate, but never authority. Only a private fresh
        //   exact replay or native-bundle translation boundary may later seal
        //   that candidate.
        // - Metadata-BEARING obligation WITHOUT the certificate (external /
        //   lossy / hand-crafted producer, or a compiler MathIr obligation that
        //   omits the field): STAYS fail-closed — a dropped assertion or a
        //   partial translation does not even emit a CHC-validity candidate.
        if let Some(metadata) = request.obligation.native_metadata.as_ref()
            && !metadata.structural_reachability_complete
        {
            return Err(native_trust_ir_trivial_safe_unsupported(&request.obligation));
        }
        let outcome = typed_trivial_safe_outcome(&request.obligation);
        let cache_key =
            typed_full_verification_cache_key(&request.obligation, &request.options, &normalized);
        let artifact_directory = typed_artifact_directory(&cache_key);
        let verdict = typed_trivial_safe_verdict(
            &request.obligation,
            &outcome,
            &cache_key,
            &normalized.normalized_input,
        );
        return Ok(TypedChcPdrFullVerification {
            route: normalized.route,
            cache_key,
            artifact_directory,
            outcome,
            verdict,
            private_native_proof_seal: None,
        });
    }

    solve_typed_chc_pdr_full_with_ay(request, prepared)
}

fn native_trust_ir_trivial_safe_unsupported(
    obligation: &trust_mc_core::MirChcPdrObligation,
) -> NativeSolveError {
    NativeSolveError::Unsupported(NativeSolveUnsupported {
        operation: NativeOperation::Solve,
        reason: String::from("native_trust_ir_trivial_safe_chc_not_proof_grade"),
        detail: format!(
            "native trust_ir obligation `{}` has no Horn rule deriving query target `{}`; \
             release proof paths must fail closed instead of treating a dropped assertion or \
             translator under-approximation as CHC validity",
            obligation.obligation_id,
            obligation.query_target()
        ),
    })
}

/// Reject a source-unbound typed CHC/PDR candidate unless it already carries
/// private in-process native-bundle authority.
///
/// `solve_typed_chc_pdr_full_verification` constructs a fresh generic response
/// with no such seal, so public callers should expect this compatibility helper
/// to fail closed. The authority-minting entry point is
/// `NativeTrustIrChcPdrRunner::solve_bundle_native_proof_grade` (or its explicit
/// live-source-authority variant), where full module validation, conservative
/// semantic preflight, and fresh translation precede sealing. The public verdict
/// remains an untrusted candidate in both paths and cannot be admitted by itself.
pub fn solve_typed_chc_pdr_native_proof_grade(
    request: trust_mc_core::ChcPdrSolveRequest,
) -> NativeSolveResult<TypedChcPdrFullVerification> {
    let solved = solve_typed_chc_pdr_full_verification(request)?;
    solved.privately_authorized_native_candidate()?;
    Ok(solved)
}

fn typed_trivial_safe_outcome(
    obligation: &trust_mc_core::MirChcPdrObligation,
) -> trust_mc_core::ChcPdrSolveOutcome {
    trust_mc_core::ChcPdrSolveOutcome::unknown(
        obligation.obligation_id.clone(),
        trust_mc_core::CHC_VALIDITY_FRESH_CONSUMER_REPLAY_REQUIRED,
        obligation.stats(),
    )
    .with_diagnostic(format!(
        "private structural derivation found no Horn rule for typed CHC query target `{}`; public evidence remains a candidate",
        obligation.query_target()
    ))
}

fn typed_trivial_safe_verdict(
    obligation: &trust_mc_core::MirChcPdrObligation,
    outcome: &trust_mc_core::ChcPdrSolveOutcome,
    cache_key: &trust_mc_core::FullVerificationCacheKey,
    normalized_input: &str,
) -> trust_mc_core::FullVerificationVerdict {
    let stats = outcome.stats;
    let normalized_input_hash =
        trust_mc_core::EvidenceHash::sha256_bytes(normalized_input.as_bytes());
    let transcript = serde_json::json!({
        "schema": "trust_mc.typed-chc-solver-transcript/v1",
        "route": "typed-trivial-safe",
        "obligation_id": &obligation.obligation_id,
        "function_name": &obligation.function_name,
        "query_target": obligation.query_target(),
        "decision": "candidate-safe",
        "reason": "no Horn rule derives the typed query target",
        "normalized_input_sha256": normalized_input_hash.value,
    });
    let transcript_bytes = json_bytes(&transcript);
    let transcript_hash = trust_mc_core::EvidenceHash::sha256_bytes(&transcript_bytes);
    let replay = serde_json::json!({
        "schema": "trust_mc.typed-chc-replay-log/v1",
        "route": "typed-trivial-safe",
        "referenced_solver_transcript": {
            "kind": "solver_transcript",
            "algorithm": transcript_hash.algorithm,
            "value": transcript_hash.value,
        },
        "steps": [
            {
                "check": "typed-rule-head-scan",
                "query_target": obligation.query_target(),
                "matching_head_count": 0
            }
        ],
    });
    let replay_bytes = json_bytes(&replay);
    let replay_hash = trust_mc_core::EvidenceHash::sha256_bytes(&replay_bytes);
    let checked_report = serde_json::json!({
        "schema": "trust_mc.typed-chc-checked-proof-report/v1",
        "accepted_as_candidate": true,
        "accepted_as_proof": false,
        "authoritative": false,
        "private_authority_not_serialized": true,
        "problem_kind": "chc-pdr",
        "proof_kind": "chc-validity",
        "route": "typed-trivial-safe",
        "referenced_solver_transcript": {
            "kind": "solver_transcript",
            "algorithm": transcript_hash.algorithm,
            "value": transcript_hash.value,
        },
        "referenced_replay_log": {
            "kind": "replay_log",
            "algorithm": replay_hash.algorithm,
            "value": replay_hash.value,
        },
        "stats": {
            "relation_count": stats.relation_count,
            "clause_count": stats.clause_count,
        },
    });

    typed_proved_verdict(
        obligation,
        trust_mc_core::ChcPdrProofKind::ChcValidity,
        stats,
        normalized_input,
        cache_key,
        transcript_bytes,
        replay_bytes,
        json_bytes(&checked_report),
        None,
        None,
    )
}

fn typed_proved_verdict(
    obligation: &trust_mc_core::MirChcPdrObligation,
    proof_kind: trust_mc_core::ChcPdrProofKind,
    stats: trust_mc_core::ChcPdrStats,
    normalized_input: &str,
    cache_key: &trust_mc_core::FullVerificationCacheKey,
    solver_transcript_bytes: Vec<u8>,
    replay_log_bytes: Vec<u8>,
    checked_report_bytes: Vec<u8>,
    invariant_count: Option<usize>,
    invariant_model_bytes: Option<Vec<u8>>,
) -> trust_mc_core::FullVerificationVerdict {
    let mut evidence_obligation = trust_mc_core::MirDerivedChcPdrObligation::new(
        obligation.obligation_id.clone(),
        obligation.kind,
        normalized_input,
    );
    if let Some(metadata) = obligation.native_metadata.clone() {
        evidence_obligation = evidence_obligation.with_native_metadata(metadata);
    }
    let base_label = format!("trust_mc://typed-chc/{}", obligation.obligation_id);
    let typed_problem_bytes = typed_chc_problem_artifact_bytes(obligation, normalized_input);
    let proof_result = match (proof_kind, invariant_count, invariant_model_bytes.as_deref()) {
        (
            trust_mc_core::ChcPdrProofKind::PdrInvariant,
            Some(invariant_count),
            Some(invariant_model_bytes),
        ) => trust_mc_core::ChcPdrProofEvidence::try_pdr_invariant_candidate_from_linked_bytes(
            evidence_obligation,
            stats,
            invariant_count,
            (
                &format!("{base_label}/ay-proof-run-replay-transcript.json"),
                &solver_transcript_bytes,
            ),
            (&format!("{base_label}/replay-log.json"), &replay_log_bytes),
            (&format!("{base_label}/checked-proof-report.json"), &checked_report_bytes),
            (&format!("{base_label}/pdr-invariant-model.json"), invariant_model_bytes),
        ),
        (trust_mc_core::ChcPdrProofKind::ChcValidity, None, None) => {
            trust_mc_core::ChcPdrProofEvidence::try_chc_validity_candidate_from_linked_bytes(
                evidence_obligation,
                stats,
                (
                    &format!("{base_label}/ay-proof-run-replay-transcript.json"),
                    &solver_transcript_bytes,
                ),
                (&format!("{base_label}/replay-log.json"), &replay_log_bytes),
                (&format!("{base_label}/checked-proof-report.json"), &checked_report_bytes),
            )
        }
        _ => {
            return trust_mc_core::FullVerificationVerdict::Unknown {
                reason: "typed CHC proof kind and invariant artifact disagree".to_string(),
            };
        }
    };
    let Ok(mut proof) = proof_result else {
        return trust_mc_core::FullVerificationVerdict::Unknown {
            reason: "typed CHC proof artifacts were empty or exceeded the materialization limit"
                .to_string(),
        };
    };
    let Ok(typed_problem_artifact) = trust_mc_core::FullVerificationArtifact::try_from_bytes(
        trust_mc_core::FullVerificationArtifactKind::TypedChcProblem,
        format!("{base_label}/typed-chc-problem.json"),
        &typed_problem_bytes,
    ) else {
        return trust_mc_core::FullVerificationVerdict::Unknown {
            reason: "typed CHC problem exceeded the materialization limit".to_string(),
        };
    };
    proof = proof.with_artifact(typed_problem_artifact);
    proof.metadata.cache_key = Some(cache_key.key.clone());

    trust_mc_core::FullVerificationVerdict::Proved {
        evidence: trust_mc_core::FullProofEvidence::ChcPdr(proof),
    }
}

fn typed_chc_problem_artifact_bytes(
    obligation: &trust_mc_core::MirChcPdrObligation,
    normalized_input: &str,
) -> Vec<u8> {
    let normalized_input_hash =
        trust_mc_core::EvidenceHash::sha256_bytes(normalized_input.as_bytes());
    json_bytes(&serde_json::json!({
        "schema": "trust_mc.typed-chc-problem/v1",
        "source": "trust_mc_core::MirChcPdrObligation",
        "obligation_id": &obligation.obligation_id,
        "function_name": &obligation.function_name,
        "kind": format!("{:?}", obligation.kind),
        "origin": format!("{:?}", obligation.origin),
        "native_metadata": &obligation.native_metadata,
        "query_target": obligation.query_target(),
        "stats": {
            "relation_count": obligation.stats().relation_count,
            "clause_count": obligation.stats().clause_count,
        },
        "normalized_input_sha256": {
            "algorithm": normalized_input_hash.algorithm,
            "value": normalized_input_hash.value,
        },
    }))
}

fn json_bytes(value: &serde_json::Value) -> Vec<u8> {
    // A `serde_json::Value` contains no fallible user serializer and a `Vec<u8>`
    // writer cannot report I/O errors.  Keep one identity encoding instead of
    // silently switching to a second formatter on an impossible error path.
    serde_json::to_vec(value).expect("serializing serde_json::Value to Vec cannot fail")
}

fn native_typed_chc_pdr_normalized_input(
    obligation: &trust_mc_core::MirChcPdrObligation,
    route: TypedChcPdrRoute,
    normalized_input: String,
) -> NativeTypedChcPdrNormalizedInput {
    // `MirDerivedChcPdrObligation` applies this canonicalizer when proof
    // evidence is built.  Apply it before cache/API hashing as well so the
    // pre-solve record, cache key, proof obligation, and materialized artifact
    // all identify byte-for-byte equal input (notably on the JSON trivial route).
    let normalized_input = trust_mc_core::normalize_chc_pdr_input(&normalized_input);
    let normalized_input_hash =
        trust_mc_core::EvidenceHash::sha256_bytes(normalized_input.as_bytes());
    let obligation_set_hash =
        trust_mc_core::EvidenceHash::sha256_bytes(&typed_obligation_set_bytes(obligation, route));
    NativeTypedChcPdrNormalizedInput {
        route,
        normalized_input,
        normalized_input_hash,
        obligation_set_hash,
    }
}

fn typed_full_verification_cache_key(
    obligation: &trust_mc_core::MirChcPdrObligation,
    options: &trust_mc_core::ChcPdrSolveOptions,
    normalized: &NativeTypedChcPdrNormalizedInput,
) -> trust_mc_core::FullVerificationCacheKey {
    trust_mc_core::FullVerificationCacheKey::from_parts(
        trust_mc_core::FullVerificationCacheKeyParts {
            trust_mc_version: env!("CARGO_PKG_VERSION").to_string(),
            trust_mc_commit: env!("TRUST_MC_GIT_SHA").to_string(),
            trust_mc_dirty: env!("TRUST_MC_GIT_DIRTY") == "1",
            ay_solver: ay_solver_identity_artifact(),
            trust_ir_snapshot: typed_trust_ir_snapshot_artifact(obligation),
            proof_mode: typed_proof_mode(options, normalized.route),
            options: typed_options_artifact(options, normalized.route),
            resource_limits: typed_resource_limits_artifact(options),
            normalized_input_hash: normalized.normalized_input_hash.clone(),
            obligation_set_hash: normalized.obligation_set_hash.clone(),
        },
    )
}

fn typed_artifact_directory(cache_key: &trust_mc_core::FullVerificationCacheKey) -> String {
    format!("target/trust_mc/native/typed-chc-pdr/{}", cache_key.key.value)
}

fn typed_proof_mode(
    options: &trust_mc_core::ChcPdrSolveOptions,
    route: TypedChcPdrRoute,
) -> String {
    format!("typed-chc-pdr::{route:?}::{:?}", options.engine)
}

fn typed_options_artifact(
    options: &trust_mc_core::ChcPdrSolveOptions,
    route: TypedChcPdrRoute,
) -> trust_mc_core::FullVerificationArtifact {
    trust_mc_core::FullVerificationArtifact::from_bytes(
        trust_mc_core::FullVerificationArtifactKind::VerificationOptions,
        "trust_mc://native/typed-chc-pdr/options.json",
        &json_bytes(&serde_json::json!({
            "schema": "trust_mc.typed-chc-pdr-options/v1",
            "engine": format!("{:?}", options.engine),
            "route": format!("{route:?}"),
            "timeout": duration_descriptor(options.timeout),
            "produce_proof_certificate": options.produce_proof_certificate,
        })),
    )
}

fn typed_resource_limits_artifact(
    options: &trust_mc_core::ChcPdrSolveOptions,
) -> trust_mc_core::FullVerificationArtifact {
    trust_mc_core::FullVerificationArtifact::from_bytes(
        trust_mc_core::FullVerificationArtifactKind::ResourceLimits,
        "trust_mc://native/typed-chc-pdr/resource-limits.json",
        &json_bytes(&serde_json::json!({
            "schema": "trust_mc.typed-chc-pdr-resource-limits/v1",
            "requested_timeout": duration_descriptor(options.timeout),
            "effective_timeout": duration_descriptor(Some(effective_typed_chc_timeout(options))),
        })),
    )
}

fn duration_descriptor(duration: Option<Duration>) -> serde_json::Value {
    match duration {
        Some(duration) => serde_json::json!({
            "secs": duration.as_secs(),
            "nanos": duration.subsec_nanos(),
            "millis": duration.as_millis(),
        }),
        None => serde_json::Value::Null,
    }
}

fn effective_typed_chc_timeout(options: &trust_mc_core::ChcPdrSolveOptions) -> Duration {
    options.timeout.unwrap_or(DEFAULT_TYPED_CHC_TIMEOUT)
}

fn typed_trust_ir_snapshot_artifact(
    obligation: &trust_mc_core::MirChcPdrObligation,
) -> Option<trust_mc_core::FullVerificationArtifact> {
    let metadata = obligation.native_metadata.as_ref()?;
    Some(trust_mc_core::FullVerificationArtifact::from_bytes(
        trust_mc_core::FullVerificationArtifactKind::CompilerInput,
        "trust_mc://native/typed-chc-pdr/trust_ir-snapshot.json",
        &json_bytes(&serde_json::json!({
            "schema": "trust_mc.typed-chc-pdr-trust_ir-snapshot/v1",
            "producer": &metadata.producer,
            "adapter_input": &metadata.adapter_input,
            "source_digest": &metadata.source_digest,
            "trust_ir_module_digest": &metadata.trust_ir_module_digest,
            "lineage_manifest_digest": &metadata.lineage_manifest_digest,
            "compiler_facts_digest": &metadata.compiler_facts_digest,
            "replay_identity": &metadata.replay_identity,
            "replay_context": &metadata.replay_context,
            "native_request_id": metadata.native_request_id,
            "function_id": metadata.function_id,
            "proof_obligation_ids": &metadata.proof_obligation_ids,
            "lineage_root_ids": &metadata.lineage_root_ids,
        })),
    ))
}

#[cfg(feature = "ay-chc-native")]
fn ay_solver_identity_artifact() -> trust_mc_core::FullVerificationArtifact {
    trust_mc_core::FullVerificationArtifact::from_bytes(
        trust_mc_core::FullVerificationArtifactKind::SolverBinary,
        "ay://solver/ay-chc-native",
        &json_bytes(&serde_json::json!({
            "schema": "trust_mc.ay-solver-identity/v1",
            "solver": "ay-chc-native",
            "ay_version": ay::VERSION,
            "ay_chc_crate": "ay-chc",
        })),
    )
}

#[cfg(not(feature = "ay-chc-native"))]
fn ay_solver_identity_artifact() -> trust_mc_core::FullVerificationArtifact {
    trust_mc_core::FullVerificationArtifact::from_bytes(
        trust_mc_core::FullVerificationArtifactKind::SolverBinary,
        "ay://solver/ay-chc-native-disabled",
        b"ay-chc-native feature disabled",
    )
}

fn typed_obligation_set_bytes(
    obligation: &trust_mc_core::MirChcPdrObligation,
    route: TypedChcPdrRoute,
) -> Vec<u8> {
    json_bytes(&serde_json::json!({
        "schema": "trust_mc.typed-chc-pdr-obligation-set/v2",
        "route": match route {
            TypedChcPdrRoute::TriviallySafe => "trivially_safe",
            TypedChcPdrRoute::PdrProof => "pdr_proof",
        },
        "obligation_id": &obligation.obligation_id,
        "function_name": &obligation.function_name,
        "kind": obligation.kind,
        "origin": obligation.origin,
        "native_metadata": &obligation.native_metadata,
        "query_target": obligation.query_target(),
        "relations": obligation
            .vc
            .relations
            .iter()
            .map(|relation| {
                serde_json::json!({
                    "name": &relation.name,
                    "arity": relation.arity(),
                    "sorts": relation
                        .arg_sorts
                        .iter()
                        .map(ToString::to_string)
                        .collect::<Vec<_>>(),
                })
            })
            .collect::<Vec<_>>(),
        "rules": obligation
            .vc
            .rules
            .iter()
            .map(|rule| {
                serde_json::json!({
                    "head": {
                        "name": rule.head.name.as_str(),
                        "arity": rule.head.args.len(),
                        "args": rule
                            .head
                            .args
                            .iter()
                            .map(|expr| expr.to_smtlib_shared())
                            .collect::<Vec<_>>(),
                    },
                    "body_relation": rule.body.relation.as_ref().map(|relation| {
                        serde_json::json!({
                            "name": relation.name.as_str(),
                            "arity": relation.args.len(),
                            "args": relation
                                .args
                                .iter()
                                .map(|expr| expr.to_smtlib_shared())
                                .collect::<Vec<_>>(),
                        })
                    }),
                    "constraints": rule
                        .body
                        .constraints
                        .iter()
                        .map(|expr| expr.to_smtlib_shared())
                        .collect::<Vec<_>>(),
                })
            })
            .collect::<Vec<_>>(),
    }))
}

#[cfg(not(feature = "ay-chc-native"))]
fn solve_typed_chc_pdr_with_ay(
    _request: trust_mc_core::ChcPdrSolveRequest,
) -> NativeSolveResult<trust_mc_core::ChcPdrSolveOutcome> {
    Err(NativeSolveError::Unsupported(NativeSolveUnsupported {
        operation: NativeOperation::Solve,
        reason: String::from("ay_chc_native_feature_disabled"),
        detail: String::from("typed CHC/PDR solving requires the ay-chc-native feature"),
    }))
}

/// The producer-recorded count of fail-closed lowering sites (unmodeled
/// constructs lowered to UNCONDITIONALLY REACHABLE error rules) in the
/// submitted CHC. Demote-only transport metadata: a SAT derivation for such a
/// problem may pass through an admission-failure rule instead of a genuine
/// program trap, so a refutation cannot be distinguished from an encoding
/// gap. Absent metadata reads as 0 — the (existing) refutation arms then keep
/// their own havoc-freedom demotion behavior; a forged 0 therefore changes
/// nothing, and a forged nonzero can only WEAKEN a verdict (Refuted →
/// Unknown), never mint authority.
fn fail_closed_lowering_sites(obligation: &trust_mc_core::MirChcPdrObligation) -> u32 {
    obligation.native_metadata.as_ref().map_or(0, |meta| meta.fail_closed_lowering_site_count)
}

/// The producer-recorded DISTINCT construct labels behind
/// [`fail_closed_lowering_sites`] (`"Cast"`, `"IndirectCall"`, …), already
/// sorted and deduplicated by the builder.
///
/// Pure diagnostic, strictly weaker than the count: it is never compared,
/// thresholded or matched, and it reaches exactly one place — the text of
/// [`fail_closed_lowering_demotion_reason`], on an obligation the COUNT has
/// already demoted to Unknown. Absent metadata reads as EMPTY, which renders the
/// message byte-identically to before this field existed.
fn fail_closed_lowering_reasons(obligation: &trust_mc_core::MirChcPdrObligation) -> &[String] {
    obligation
        .native_metadata
        .as_ref()
        .map_or(&[][..], |meta| meta.fail_closed_lowering_reasons.as_slice())
}

/// Render the demotion reason. `sites` is the load-bearing part (it is what the
/// callers gate on); `reasons` only NAMES the constructs so a 21-obligation
/// "N unsupported trust_ir construct(s)" frontier is diagnosable without
/// re-running the translator. An empty `reasons` reproduces the historical text
/// exactly.
fn fail_closed_lowering_demotion_reason(sites: u32, reasons: &[String]) -> String {
    let mut message = format!(
        "fail-closed lowering reachable: {sites} unsupported trust_ir construct(s) lowered to \
         unconditional error rules; refutation demoted to unknown"
    );
    if !reasons.is_empty() {
        message.push_str(" (constructs: ");
        message.push_str(&reasons.join(", "));
        message.push(')');
    }
    message
}

#[cfg(not(feature = "ay-chc-native"))]
fn solve_typed_chc_pdr_full_with_ay(
    _request: trust_mc_core::ChcPdrSolveRequest,
    _prepared: PreparedTypedChcPdrInput,
) -> NativeSolveResult<TypedChcPdrFullVerification> {
    Err(NativeSolveError::Unsupported(NativeSolveUnsupported {
        operation: NativeOperation::Solve,
        reason: String::from("ay_chc_native_feature_disabled"),
        detail: String::from("typed CHC/PDR full verification requires the ay-chc-native feature"),
    }))
}

#[cfg(feature = "ay-chc-native")]
fn solve_typed_chc_pdr_with_ay(
    request: trust_mc_core::ChcPdrSolveRequest,
) -> NativeSolveResult<trust_mc_core::ChcPdrSolveOutcome> {
    let obligation_id = request.obligation.obligation_id.clone();
    let stats = request.obligation.stats();
    let timeout = effective_typed_chc_timeout(&request.options);
    let (problem, lowering) = typed_chc_ay::lower_obligation_with_accounting(&request.obligation)?;
    // Bind the pre-solve identity of the exact lowered problem before the
    // solver consumes it, so a refutation witness can carry the normalized
    // encoded-formula digest of exactly what was solved.
    let route = typed_chc_pdr_route(&request.obligation);
    let normalized = native_typed_chc_pdr_normalized_input(
        &request.obligation,
        route,
        ay_encode::normalized_chc_input(&problem),
    );

    let verdict = match request.options.engine {
        trust_mc_core::ChcPdrEngine::Pdr => solve_typed_chc_with_pdr(problem, timeout)?,
        _ => solve_typed_chc_with_adaptive_portfolio(problem, timeout)?,
    };

    // WS1: consume the frontend-neutral `ay_encode::verdict::AyVerdict` instead of the raw
    // `VerifiedChcResult`. The mapping is byte-identical to the pre-port match:
    //   Proved   -> unknown pending private replay (was Safe(_))
    //   Violated -> refuted(..)                 (was Unsafe(_))
    //   Unknown  -> unknown(detail, ..)         (was Unknown(reason) => reason.to_string())
    // `AyVerdict::Unknown.detail` carries AY's original `VerifiedUnknownMarker`
    // `Display` rendering (G4), so it reproduces the pre-port `reason.to_string()`
    // text exactly. `AyVerdict` is `#[non_exhaustive]`; an unrecognized future
    // variant maps to the same "unrecognized" Unknown the pre-port `_` arm used.
    Ok(match verdict {
        ay_encode::verdict::AyVerdict::Proved { .. } => trust_mc_core::ChcPdrSolveOutcome::unknown(
            obligation_id,
            trust_mc_core::PDR_INVARIANT_FRESH_CONSUMER_REPLAY_REQUIRED,
            stats,
        )
        .with_diagnostic("AY PDR candidate awaits fresh private consumer replay"),
        ay_encode::verdict::AyVerdict::Violated(model) => {
            // Merge composition (main x refutation-witness-20260719): main's
            // fail-closed-lowering demotion stays OUTERMOST — a counterexample
            // whose derivation may pass through a fail-closed lowering error
            // rule is an admission failure, not a program trap, and must never
            // become Refuted (with or without a witness). Only the clean path
            // attaches the branch's replay-verified refutation witness.
            let sites = fail_closed_lowering_sites(&request.obligation);
            if sites > 0 {
                trust_mc_core::ChcPdrSolveOutcome::unknown(
                    obligation_id,
                    fail_closed_lowering_demotion_reason(
                        sites,
                        fail_closed_lowering_reasons(&request.obligation),
                    ),
                    stats,
                )
                .with_diagnostic(
                    "ay-chc counterexample discarded: the derivation may pass through a \
                     fail-closed lowering error rule (admission failure, not a program trap)",
                )
            } else {
                // `AyVerdict::Violated` wraps ay-chc's REPLAY-VERIFIED
                // `Counterexample` (from `VerifiedChcResult::Unsafe`), never a
                // bare solver claim. Attach a refutation witness bound to the
                // exact pre-solve normalized input when the lowering was
                // exact; a nonzero accounting degrades to the historical
                // witnessless `Refuted`.
                let counterexample = serde_json::json!({
                    "schema": "trust_mc.typed-chc-pdr-counterexample/v1",
                    "source": "ay-chc-replay-verified-counterexample",
                    "step_count": model.counterexample.steps.len(),
                    "counterexample_debug": format!("{:?}", model.counterexample),
                });
                let witness = typed_chc_pdr_refutation_witness(
                    &obligation_id,
                    &normalized.normalized_input_hash,
                    request.options.engine,
                    normalized.route,
                    &counterexample,
                    trust_mc_core::ChcPdrCexVerification::AyChcReplayVerified {
                        step_count: model.counterexample.steps.len() as u64,
                    },
                    Some(lowering),
                );
                match witness {
                    Some(witness) => trust_mc_core::ChcPdrSolveOutcome::refuted_with_witness(
                        obligation_id,
                        witness,
                        stats,
                    ),
                    None => trust_mc_core::ChcPdrSolveOutcome::refuted(obligation_id, stats),
                }
                .with_diagnostic("ay-chc verified counterexample for typed CHC/PDR obligation")
            }
        }
        ay_encode::verdict::AyVerdict::Unknown { detail: Some(detail), .. } => {
            trust_mc_core::ChcPdrSolveOutcome::unknown(obligation_id, detail, stats)
                .with_diagnostic("ay-chc returned unknown for typed CHC/PDR obligation")
        }
        // `detail: None` only arises from `from_verified`'s non-exhaustive `_`
        // arm — an unrecognized future `VerifiedChcResult` variant with no AY
        // marker. Preserve the pre-port `_` arm's exact diagnostic for that
        // degenerate case rather than emitting an empty reason string.
        ay_encode::verdict::AyVerdict::Unknown { detail: None, .. } => {
            trust_mc_core::ChcPdrSolveOutcome::unknown(
                obligation_id,
                "ay-chc returned an unrecognized non-exhaustive result",
                stats,
            )
            .with_diagnostic("ay-chc returned unrecognized result for typed CHC/PDR obligation")
        }
        // Future-proofing for `AyVerdict`'s own `#[non_exhaustive]` marker; no
        // such variant exists today, so this is unreachable in practice.
        _ => trust_mc_core::ChcPdrSolveOutcome::unknown(
            obligation_id,
            "ay-chc returned an unrecognized non-exhaustive result",
            stats,
        )
        .with_diagnostic("ay-chc returned unrecognized result for typed CHC/PDR obligation"),
    })
}

/// Enforce a HARD wall-clock ceiling on a native solve phase. The ay solver
/// does not honor its internal budget during every phase — notably bit-blasting
/// the 128-bit BV multiplies of a mul/div-heavy function — so a hard obligation
/// can spin far past its deadline (a real 23h orca-core survey hang,
/// 2026-06-13). Run the work on a worker thread and `recv_timeout`; on expiry
/// abandon the worker (it exits at process end) and return `None`. Callers map
/// `None` to an `Unknown` verdict — SOUND: a timed-out solve is undecided, never
/// a false proof. Mirrors the SMT-LIB BMC path's watchdog (`execute_smtlib_bmc`).
#[cfg(feature = "ay-chc-native")]
fn run_native_solve_within_deadline<T, F>(deadline: Duration, work: F) -> Option<T>
where
    F: FnOnce() -> T + Send + 'static,
    T: Send + 'static,
{
    let (tx, rx) = mpsc::channel();
    thread::spawn(move || {
        let _ = tx.send(work());
    });
    rx.recv_timeout(deadline).ok()
}

#[cfg(feature = "ay-chc-native")]
fn solve_typed_chc_pdr_full_with_ay(
    request: trust_mc_core::ChcPdrSolveRequest,
    prepared: PreparedTypedChcPdrInput,
) -> NativeSolveResult<TypedChcPdrFullVerification> {
    let obligation_id = request.obligation.obligation_id.clone();
    let stats = request.obligation.stats();
    let timeout = effective_typed_chc_timeout(&request.options);
    let PreparedTypedChcPdrInput { normalized, problem, lowering } = prepared;
    let Some(problem) = problem else {
        return Err(NativeSolveError::SolverFailed {
            reason: String::from(
                "PDR route preparation did not retain the lowered typed CHC problem",
            ),
        });
    };
    if normalized.route != TypedChcPdrRoute::PdrProof {
        return Err(NativeSolveError::SolverFailed {
            reason: String::from("lowered typed CHC problem was prepared for a non-PDR route"),
        });
    }
    // The public request normalizer and production solve share this exact value;
    // do not derive proof identity from the returned cache key or verdict.
    let route = normalized.route;
    let cache_key =
        typed_full_verification_cache_key(&request.obligation, &request.options, &normalized);
    let normalized_input_hash = normalized.normalized_input_hash.clone();
    let normalized_input = normalized.normalized_input;
    let artifact_directory = typed_artifact_directory(&cache_key);

    // Cheap, sound refutation first: if the acyclic direct-SMT shortcut composes
    // a concrete satisfiable derivation of `error`, that is a *real*
    // counterexample, so report Failed immediately instead of paying for an
    // expensive PDR/PDR run that would only return Unknown (PDR cannot
    // synthesize an invariant for a false property). Safe obligations yield
    // `None` here and fall through to PDR for the proof, so this never turns a
    // genuine proof into a refutation.
    // Wall-clock watchdog ceiling (the in-solver budget plus a small grace, so
    // the solver's own timeout wins when it can; the watchdog backstops the
    // phases that ignore it). See `run_native_solve_within_deadline`.
    let watchdog_ceiling = timeout.saturating_add(Duration::from_secs(2));

    let decision_problem = problem.clone();
    let decision = match run_native_solve_within_deadline(watchdog_ceiling, move || {
        crate::direct_smt_cex::acyclic_direct_smt_decision(&decision_problem)
    }) {
        Some(decision) => decision,
        None => {
            let reason = format!(
                "native direct-SMT decision search exceeded the {}s wall-clock ceiling",
                watchdog_ceiling.as_secs()
            );
            return Ok(TypedChcPdrFullVerification {
                route,
                cache_key: cache_key.clone(),
                artifact_directory: artifact_directory.clone(),
                outcome: trust_mc_core::ChcPdrSolveOutcome::unknown(
                    obligation_id.clone(),
                    reason.clone(),
                    stats,
                )
                .with_diagnostic("native typed-CHC solve exceeded its wall-clock ceiling"),
                verdict: trust_mc_core::FullVerificationVerdict::Unknown { reason },
                private_native_proof_seal: None,
            });
        }
    };
    match decision {
        crate::direct_smt_cex::AcyclicDecision::Unsafe(direct_witness) => {
            let sites = fail_closed_lowering_sites(&request.obligation);
            if sites > 0 {
                let reason = fail_closed_lowering_demotion_reason(
                    sites,
                    fail_closed_lowering_reasons(&request.obligation),
                );
                return Ok(TypedChcPdrFullVerification {
                    route,
                    cache_key: cache_key.clone(),
                    artifact_directory: artifact_directory.clone(),
                    outcome: trust_mc_core::ChcPdrSolveOutcome::unknown(
                        obligation_id.clone(),
                        reason.clone(),
                        stats,
                    )
                    .with_diagnostic(
                        "direct SMT satisfiable typed query fact discarded: the acyclic error \
                         derivation may pass through a fail-closed lowering error rule \
                         (admission failure, not a program trap)",
                    ),
                    verdict: trust_mc_core::FullVerificationVerdict::Unknown { reason },
                    private_native_proof_seal: None,
                });
            }
            let counterexample = serde_json::json!({
                "schema": "trust_mc.typed-chc-pdr-counterexample/v1",
                "source": "direct-smt-acyclic-error-derivation",
                "derivation_clause_indices": direct_witness.derivation_clause_indices,
                "witness_model": direct_witness.model,
            });
            // Attach a refutation witness bound to the exact pre-solve
            // normalized input when the lowering was exact; a nonzero
            // accounting degrades to the historical witnessless `Refuted`.
            let witness = typed_chc_pdr_refutation_witness(
                &obligation_id,
                &normalized_input_hash,
                request.options.engine,
                route,
                &counterexample,
                trust_mc_core::ChcPdrCexVerification::DirectSmtModel,
                lowering,
            );
            let outcome = match witness {
                Some(witness) => trust_mc_core::ChcPdrSolveOutcome::refuted_with_witness(
                    obligation_id.clone(),
                    witness,
                    stats,
                ),
                None => trust_mc_core::ChcPdrSolveOutcome::refuted(obligation_id.clone(), stats),
            }
            .with_diagnostic(
                "direct SMT confirmed a satisfiable typed query fact; refuted obligation via \
                 acyclic error derivation before PDR",
            );
            let verdict = trust_mc_core::FullVerificationVerdict::Failed {
                counterexample_artifacts: vec![
                    trust_mc_core::FullVerificationArtifact::from_bytes(
                        trust_mc_core::FullVerificationArtifactKind::CounterexampleTrace,
                        format!(
                            "trust_mc://typed-chc/{}/counterexample.json",
                            request.obligation.obligation_id
                        ),
                        &json_bytes(&counterexample),
                    ),
                ],
            };
            return Ok(TypedChcPdrFullVerification {
                route,
                cache_key: cache_key.clone(),
                artifact_directory: artifact_directory.clone(),
                outcome,
                verdict,
                private_native_proof_seal: None,
            });
        }
        crate::direct_smt_cex::AcyclicDecision::Safe => {
            // OBLIGATION-AWARE direct-Safe re-enable (the future fix the deferral note
            // below describes). Finalize the acyclic Safe as a proof ONLY when the
            // direct problem is the COMPLETE obligation encoding — it carries the full
            // CFG block relations (≥1 block predicate beyond the `error` query target),
            // NOT a reduced single-`error`-headed sub-VC.
            //
            // SOUNDNESS (sound-by-construction): the false-PROVE the `a957a9ee3` defer
            // closed comes from a PARTIAL sub-VC — e.g. `let x = r?; assert!(x==0)`
            // reduces in the direct path to the switch EXHAUSTIVENESS contradiction
            // `(_3∈{0,1}) ∧ (_3∉{0,1})`, a SINGLE `error`-headed clause (predicate_count
            // == 1) that OMITS the `assert!(x==0)` reachability. A COMPLETE-CFG problem
            // (predicate_count ≥ 2) encodes the obligation's full block/transition
            // structure, so an EXHAUSTIVE acyclic search finding no error derivation is
            // a genuine proof (ChcValidity). Reduced single-clause problems still DEFER
            // to the faithful PDR/transport solve below — never PROVE — so the partial
            // sub-VC false proof stays closed. The Trust falsification gate is the
            // guard: a wrong finalization surfaces as a surviving mutant.
            //
            // Conservative by design: faithful-but-single-clause problems (e.g. modulo
            // `n%4` unreachable, already proved by the ay soundness-merge) also defer
            // here — no regression, they prove via PDR/transport below.
            if problem.predicates().len() >= 2 {
                let input_hash =
                    trust_mc_core::EvidenceHash::sha256_bytes(normalized_input.as_bytes()).value;
                let certificate = serde_json::json!({
                    "schema": "trust_mc.typed-chc-acyclic-safe-certificate/v1",
                    "source": "acyclic-direct-smt-exhaustive-no-error-derivation",
                    "decision": "safe",
                    "complete_encoding": true,
                    "predicate_count": problem.predicates().len(),
                    "normalized_input_sha256": input_hash,
                });
                let certificate_bytes = json_bytes(&certificate);
                let certificate_hash =
                    trust_mc_core::EvidenceHash::sha256_bytes(&certificate_bytes);
                let replay = serde_json::json!({
                    "schema": "trust_mc.typed-chc-pdr-replay-log/v2",
                    "source": "acyclic-direct-smt-exhaustive-safe-complete-encoding",
                    "accepted_as_candidate": true,
                    "accepted_as_proof": false,
                    "authoritative": false,
                    "private_authority_not_serialized": true,
                    "normalized_input_sha256": input_hash,
                    "certificate": certificate.clone(),
                    "referenced_solver_transcript": {
                        "kind": "solver_transcript",
                        "algorithm": certificate_hash.algorithm,
                        "value": certificate_hash.value,
                    },
                });
                let replay_bytes = json_bytes(&replay);
                let replay_hash = trust_mc_core::EvidenceHash::sha256_bytes(&replay_bytes);
                let checked_report = serde_json::json!({
                    "schema": "trust_mc.typed-chc-pdr-checked-proof-report/v2",
                    "accepted_as_candidate": true,
                    "accepted_as_proof": false,
                    "authoritative": false,
                    "private_authority_not_serialized": true,
                    "problem_kind": "chc-acyclic-exhaustive-complete-encoding",
                    "proof_status": "safe",
                    "result": "safe",
                    "replay_check_status": { "replay": "unknown", "check": "unknown" },
                    "referenced_solver_transcript": {
                        "kind": "solver_transcript",
                        "algorithm": certificate_hash.algorithm,
                        "value": certificate_hash.value,
                    },
                    "referenced_replay_log": {
                        "kind": "replay_log",
                        "algorithm": replay_hash.algorithm,
                        "value": replay_hash.value,
                    },
                    "stats": {
                        "relation_count": stats.relation_count,
                        "clause_count": stats.clause_count,
                    },
                });
                let verdict = typed_proved_verdict(
                    &request.obligation,
                    trust_mc_core::ChcPdrProofKind::ChcValidity,
                    stats,
                    &normalized_input,
                    &cache_key,
                    certificate_bytes,
                    replay_bytes,
                    json_bytes(&checked_report),
                    None,
                    None,
                );
                let outcome = trust_mc_core::ChcPdrSolveOutcome::unknown(
                    obligation_id.clone(),
                    trust_mc_core::CHC_VALIDITY_FRESH_CONSUMER_REPLAY_REQUIRED,
                    stats,
                )
                .with_diagnostic(
                    "private acyclic direct-SMT exhaustive derivation found a COMPLETE-encoding \
                     obligation SAFE; public ChcValidity evidence remains a candidate",
                );
                return Ok(TypedChcPdrFullVerification {
                    route,
                    cache_key: cache_key.clone(),
                    artifact_directory: artifact_directory.clone(),
                    outcome,
                    verdict,
                    private_native_proof_seal: None,
                });
            }
            // Reduced single-`error`-headed problem (predicate_count == 1): may be a
            // PARTIAL sub-VC of a richer obligation (the `a957a9ee3` false-PROVE class).
            // DEFER to the faithful PDR/transport solve below — never PROVE here.
        }
        crate::direct_smt_cex::AcyclicDecision::Inconclusive => {}
    }

    // CYCLIC FAST PATH (G2 loop-invariant lane, run BEFORE the primary PDR solve).
    // For a genuinely cyclic (loop) obligation the direct PDR proof search below
    // frequently cannot synthesize the loop invariant and SPINS for the entire
    // `watchdog_ceiling`, consuming the router's wall-clock budget before the
    // fast, sound IC3 loop lane (invoked otherwise only in the post-solve Unknown
    // arm — too late) ever runs. A lane-provable loop (e.g. the count-parity
    // invariant `acc <=> count[0]`) then times out despite a ~15ms proof. The
    // lane is candidate-only, re-validated fail-closed against the ORIGINAL
    // problem (including the query/safety clause) both here and inside
    // `prove_with_external_model`, and ADDITIVE: it can emit ONLY a reject-only
    // `PdrInvariant` carrier (never `Unsafe`). Public status remains Unknown
    // until the compiler's private consumer freshly replays it. Trying the lane
    // FIRST is sound — a genuinely unsafe loop makes re-validation FAIL (→
    // `None`) and falls through to the full solve below, which finds the
    // counterexample. Acyclic problems are untouched (the lane self-gates on
    // `has_cycles`), so the common case pays nothing.
    if problem.has_cycles() {
        // W2-i3: HARD wall-clock bound on the IC3 loop lane. `try_prove_chc_loop`
        // runs the bit-level IC3 `solve()`, which does NOT honor its in-solver
        // timeout, so a non-converging loop obligation (Fibonacci-class) spins for
        // the entire router budget (observed ~140s) before this fast, sound lane
        // ever yields — starving the primary PDR run and burning the whole clock.
        // The existing native watchdog caps it at `watchdog_ceiling`: on expiry
        // the worker is abandoned (it exits at process end) and we fall through as
        // a `None` (no-candidate) return, exactly as when the lane finds nothing.
        // SOUND: a timed-out lane is undecided, never a false proof
        // (`run_native_solve_within_deadline` contract, native.rs:1360). The lane
        // operates on owned clones, so abandonment shares no state with this thread.
        let lane_problem = problem.clone();
        let lane_obligation = request.obligation.clone();
        let lane_normalized = normalized_input.clone();
        let lane_cache_key = cache_key.clone();
        let lane_artifact = artifact_directory.clone();
        if let Some(Some(verification)) =
            run_native_solve_within_deadline(watchdog_ceiling, move || {
                try_ic3_loop_lane(
                    &lane_problem,
                    &lane_obligation,
                    stats,
                    &lane_normalized,
                    &lane_cache_key,
                    &lane_artifact,
                    route,
                    timeout,
                )
            })
        {
            return Ok(verification);
        }
    }

    // WS1: drive the PDR proof run through `ay_encode::invoke::solve_with_proof`.
    // `EncodeConfig::to_pdr_config` (G2) builds `PdrConfig::production(false)` +
    // the timeout as `solve_timeout`, and `solve_pdr_proof` forces
    // `strict_proofs` internally — identical to the pre-port
    // `PdrConfig::production(false).with_strict_proofs(true)` config. The proof
    // run is then digested through `ay_encode::proof::Certificate`.
    let pdr_problem = problem.clone();
    // Auto-invariant CANDIDATE hints (shared `chc_auto_hints` lane): loop
    // templates — counter ranges, difference bounds, scaled accumulators —
    // mined from the transition clauses. PDR VALIDATES every hint via
    // `is_inductive_blocking` before installing it (never trusted), so this
    // can only convert Inconclusive into a genuinely proved invariant.
    let (auto_hints, _auto_stats) = crate::chc_auto_hints::generate_lemma_hint_candidates(
        &pdr_problem,
        crate::chc_auto_hints::HintSource::Native,
    );
    let pdr_config = ay_encode::invoke::EncodeConfig::new()
        .with_engine(ay_encode::invoke::Engine::Pdr)
        .with_proof_mode(ay_encode::invoke::ProofMode::Strict)
        .with_timeout(timeout)
        .with_lemma_hints(auto_hints);
    let proof_run = match run_native_solve_within_deadline(watchdog_ceiling, move || {
        ay_encode::invoke::solve_with_proof(pdr_problem, &pdr_config)
    }) {
        Some(Ok(run)) => run,
        Some(Err(err)) => {
            return Err(NativeSolveError::SolverFailed {
                reason: format!("ay-chc PDR proof run failed: {err}"),
            });
        }
        None => {
            let reason = format!(
                "native PDR proof search exceeded the {}s wall-clock ceiling",
                watchdog_ceiling.as_secs()
            );
            return Ok(TypedChcPdrFullVerification {
                route,
                cache_key: cache_key.clone(),
                artifact_directory: artifact_directory.clone(),
                outcome: trust_mc_core::ChcPdrSolveOutcome::unknown(
                    obligation_id.clone(),
                    reason.clone(),
                    stats,
                )
                .with_diagnostic("native typed-CHC solve exceeded its wall-clock ceiling"),
                verdict: trust_mc_core::FullVerificationVerdict::Unknown { reason },
                private_native_proof_seal: None,
            });
        }
    };

    // Digest the proof run into the shared `Certificate` (G5/G6): it carries the
    // AY candidate-accepted bit, the strict QF invariant, diagnostic model
    // metadata, replay-transcript artifacts (each with
    // `schema`/`role`/`digest`/`bytes()`), and the proof-run metadata
    // (`metadata_json`/`normalized_input_sha256`/`proof_status`/`result`). The
    // raw `VerifiedChcResult` is read off `proof_run.result()` for the
    // Safe/Unsafe/Unknown match below (the invariant/cex payloads do not live on
    // the certificate). Reject-only `PdrInvariant` transport (certificate/
    // artifact/replay/checked-report bytes + AY acceptance guard) lives in
    // `emit_pdr_invariant_from_run`, shared with the IC3 loop lane so the
    // evidence-payload JSON schema strings stay byte-identical on both paths.
    let run = proof_run.result();
    let certificate = proof_run.certificate();
    let metadata = certificate.metadata_json();

    let (outcome, verdict) = match run {
        ay_chc::VerifiedChcResult::Safe(_) => {
            // Reject-only `PdrInvariant` transport via the shared helper. The
            // helper enforces the AY acceptance guard (`accepted &&
            // accepted_as_proof &&` the normalized-input hash binds to this
            // obligation); a non-accepted Safe run yields `None`. Even a valid
            // candidate reports Unknown until fresh private-consumer replay.
            match emit_pdr_invariant_from_run(
                run,
                &certificate,
                &request.obligation,
                stats,
                &normalized_input,
                &cache_key,
            ) {
                Some(outcome_and_verdict) => outcome_and_verdict,
                None => (
                    trust_mc_core::ChcPdrSolveOutcome::unknown(
                        obligation_id,
                        "ay-chc PDR proof metadata was not accepted",
                        stats,
                    )
                    .with_diagnostic("typed PDR proof metadata failed acceptance checks"),
                    trust_mc_core::FullVerificationVerdict::Unknown {
                        reason: String::from("typed PDR proof metadata failed acceptance checks"),
                    },
                ),
            }
        }
        ay_chc::VerifiedChcResult::Unsafe(verified_cex) => {
            // Merge composition (main x refutation-witness-20260719): main's
            // fail-closed-lowering demotion stays OUTERMOST; the clean path
            // attaches the branch's replay-verified refutation witness.
            let sites = fail_closed_lowering_sites(&request.obligation);
            if sites > 0 {
                let reason = fail_closed_lowering_demotion_reason(
                    sites,
                    fail_closed_lowering_reasons(&request.obligation),
                );
                (
                    trust_mc_core::ChcPdrSolveOutcome::unknown(
                        obligation_id,
                        reason.clone(),
                        stats,
                    )
                    .with_diagnostic(
                        "ay-chc counterexample discarded: the derivation may pass through a \
                         fail-closed lowering error rule (admission failure, not a program trap)",
                    ),
                    trust_mc_core::FullVerificationVerdict::Unknown { reason },
                )
            } else {
                let counterexample = serde_json::json!({
                    "schema": "trust_mc.typed-chc-pdr-counterexample/v1",
                    "step_count": verified_cex.counterexample().steps.len(),
                    "counterexample_debug": format!("{:?}", verified_cex.counterexample()),
                    "ay_metadata": metadata,
                });
                // `VerifiedChcResult::Unsafe` is ay-chc's REPLAY-VERIFIED
                // counterexample. Attach a refutation witness bound to the
                // exact pre-solve normalized input when the lowering was
                // exact; a nonzero accounting degrades to the historical
                // witnessless `Refuted`.
                let witness = typed_chc_pdr_refutation_witness(
                    &obligation_id,
                    &normalized_input_hash,
                    request.options.engine,
                    route,
                    &counterexample,
                    trust_mc_core::ChcPdrCexVerification::AyChcReplayVerified {
                        step_count: verified_cex.counterexample().steps.len() as u64,
                    },
                    lowering,
                );
                (
                    match witness {
                        Some(witness) => trust_mc_core::ChcPdrSolveOutcome::refuted_with_witness(
                            obligation_id,
                            witness,
                            stats,
                        ),
                        None => trust_mc_core::ChcPdrSolveOutcome::refuted(obligation_id, stats),
                    }
                    .with_diagnostic("ay-chc verified counterexample for typed CHC/PDR obligation"),
                    trust_mc_core::FullVerificationVerdict::Failed {
                        counterexample_artifacts: vec![
                            trust_mc_core::FullVerificationArtifact::from_bytes(
                                trust_mc_core::FullVerificationArtifactKind::CounterexampleTrace,
                                format!(
                                    "trust_mc://typed-chc/{}/counterexample.json",
                                    request.obligation.obligation_id
                                ),
                                &json_bytes(&counterexample),
                            ),
                        ],
                    },
                )
            }
        }
        ay_chc::VerifiedChcResult::Unknown(reason) => {
            // G2 real-call loop lane. The portfolio/PDR solve returned a
            // non-Safe verdict (Unknown). The acyclic direct-SMT shortcut and
            // the Safe/Unsafe arms above have already returned for every decided
            // case, so reaching here means the obligation is genuinely undecided
            // by the primary path. ONLY now — never overriding an existing
            // Safe/Unsafe verdict — try to synthesize a loop invariant via ay's
            // bit-level IC3 lane, re-validate it fail-closed (explicitly here AND
            // again inside `prove_with_external_model`), and transport a
            // reject-only `PdrInvariant` candidate. The lane self-gates to cyclic
            // problems and returns `None` (this Unknown fall-through) whenever
            // re-validation rejects the candidate. A valid candidate still
            // remains Unknown here until the compiler's private replay gate.
            // W2-i3: same HARD wall-clock bound as the cyclic fast path above —
            // this post-solve arm can also spin in the unbounded IC3 `solve()`.
            // On watchdog expiry we fall through to the Unknown outcome below.
            let lane_problem = problem.clone();
            let lane_obligation = request.obligation.clone();
            let lane_normalized = normalized_input.clone();
            let lane_cache_key = cache_key.clone();
            let lane_artifact = artifact_directory.clone();
            if let Some(Some(verification)) =
                run_native_solve_within_deadline(watchdog_ceiling, move || {
                    try_ic3_loop_lane(
                        &lane_problem,
                        &lane_obligation,
                        stats,
                        &lane_normalized,
                        &lane_cache_key,
                        &lane_artifact,
                        route,
                        timeout,
                    )
                })
            {
                return Ok(verification);
            }
            // Bounded-unroll REFUTATION lane (last escalation, cyclic L0
            // obligations only). Runs only after every proof-seeking lane
            // (direct-SMT, IC3 loop invariant, PDR) ended Unknown, and can
            // only ever return `Refuted { witness }` + `Failed` — its return
            // type has no Proved/Safe arm, so a truncated search can never
            // mint proof credit. See `bounded_unroll` module docs.
            if let Some(verification) = try_bounded_unroll_refutation_lane(
                &problem,
                &request,
                stats,
                &normalized_input_hash,
                route,
                &cache_key,
                &artifact_directory,
                lowering,
                watchdog_ceiling,
            ) {
                return Ok(verification);
            }
            (
                trust_mc_core::ChcPdrSolveOutcome::unknown(
                    obligation_id,
                    format!("{:?}", reason.reason()),
                    stats,
                )
                .with_diagnostic("ay-chc returned unknown for typed CHC/PDR obligation"),
                trust_mc_core::FullVerificationVerdict::Unknown {
                    reason: format!("ay-chc returned unknown: {:?}", reason.reason()),
                },
            )
        }
        _ => (
            trust_mc_core::ChcPdrSolveOutcome::unknown(
                obligation_id,
                "ay-chc returned an unrecognized non-exhaustive result",
                stats,
            )
            .with_diagnostic("ay-chc returned unrecognized result for typed CHC/PDR obligation"),
            trust_mc_core::FullVerificationVerdict::Unknown {
                reason: String::from("ay-chc returned an unrecognized non-exhaustive result"),
            },
        ),
    };

    Ok(TypedChcPdrFullVerification {
        route,
        cache_key,
        artifact_directory,
        outcome,
        verdict,
        private_native_proof_seal: None,
    })
}

/// Build a reject-only `PdrInvariant` `(outcome, verdict)` carrier from a
/// digested proof run, or `None` when the run is not an AY-accepted `Safe`
/// candidate for this obligation.
///
/// This is the SINGLE emission point shared by the normal PDR `Safe` arm and the
/// IC3 loop lane (`try_ic3_loop_lane`), so the evidence-payload JSON schema
/// (`trust_mc.typed-chc-pdr-replay-log/v3`, `…-checked-proof-report/v3`, the
/// separate QF-invariant/diagnostic-metadata/replay-transcript descriptors, and the
/// `PdrInvariant` verdict) is byte-identical regardless of which path produced
/// the candidate.
///
/// Fail-closed acceptance guard: the run must be `Safe` AND
/// `certificate.accepted_as_proof()` (consumer evidence AND transcript metadata) AND the
/// certificate's normalized-input hash must bind to `normalized_input`. Any
/// miss returns `None`, so an unaccepted or mis-bound run can never be emitted.
/// A successful carrier uses a Proved-shaped typed verdict only for private
/// replay transport; its public solve outcome and proof-grade classification
/// remain Unknown/rejected.
#[cfg(feature = "ay-chc-native")]
fn emit_pdr_invariant_from_run(
    run: &ay_chc::VerifiedChcResult,
    certificate: &ay_encode::proof::Certificate,
    obligation: &trust_mc_core::MirChcPdrObligation,
    stats: trust_mc_core::ChcPdrStats,
    normalized_input: &str,
    cache_key: &trust_mc_core::FullVerificationCacheKey,
) -> Option<(trust_mc_core::ChcPdrSolveOutcome, trust_mc_core::FullVerificationVerdict)> {
    let ay_chc::VerifiedChcResult::Safe(verified_inv) = run else {
        return None;
    };
    if !(certificate.accepted_as_proof()
        && certificate.normalized_input_sha256()
            == trust_mc_core::EvidenceHash::sha256_bytes(normalized_input.as_bytes()).value)
    {
        return None;
    }

    let metadata = certificate.metadata_json();
    let proof_run_artifacts = certificate.artifacts();
    // The legacy `model` artifact is consumer-status metadata, not predicate
    // interpretations. Only AY's strict, bounded QF artifact may occupy
    // trust-mc's `PdrInvariantModel` transport slot. Absence means this Safe
    // result belongs to a different/non-replayable evidence class, so fail
    // closed before constructing even a reject-only candidate carrier.
    let invariant_model_artifact = proof_run_artifacts.quantifier_free_invariant_model()?;
    let transcript_bytes = proof_run_artifacts.replay_transcript().bytes().to_vec();
    let transcript_hash = trust_mc_core::EvidenceHash::sha256_bytes(&transcript_bytes);
    let invariant_model_bytes = invariant_model_artifact.bytes().to_vec();
    let replay = serde_json::json!({
        "schema": "trust_mc.typed-chc-pdr-replay-log/v3",
        "source": "ay_chc::ChcPdrProofRun::proof_run_artifacts",
        "ay_candidate_accepted": certificate.accepted_as_proof(),
        "normalized_input_sha256": certificate.normalized_input_sha256(),
        "referenced_solver_transcript": {
            "kind": "solver_transcript",
            "algorithm": transcript_hash.algorithm,
            "value": transcript_hash.value,
        },
        "ay_artifacts": {
            "quantifier_free_invariant_model": ay_chc_proof_run_artifact_descriptor(
                invariant_model_artifact
            ),
            "diagnostic_model_metadata": ay_chc_proof_run_artifact_descriptor(
                proof_run_artifacts.model()
            ),
            "replay_transcript": ay_chc_proof_run_artifact_descriptor(
                proof_run_artifacts.replay_transcript()
            ),
        },
        "ay_consumer_evidence": certificate.consumer_evidence().to_json_value(),
        "ay_transcript_metadata": metadata.clone(),
    });
    let replay_bytes = json_bytes(&replay);
    let replay_log_hash = trust_mc_core::EvidenceHash::sha256_bytes(&replay_bytes);
    let checked_report = serde_json::json!({
        "schema": "trust_mc.typed-chc-pdr-checked-proof-report/v3",
        "ay_candidate_accepted": certificate.accepted_as_proof(),
        "problem_kind": "chc-pdr",
        "proof_status": certificate.proof_status(),
        "result": certificate.result(),
        "replay_check_status": {
            "replay": "not-run-by-private-consumer",
            "check": "unknown",
            "fresh_private_consumer_replay_required": true,
            "authoritative": false,
        },
        "checked_artifacts": {
            "quantifier_free_invariant_model": ay_chc_proof_run_artifact_descriptor(
                invariant_model_artifact
            ),
            "diagnostic_model_metadata": ay_chc_proof_run_artifact_descriptor(
                proof_run_artifacts.model()
            ),
            "replay_transcript": ay_chc_proof_run_artifact_descriptor(
                proof_run_artifacts.replay_transcript()
            ),
            "replay_log": {
                "algorithm": replay_log_hash.algorithm,
                "value": replay_log_hash.value,
                "bytes": replay_bytes.len(),
            },
        },
        "referenced_solver_transcript": {
            "kind": "solver_transcript",
            "algorithm": transcript_hash.algorithm,
            "value": transcript_hash.value,
        },
        "referenced_replay_log": {
            "kind": "replay_log",
            "algorithm": replay_log_hash.algorithm,
            "value": replay_log_hash.value,
        },
        "stats": {
            "relation_count": stats.relation_count,
            "clause_count": stats.clause_count,
        },
        "ay_consumer_evidence": certificate.consumer_evidence().to_json_value(),
        "ay_transcript_metadata": metadata,
    });

    let verdict = typed_proved_verdict(
        obligation,
        trust_mc_core::ChcPdrProofKind::PdrInvariant,
        stats,
        normalized_input,
        cache_key,
        transcript_bytes,
        replay_bytes,
        json_bytes(&checked_report),
        Some(verified_inv.model().len()),
        Some(invariant_model_bytes),
    );
    let outcome = match &verdict {
        trust_mc_core::FullVerificationVerdict::Proved { .. } => {
            trust_mc_core::ChcPdrSolveOutcome::unknown(
                obligation.obligation_id.clone(),
                trust_mc_core::PDR_INVARIANT_FRESH_CONSUMER_REPLAY_REQUIRED,
                stats,
            )
            .with_diagnostic("transported AY PDR candidate awaits fresh private consumer replay")
        }
        trust_mc_core::FullVerificationVerdict::Unknown { reason } => {
            trust_mc_core::ChcPdrSolveOutcome::unknown(
                obligation.obligation_id.clone(),
                reason.clone(),
                stats,
            )
            .with_diagnostic("typed PDR evidence materialization failed closed")
        }
        _ => trust_mc_core::ChcPdrSolveOutcome::unknown(
            obligation.obligation_id.clone(),
            "typed PDR evidence returned a non-proof verdict",
            stats,
        ),
    };

    Some((outcome, verdict))
}

/// G2 real-call IC3 loop lane.
///
/// Cyclic fast/fallback lane used before the primary PDR search and again after
/// a primary Unknown. It synthesizes a candidate loop invariant with AY's
/// bit-level IC3 lane, re-validates it fail-closed, and—only if it survives—
/// transports reject-only `PdrInvariant` evidence identical to the normal
/// `Safe` path.
///
/// Soundness (belt-and-suspenders, the whole point of the lane):
/// 1. **Cyclicity gate** — `problem.has_cycles()`. Acyclic obligations are fully
///    decided by the direct-SMT / PDR path and skip the lane entirely.
/// 2. **Candidate generation** — `ay_chc::ic3_lane::try_prove_chc_loop` returns a
///    word-level `InvariantModel` that is explicitly NOT trusted (see that
///    module's contract).
/// 3. **Mandatory explicit re-validation** —
///    `ay_chc::engines::validate_external_invariant_model` runs the full init +
///    transition + query clause check in a fresh verifier; any failure/panic
///    (`unwrap_or(false)`) rejects the candidate and the lane returns `None`.
/// 4. **Re-validation AGAIN on emission** — `prove_with_external_model` re-runs
///    the same full clause check internally before wrapping the model as an
///    accepted proof run; a rejected candidate comes back non-accepted and
///    `emit_pdr_invariant_from_run` refuses it.
///
/// So the candidate is re-validated twice before transport. The public result
/// remains Unknown; only a fresh private compiler replay may later grant it
/// authority. The lane never overrides or weakens an existing Unsafe verdict.
#[cfg(feature = "ay-chc-native")]
fn try_ic3_loop_lane(
    problem: &ay_chc::ChcProblem,
    obligation: &trust_mc_core::MirChcPdrObligation,
    stats: trust_mc_core::ChcPdrStats,
    normalized_input: &str,
    cache_key: &trust_mc_core::FullVerificationCacheKey,
    artifact_directory: &str,
    route: TypedChcPdrRoute,
    timeout: Duration,
) -> Option<TypedChcPdrFullVerification> {
    // (1) Cyclicity gate: only genuinely cyclic (self-recursive or multi-block
    // loop) predicate graphs are candidates for a loop invariant. Acyclic
    // obligations skip the lane so it adds no cost to the common case and can
    // never fire where the direct-SMT / PDR path is already exhaustive.
    if !problem.has_cycles() {
        return None;
    }

    // (2) Generate a CANDIDATE loop invariant. Not trusted until re-validated.
    let candidate = ay_chc::ic3_lane::try_prove_chc_loop(problem, timeout)?;

    // Shared config: the production PDR profile + this solve's timeout, built the
    // same way the primary PDR run above is (`EncodeConfig` → `to_pdr_config`),
    // so the explicit re-validation and the emission's internal re-validation use
    // identical verifier settings.
    let encode_cfg = ay_encode::invoke::EncodeConfig::new()
        .with_engine(ay_encode::invoke::Engine::Pdr)
        .with_proof_mode(ay_encode::invoke::ProofMode::Strict)
        .with_timeout(timeout);

    // (3) MANDATORY explicit re-validation, fail-closed. This is the load-bearing
    // soundness gate the ic3_lane module contract requires: a wrong invariant,
    // a false loop, or an imprecise header lift fails here and the lane
    // contributes nothing. Any verifier error/panic is treated as rejection.
    let validated = ay_chc::engines::validate_external_invariant_model(
        problem,
        &candidate,
        &encode_cfg.to_pdr_config(),
    )
    .unwrap_or(false);
    if !validated {
        return None;
    }

    // (4) Build the reject-only evidence carrier. `prove_with_external_model`
    // re-validates the candidate AGAIN internally before wrapping it as an
    // AY-accepted proof run, so by the time we digest the certificate the model
    // has passed the full clause check twice. This still grants no public proof
    // authority; a rejected candidate comes back as a non-accepted run.
    let proof_run =
        ay_encode::invoke::prove_with_external_model(problem.clone(), candidate, &encode_cfg)
            .ok()?;
    let certificate = proof_run.certificate();

    // Reuse the SAME reject-only `PdrInvariant` transport the normal Safe arm uses.
    // `emit_pdr_invariant_from_run` re-checks `certificate.accepted_as_proof()
    // && the normalized-input hash binds`; if the run is not
    // accepted (rejected candidate) it returns `None` and the lane yields `None`.
    let (outcome, verdict) = emit_pdr_invariant_from_run(
        proof_run.result(),
        &certificate,
        obligation,
        stats,
        normalized_input,
        cache_key,
    )?;

    Some(TypedChcPdrFullVerification {
        route,
        cache_key: cache_key.clone(),
        artifact_directory: artifact_directory.to_string(),
        outcome,
        verdict,
        private_native_proof_seal: None,
    })
}

/// Map an `ay_encode::EncodeError` from the typed CHC/PDR invocation onto the
/// driver's `NativeSolveError`. AY-classified solver panics and engine failures
/// both become `SolverFailed` — byte-identical to the pre-port wording so the
/// canary's diagnostic column does not shift.
#[cfg(feature = "ay-chc-native")]
fn encode_error_to_solver_failed(err: ay_encode::EncodeError, what: &str) -> NativeSolveError {
    NativeSolveError::SolverFailed { reason: format!("ay-chc {what} failed: {err}") }
}

/// WS1: thin wrapper over `ay_encode::invoke::solve` for the PDR engine.
///
/// Equivalent to the pre-port body, which built
/// `PdrConfig::production(false).with_strict_proofs(true)` + `solve_timeout` and
/// called `engines::solve_pdr_proof(..).result`. `ay_encode`'s
/// `EncodeConfig::to_pdr_config` (G2) starts from `PdrConfig::production(false)`
/// and `solve_pdr_proof` forces `strict_proofs` internally, so the lowered
/// `PdrConfig` is identical.
#[cfg(feature = "ay-chc-native")]
fn solve_typed_chc_with_pdr(
    problem: ay_chc::ChcProblem,
    timeout: Duration,
) -> NativeSolveResult<ay_encode::verdict::AyVerdict> {
    // Validated-candidate loop hints (see the primary PDR run's rationale).
    let (auto_hints, _) = crate::chc_auto_hints::generate_lemma_hint_candidates(
        &problem,
        crate::chc_auto_hints::HintSource::Native,
    );
    let config = ay_encode::invoke::EncodeConfig::new()
        .with_engine(ay_encode::invoke::Engine::Pdr)
        .with_proof_mode(ay_encode::invoke::ProofMode::Strict)
        .with_timeout(timeout)
        .with_lemma_hints(auto_hints);
    ay_encode::invoke::solve(problem, &config)
        .map_err(|err| encode_error_to_solver_failed(err, "PDR proof run"))
}

/// WS1: thin wrapper over `ay_encode::invoke::solve` for the adaptive portfolio.
///
/// Equivalent to the pre-port body, which built
/// `AdaptiveConfig::with_budget(timeout, false)` + `strict_proofs = true` and
/// called `AdaptivePortfolio::new(..).solve_with_budget_report().0`. In non-test
/// builds `with_budget(t, false)` == `default().with_time_budget(t)`, and
/// `solve_with_budget_report().0` == `solve()` (same scoped solve; the budget
/// report was discarded), so the verdict is identical. `with_strict_validation`
/// (G1) re-validates every `Safe` exactly as the pre-port `strict_proofs = true`
/// did.
///
/// The pre-port code caught panics via `catch_unwind` and mapped them to
/// `SolverFailed`. `ay_encode::invoke::solve` already converts AY-classified
/// panics into `EncodeError::SolverPanicked` (G3); the surrounding `catch_unwind`
/// is kept so a non-AY (programmer) panic still becomes `SolverFailed` rather
/// than unwinding through the worker thread, preserving pre-port behavior.
#[cfg(feature = "ay-chc-native")]
fn solve_typed_chc_with_adaptive_portfolio(
    problem: ay_chc::ChcProblem,
    timeout: Duration,
) -> NativeSolveResult<ay_encode::verdict::AyVerdict> {
    // Validated-candidate loop hints (see the primary PDR run's rationale) —
    // the portfolio's PDR engines consume `user_hints` through the same
    // inductively-validating `apply_lemma_hints` pipeline.
    let (auto_hints, _) = crate::chc_auto_hints::generate_lemma_hint_candidates(
        &problem,
        crate::chc_auto_hints::HintSource::Native,
    );
    let config = ay_encode::invoke::EncodeConfig::new()
        .with_engine(ay_encode::invoke::Engine::Auto)
        .with_timeout(timeout)
        .with_strict_validation(true)
        .with_lemma_hints(auto_hints);
    std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        ay_encode::invoke::solve(problem, &config)
    }))
    .map_err(|panic_payload| NativeSolveError::SolverFailed {
        reason: format!(
            "ay-chc adaptive portfolio panicked: {}",
            panic_payload
                .downcast_ref::<String>()
                .map(|s| s.as_str())
                .or_else(|| panic_payload.downcast_ref::<&str>().copied())
                .unwrap_or("<non-string panic>")
        ),
    })?
    .map_err(|err| encode_error_to_solver_failed(err, "adaptive portfolio"))
}

fn validate_solve_request(request: &NativeSolveRequest) -> NativeSolveResult<()> {
    if request.artifact.obligation_id.trim().is_empty() {
        return Err(NativeSolveError::InvalidInput {
            field: String::from("artifact.obligation_id"),
            detail: String::from("must not be empty"),
        });
    }
    if request.artifact.function_name.trim().is_empty() {
        return Err(NativeSolveError::InvalidInput {
            field: String::from("artifact.function_name"),
            detail: String::from("must not be empty"),
        });
    }
    if request.artifact.payload.is_empty() {
        return Err(NativeSolveError::InvalidInput {
            field: String::from("artifact.payload"),
            detail: String::from("must not be empty"),
        });
    }
    match request.artifact.provenance.proof_mode {
        NativeProofMode::Bmc | NativeProofMode::FiniteAcyclicBmc => {
            if request.artifact.provenance.bmc_depth.is_none() {
                return Err(NativeSolveError::InvalidInput {
                    field: String::from("artifact.provenance.bmc_depth"),
                    detail: String::from("must be set for BMC proof modes"),
                });
            }
        }
        NativeProofMode::Chc | NativeProofMode::PdrIc3 => {}
    }
    Ok(())
}

fn solve_smtlib_bmc(request: NativeSolveRequest) -> NativeSolveResult<NativeSolvedArtifact> {
    if !matches!(
        request.artifact.provenance.proof_mode,
        NativeProofMode::Bmc | NativeProofMode::FiniteAcyclicBmc
    ) {
        return Err(NativeSolveError::InvalidInput {
            field: String::from("artifact.provenance.proof_mode"),
            detail: String::from("BMC artifacts require BMC proof provenance"),
        });
    }

    let payload = decode_smtlib_bmc_payload(&request.artifact)?;
    validate_payload_matches_artifact(&payload, &request.artifact)?;

    let execution = execute_smtlib_bmc(&payload.script, request.timeout)?;
    let (verdict, diagnostics) = interpret_bmc_execution(execution);

    Ok(NativeSolvedArtifact {
        obligation_id: request.artifact.obligation_id,
        verdict,
        provenance: request.artifact.provenance,
        proof_certificate: None,
        diagnostics,
    })
}

fn decode_smtlib_bmc_payload(
    artifact: &NativeEncodedArtifact,
) -> NativeSolveResult<SmtLibBmcPayload> {
    let payload =
        std::str::from_utf8(&artifact.payload).map_err(|err| NativeSolveError::InvalidInput {
            field: String::from("artifact.payload"),
            detail: format!("payload is not valid UTF-8 JSON: {err}"),
        })?;
    serde_json::from_str(payload).map_err(|err| NativeSolveError::InvalidInput {
        field: String::from("artifact.payload"),
        detail: format!("payload is not a native SMT-LIB BMC envelope: {err}"),
    })
}

fn validate_payload_matches_artifact(
    payload: &SmtLibBmcPayload,
    artifact: &NativeEncodedArtifact,
) -> NativeSolveResult<()> {
    if payload.format != SMTLIB_BMC_PAYLOAD_FORMAT {
        return invalid_payload("format", "must be `trust-mc.native.smtlib-bmc`");
    }
    if payload.version != SMTLIB_BMC_PAYLOAD_VERSION {
        return invalid_payload("version", "unsupported native SMT-LIB BMC payload version");
    }
    if payload.kind != "bmc" {
        return invalid_payload("kind", "must be `bmc`");
    }
    if payload.obligation_id != artifact.obligation_id {
        return invalid_payload("obligation_id", "must match artifact.obligation_id");
    }
    if payload.function_name != artifact.function_name {
        return invalid_payload("function_name", "must match artifact.function_name");
    }
    if payload.script.trim().is_empty() {
        return invalid_payload("script", "must not be empty");
    }

    let payload_mode = proof_mode_from_payload(&payload.provenance.proof_mode)?;
    if payload_mode != artifact.provenance.proof_mode {
        return invalid_payload("provenance.proof_mode", "must match artifact provenance");
    }
    if payload.provenance.bmc_depth != artifact.provenance.bmc_depth {
        return invalid_payload("provenance.bmc_depth", "must match artifact provenance");
    }
    if payload.provenance.finite_acyclic != artifact.provenance.finite_acyclic {
        return invalid_payload("provenance.finite_acyclic", "must match artifact provenance");
    }
    if payload.provenance.producer != artifact.provenance.producer {
        return invalid_payload("provenance.producer", "must match artifact provenance");
    }
    Ok(())
}

fn invalid_payload<T>(field: &str, detail: &str) -> NativeSolveResult<T> {
    Err(NativeSolveError::InvalidInput {
        field: format!("artifact.payload.{field}"),
        detail: String::from(detail),
    })
}

fn proof_mode_from_payload(mode: &str) -> NativeSolveResult<NativeProofMode> {
    match mode {
        "bmc" => Ok(NativeProofMode::Bmc),
        "finite_acyclic_bmc" => Ok(NativeProofMode::FiniteAcyclicBmc),
        "chc" => Ok(NativeProofMode::Chc),
        "pdr_ic3" => Ok(NativeProofMode::PdrIc3),
        _ => invalid_payload("provenance.proof_mode", "unknown proof mode"),
    }
}

#[cfg(any(feature = "ay-chc-native", feature = "ay-direct"))]
enum NativeBmcExecution {
    Completed(Vec<String>),
    TimedOut,
}

#[cfg(any(feature = "ay-chc-native", feature = "ay-direct"))]
fn execute_smtlib_bmc(
    script: &str,
    timeout: Option<Duration>,
) -> NativeSolveResult<NativeBmcExecution> {
    let commands = ay::parse(script).map_err(|err| NativeSolveError::InvalidInput {
        field: String::from("artifact.payload.script"),
        detail: format!("SMT-LIB parse error: {err}"),
    })?;
    if !commands
        .iter()
        .any(|command| matches!(command, ay::Command::CheckSat | ay::Command::CheckSatAssuming(_)))
    {
        return Err(NativeSolveError::InvalidInput {
            field: String::from("artifact.payload.script"),
            detail: String::from("must contain a check-sat command"),
        });
    }

    if let Some(timeout) = timeout {
        let (tx, rx) = mpsc::channel();
        thread::spawn(move || {
            let _ = tx.send(run_ay_executor(commands));
        });
        match rx.recv_timeout(timeout) {
            Ok(result) => result.map(NativeBmcExecution::Completed),
            Err(mpsc::RecvTimeoutError::Timeout) => Ok(NativeBmcExecution::TimedOut),
            Err(mpsc::RecvTimeoutError::Disconnected) => {
                Ok(NativeBmcExecution::Completed(vec![String::from("unknown")]))
            }
        }
    } else {
        run_ay_executor(commands).map(NativeBmcExecution::Completed)
    }
}

#[cfg(any(feature = "ay-chc-native", feature = "ay-direct"))]
fn run_ay_executor(commands: Vec<ay::Command>) -> NativeSolveResult<Vec<String>> {
    ay::catch_ay_panics(
        || {
            let mut executor = ay::executor::Executor::new();
            executor.execute_all(&commands).map_err(|err| NativeSolveError::InvalidInput {
                field: String::from("artifact.payload.script"),
                detail: format!("native AY executor error: {err}"),
            })
        },
        |reason| Ok(vec![format!("unknown\n; native AY executor panic: {reason}")]),
    )
}

#[cfg(not(any(feature = "ay-chc-native", feature = "ay-direct")))]
fn execute_smtlib_bmc(_script: &str, _timeout: Option<Duration>) -> NativeSolveResult<()> {
    Err(NativeSolveError::Unsupported(NativeSolveUnsupported {
        operation: NativeOperation::Solve,
        reason: String::from("ay_native_solver_not_enabled"),
        detail: String::from("build with ay-chc-native or ay-direct to solve native BMC payloads"),
    }))
}

#[cfg(any(feature = "ay-chc-native", feature = "ay-direct"))]
fn interpret_bmc_execution(execution: NativeBmcExecution) -> (NativeSolverVerdict, Vec<String>) {
    match execution {
        NativeBmcExecution::Completed(outputs) => interpret_solver_outputs(outputs),
        NativeBmcExecution::TimedOut => {
            (NativeSolverVerdict::Timeout, vec![String::from("native AY executor timed out")])
        }
    }
}

#[cfg(not(any(feature = "ay-chc-native", feature = "ay-direct")))]
fn interpret_bmc_execution(_execution: ()) -> (NativeSolverVerdict, Vec<String>) {
    unreachable!("no-solver execute_smtlib_bmc always returns Err")
}

#[cfg(any(feature = "ay-chc-native", feature = "ay-direct"))]
fn interpret_solver_outputs(outputs: Vec<String>) -> (NativeSolverVerdict, Vec<String>) {
    let verdict = outputs.iter().filter_map(|output| classify_solver_output(output)).next_back();
    let diagnostics =
        outputs.iter().filter(|output| classify_solver_output(output).is_none()).cloned().collect();
    match verdict {
        Some(NativeSolverVerdict::Proved) => (NativeSolverVerdict::Proved, diagnostics),
        Some(NativeSolverVerdict::Failed) => (NativeSolverVerdict::Failed, diagnostics),
        Some(NativeSolverVerdict::Unknown { reason }) => {
            (NativeSolverVerdict::Unknown { reason }, diagnostics)
        }
        Some(NativeSolverVerdict::Timeout) => (NativeSolverVerdict::Timeout, diagnostics),
        None => (
            NativeSolverVerdict::Unknown {
                reason: String::from("native AY executor emitted no check-sat result"),
            },
            diagnostics,
        ),
    }
}

#[cfg(any(feature = "ay-chc-native", feature = "ay-direct"))]
fn classify_solver_output(output: &str) -> Option<NativeSolverVerdict> {
    match output.lines().next().unwrap_or("").trim() {
        "unsat" => Some(NativeSolverVerdict::Proved),
        "sat" => Some(NativeSolverVerdict::Failed),
        "unknown" => Some(NativeSolverVerdict::Unknown {
            reason: String::from("native AY executor returned unknown"),
        }),
        _ => None,
    }
}

/// Classify a native full-verification verdict for proof-grade publication.
///
/// This is a library-facing wrapper around `trust-mc_core`'s evidence policy. It is
/// intentionally separate from `solve_native`, whose current implementation can
/// solve diagnostic SMT-LIB BMC payloads but cannot upgrade them into full
/// verification proofs.
#[must_use]
pub fn classify_native_full_verification_verdict(
    verdict: &trust_mc_core::FullVerificationVerdict,
) -> trust_mc_core::ProofGradeVerdict {
    trust_mc_core::classify_proof_grade_verdict(verdict)
}

/// Returns true only for proof-grade CHC/PDR native full-verification verdicts.
#[must_use]
pub fn is_proof_grade_native_full_verification_verdict(
    verdict: &trust_mc_core::FullVerificationVerdict,
) -> bool {
    matches!(
        classify_native_full_verification_verdict(verdict),
        trust_mc_core::ProofGradeVerdict::ProofGrade { .. }
    )
}

/// The two rejection buckets that never reach the two-lane predicate, because
/// the admission arm's own PATTERN (`count: None, align: None`) excludes them.
/// They cannot be exercised from `trust-mc-trust-bmc`, so they are pinned here.
#[cfg(all(test, feature = "native-trust-ir-bundle"))]
mod alloca_rejection_reason_tests {
    use super::alloca_rejection_reason;
    use trust_ir::inst::Inst;
    use trust_ir::node::InstrNode;
    use trust_ir::ty::Ty;
    use trust_ir::value::{BlockId, FuncId, FuncTyId, ValueId};
    use trust_ir::{Block, Function, Module};

    /// The fixtures are hand-built `Function`s over scalar cells only, so the
    /// module is consulted solely by `aggregate_field_tys_of` (which never fires
    /// for `Ty::I64`). An empty module is therefore exact, not a stub.
    fn empty_module() -> Module {
        Module::new("alloca_reason")
    }

    fn function_with(body: Vec<InstrNode>) -> Function {
        let mut function =
            Function::new(FuncId::new(0), "alloca_reason", FuncTyId::new(0), BlockId::new(0));
        let mut block = Block::new(BlockId::new(0));
        block.body = body;
        function.blocks = vec![block];
        function
    }

    #[test]
    fn an_array_alloca_is_named_as_such() {
        let cell = ValueId::new(0);
        let function = function_with(vec![
            InstrNode::new(Inst::Alloca {
                ty: Ty::I64,
                count: Some(ValueId::new(9)),
                align: None,
            })
            .with_result(cell),
            InstrNode::new(Inst::Return { values: Vec::new() }),
        ]);
        let reason =
            alloca_rejection_reason(&empty_module(), &function, Some(cell), &Ty::I64, true, false);
        assert_eq!(reason.kind, "alloca_count_some");
    }

    #[test]
    fn a_caller_aligned_alloca_is_named_as_such() {
        let cell = ValueId::new(0);
        let function = function_with(vec![
            InstrNode::new(Inst::Alloca { ty: Ty::I64, count: None, align: Some(8) })
                .with_result(cell),
            InstrNode::new(Inst::Return { values: Vec::new() }),
        ]);
        let reason =
            alloca_rejection_reason(&empty_module(), &function, Some(cell), &Ty::I64, false, true);
        assert_eq!(reason.kind, "alloca_align_some");
        // The extent check comes first, exactly as the arm's pattern reads.
        let both =
            alloca_rejection_reason(&empty_module(), &function, Some(cell), &Ty::I64, true, true);
        assert_eq!(both.kind, "alloca_count_some");
    }

    #[test]
    fn a_result_less_alloca_is_named_as_such() {
        let function = function_with(vec![
            InstrNode::new(Inst::Alloca { ty: Ty::I64, count: None, align: None }),
            InstrNode::new(Inst::Return { values: Vec::new() }),
        ]);
        let reason =
            alloca_rejection_reason(&empty_module(), &function, None, &Ty::I64, false, false);
        assert_eq!(reason.kind, "alloca_no_result");
    }

    /// A metadata-less alloca defers to the two-lane predicate, and the bucket it
    /// returns carries BOTH lanes so a gate log can be split on `/`.
    #[test]
    fn a_metadata_less_alloca_defers_to_the_admission_predicate() {
        let cell = ValueId::new(0);
        let function = function_with(vec![
            InstrNode::new(Inst::Alloca { ty: Ty::I64, count: None, align: None })
                .with_result(cell),
            InstrNode::new(Inst::Load {
                ty: Ty::I64,
                ptr: cell,
                volatile: false,
                align: None,
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::Return { values: Vec::new() }),
        ]);
        let reason =
            alloca_rejection_reason(&empty_module(), &function, Some(cell), &Ty::I64, false, false);
        assert_eq!(reason.kind, "load_before_store/not_definitely_initialized");
        assert!(reason.detail.contains("block-local="), "the detail names both lanes");
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn smtlib_bmc_payload(
        obligation_id: &str,
        function_name: &str,
        script: &str,
        provenance: &NativeProofProvenance,
    ) -> Vec<u8> {
        serde_json::to_vec(&serde_json::json!({
            "format": SMTLIB_BMC_PAYLOAD_FORMAT,
            "version": SMTLIB_BMC_PAYLOAD_VERSION,
            "kind": "bmc",
            "obligation_id": obligation_id,
            "function_name": function_name,
            "script": script,
            "provenance": {
                "proof_mode": match provenance.proof_mode {
                    NativeProofMode::Bmc => "bmc",
                    NativeProofMode::FiniteAcyclicBmc => "finite_acyclic_bmc",
                    NativeProofMode::Chc => "chc",
                    NativeProofMode::PdrIc3 => "pdr_ic3",
                },
                "bmc_depth": provenance.bmc_depth,
                "finite_acyclic": provenance.finite_acyclic,
                "producer": provenance.producer,
            },
        }))
        .expect("test payload serialization")
    }

    fn sample_artifact(provenance: NativeProofProvenance) -> NativeEncodedArtifact {
        NativeEncodedArtifact::new(
            "obligation-1",
            "crate::harness",
            NativeVcKind::Bmc,
            smtlib_bmc_payload(
                "obligation-1",
                "crate::harness",
                "(set-logic QF_LIA)\n(assert false)\n(check-sat)\n",
                &provenance,
            ),
            provenance,
        )
    }

    #[cfg(any(feature = "ay-chc-native", feature = "ay-direct"))]
    fn compiler_bmc_provenance(depth: u32) -> NativeProofProvenance {
        NativeProofProvenance {
            proof_mode: NativeProofMode::Bmc,
            bmc_depth: Some(depth),
            finite_acyclic: false,
            producer: String::from("trust-mc-compiler-native"),
        }
    }

    fn trust_mc_core_obligation() -> trust_mc_core::MirDerivedChcPdrObligation {
        trust_mc_core::MirDerivedChcPdrObligation::new(
            "native-full-obligation",
            trust_mc_core::MirObligationKind::Assertion,
            "(set-logic HORN)\n(declare-rel error ())\n(rule false)\n(query error)\n",
        )
    }

    fn typed_chc_obligation(derive_error: bool) -> trust_mc_core::MirChcPdrObligation {
        let mut vc = trust_mc_core::ChcVc::new();
        vc.add_relation(trust_mc_core::RelationDecl::nullary("entry"));
        vc.add_relation(trust_mc_core::RelationDecl::nullary("error"));
        vc.query = trust_mc_core::ChcQuery::new().with_target("error");

        vc.add_rule(trust_mc_core::Rule::new(
            trust_mc_core::RuleBody::empty(),
            trust_mc_core::RelationApp::nullary("entry"),
        ));
        if derive_error {
            vc.add_rule(trust_mc_core::Rule::new(
                trust_mc_core::RuleBody::empty(),
                trust_mc_core::RelationApp::nullary("error"),
            ));
        }

        trust_mc_core::MirChcPdrObligation::new(
            "typed-obligation",
            "crate::harness",
            trust_mc_core::MirObligationKind::Assertion,
            vc,
        )
    }

    fn typed_native_chc_obligation(derive_error: bool) -> trust_mc_core::MirChcPdrObligation {
        let mut obligation = typed_chc_obligation(derive_error);
        obligation.obligation_id = "trust_ir-native-trust_mc-request-7-proof-0".to_string();
        obligation.with_native_metadata(
            trust_mc_core::NativeTypedChcObligationMetadata::new(
                "tRust",
                "rust-mir",
                Some(trust_mc_core::NativeArtifactDigest::new("sha256", "11".repeat(32))),
                trust_mc_core::NativeArtifactDigest::new("sha256", "22".repeat(32)),
                trust_mc_core::NativeArtifactDigest::new("trust_ir-stable-v1", "33".repeat(32)),
                7,
                "chc",
                9,
                vec![0],
                vec![0],
            )
            .with_compiler_facts(
                trust_mc_core::NativeArtifactDigest::new("trust_ir-stable-v1", "44".repeat(32)),
                trust_mc_core::NativeCompilerFactCounts {
                    monomorphizations: 1,
                    obligation_sources: 1,
                    ..trust_mc_core::NativeCompilerFactCounts::default()
                },
                vec![trust_mc_core::NativeObligationCompilerFacts {
                    proof_obligation_id: 0,
                    function_id: Some(9),
                    span: Some(trust_mc_core::NativeSourceSpanMetadata {
                        file: 0,
                        line: 18,
                        col: 13,
                    }),
                    cause: trust_mc_core::NativeObligationCauseMetadata::Assert,
                    monomorphization_id: Some(0),
                    fact_refs: vec![trust_mc_core::NativeCompilerFactReference::new(
                        trust_mc_core::NativeCompilerFactKind::Monomorphization,
                        0,
                    )],
                }],
            )
            .with_replay_metadata(
                trust_mc_core::NativeReplayIdentityMetadata {
                    engine: "trust-mc".to_string(),
                    invocation: "trust_mc native typed CHC/PDR transport test replay".to_string(),
                    transcript_digest: trust_mc_core::NativeArtifactDigest::new(
                        "sha256",
                        "55".repeat(32),
                    ),
                },
                trust_mc_core::NativeReplayContextMetadata {
                    atoms: vec![trust_mc_core::NativeReplayAtomMetadata {
                        atom_id: 0,
                        kind: trust_mc_core::NativeReplayAtomKindMetadata::Assertion,
                        formula_schema: "smtlib2".to_string(),
                        payload_digest: trust_mc_core::NativeArtifactDigest::new(
                            "trust_ir-stable-v1",
                            "66".repeat(32),
                        ),
                        proof_obligation_id: Some(0),
                        assertion_id: Some(0),
                        span: Some(trust_mc_core::NativeSourceSpanMetadata {
                            file: 0,
                            line: 18,
                            col: 13,
                        }),
                    }],
                    unsupported_modes: Vec::new(),
                },
            ),
        )
    }

    /// Same native-metadata-bound trivially-safe obligation as
    /// [`typed_native_chc_obligation`], but carrying the diagnostic
    /// `structural_reachability_complete` claim that
    /// `native_bundle::native_chc_metadata` stamps on every CHC minted by the
    /// complete-by-construction native translator. The public claim alone never
    /// grants authority.
    fn typed_native_chc_obligation_structural_complete(
        derive_error: bool,
    ) -> trust_mc_core::MirChcPdrObligation {
        let mut obligation = typed_native_chc_obligation(derive_error);
        let metadata = obligation
            .native_metadata
            .take()
            .expect("native trust_ir obligation carries metadata")
            .with_structural_reachability_complete(true);
        obligation.with_native_metadata(metadata)
    }

    fn typed_chc_obligation_with_non_error_query() -> trust_mc_core::MirChcPdrObligation {
        let mut vc = trust_mc_core::ChcVc::new();
        vc.add_relation(trust_mc_core::RelationDecl::nullary("entry"));
        vc.add_relation(trust_mc_core::RelationDecl::nullary("error"));
        vc.add_relation(trust_mc_core::RelationDecl::nullary("panic_target"));
        vc.query = trust_mc_core::ChcQuery::new().with_target("panic_target");

        vc.add_rule(trust_mc_core::Rule::new(
            trust_mc_core::RuleBody::empty(),
            trust_mc_core::RelationApp::nullary("entry"),
        ));
        vc.add_rule(trust_mc_core::Rule::new(
            trust_mc_core::RuleBody::empty(),
            trust_mc_core::RelationApp::nullary("error"),
        ));

        trust_mc_core::MirChcPdrObligation::new(
            "typed-non-error-query",
            "crate::harness_with_misleading_error_rule",
            trust_mc_core::MirObligationKind::Assertion,
            vc,
        )
    }

    #[cfg(feature = "ay-chc-native")]
    fn safe_nontrivial_typed_chc_obligation() -> trust_mc_core::MirChcPdrObligation {
        let mut vc = trust_mc_core::ChcVc::new();
        vc.add_relation(trust_mc_core::RelationDecl::new("entry", vec![ay_bindings::Sort::int()]));
        vc.add_relation(trust_mc_core::RelationDecl::nullary("error"));
        vc.query = trust_mc_core::ChcQuery::new().with_target("error");

        let x = vc.declare_var("x", ay_bindings::Sort::int());
        vc.add_rule(trust_mc_core::Rule::new(
            trust_mc_core::RuleBody::empty(),
            trust_mc_core::RelationApp::new("entry", vec![ay_bindings::Expr::int_const(0)]),
        ));
        vc.add_rule(trust_mc_core::Rule::new(
            trust_mc_core::RuleBody::new(
                Some(trust_mc_core::RelationApp::new("entry", vec![x.clone()])),
                vec![x.int_lt(ay_bindings::Expr::int_const(0))],
            ),
            trust_mc_core::RelationApp::nullary("error"),
        ));

        trust_mc_core::MirChcPdrObligation::new(
            "safe-nontrivial-typed-obligation",
            "crate::safe_harness",
            trust_mc_core::MirObligationKind::Assertion,
            vc,
        )
    }

    #[cfg(feature = "ay-chc-native")]
    fn safe_cyclic_typed_chc_obligation(
        obligation_id: &str,
        step_limit: i128,
    ) -> trust_mc_core::MirChcPdrObligation {
        let mut vc = trust_mc_core::ChcVc::new();
        vc.add_relation(trust_mc_core::RelationDecl::new("loop", vec![ay_bindings::Sort::int()]));
        vc.add_relation(trust_mc_core::RelationDecl::nullary("error"));
        vc.query = trust_mc_core::ChcQuery::new().with_target("error");

        let x = vc.declare_var("x", ay_bindings::Sort::int());
        vc.add_rule(trust_mc_core::Rule::new(
            trust_mc_core::RuleBody::empty(),
            trust_mc_core::RelationApp::new("loop", vec![ay_bindings::Expr::int_const(0)]),
        ));
        vc.add_rule(trust_mc_core::Rule::new(
            trust_mc_core::RuleBody::new(
                Some(trust_mc_core::RelationApp::new("loop", vec![x.clone()])),
                vec![x.clone().int_lt(ay_bindings::Expr::int_const(step_limit))],
            ),
            trust_mc_core::RelationApp::new(
                "loop",
                vec![x.clone().int_add(ay_bindings::Expr::int_const(1))],
            ),
        ));
        vc.add_rule(trust_mc_core::Rule::new(
            trust_mc_core::RuleBody::new(
                Some(trust_mc_core::RelationApp::new("loop", vec![x.clone()])),
                vec![x.int_lt(ay_bindings::Expr::int_const(0))],
            ),
            trust_mc_core::RelationApp::nullary("error"),
        ));

        trust_mc_core::MirChcPdrObligation::new(
            obligation_id,
            "crate::safe_cyclic_harness",
            trust_mc_core::MirObligationKind::Assertion,
            vc,
        )
        .with_native_metadata(
            typed_native_chc_obligation(false).native_metadata.expect("native test metadata"),
        )
    }

    #[cfg(feature = "ay-chc-native")]
    fn rebuild_pdr_candidate_with_model(
        mut verification: TypedChcPdrFullVerification,
        model_bytes: &[u8],
    ) -> TypedChcPdrFullVerification {
        let rebuilt = {
            let trust_mc_core::FullVerificationVerdict::Proved {
                evidence: trust_mc_core::FullProofEvidence::ChcPdr(proof),
            } = &verification.verdict
            else {
                panic!("fixture must carry CHC/PDR evidence");
            };
            assert_eq!(proof.kind, trust_mc_core::ChcPdrProofKind::PdrInvariant);
            let artifact = |kind| {
                let mut matches = proof.artifacts.iter().filter(|artifact| artifact.kind == kind);
                let artifact = matches.next().expect("required proof artifact");
                assert!(matches.next().is_none(), "proof artifact must be unique");
                artifact
            };
            let transcript =
                artifact(trust_mc_core::FullVerificationArtifactKind::SolverTranscript);
            let replay = artifact(trust_mc_core::FullVerificationArtifactKind::ReplayLog);
            let check = artifact(trust_mc_core::FullVerificationArtifactKind::CheckedProofReport);
            let typed_problem =
                artifact(trust_mc_core::FullVerificationArtifactKind::TypedChcProblem).clone();
            let cache_key = proof.metadata.cache_key.clone();
            let mut rebuilt =
                trust_mc_core::ChcPdrProofEvidence::try_pdr_invariant_candidate_from_linked_bytes(
                    proof.obligation.clone(),
                    proof.stats,
                    proof.invariant_count,
                    (
                        transcript.label.as_str(),
                        transcript.materialized_bytes().expect("materialized transcript"),
                    ),
                    (
                        replay.label.as_str(),
                        replay.materialized_bytes().expect("materialized replay"),
                    ),
                    (check.label.as_str(), check.materialized_bytes().expect("materialized check")),
                    ("trust-mc://adversarial/replacement-model.json", model_bytes),
                )
                .expect("bounded replacement candidate");
            rebuilt = rebuilt.with_artifact(typed_problem);
            rebuilt.metadata.cache_key = cache_key;
            rebuilt
        };
        verification.verdict = trust_mc_core::FullVerificationVerdict::Proved {
            evidence: trust_mc_core::FullProofEvidence::ChcPdr(rebuilt),
        };
        verification
    }

    #[cfg(feature = "ay-chc-native")]
    fn invalid_but_canonical_pdr_model_bytes(
        obligation: &trust_mc_core::MirChcPdrObligation,
    ) -> Vec<u8> {
        #[derive(Serialize)]
        struct Envelope {
            schema: &'static str,
            schema_version: u32,
            role: &'static str,
            model_format: &'static str,
            normalized_input_sha256: String,
            predicate_count: u64,
            model_sha256: String,
            model_smtlib: String,
        }

        let problem = typed_chc_ay::lower_obligation(obligation).expect("fixture lowers");
        let raw_model = r#"
(define-fun loop ((x Int)) Bool
  true)
(define-fun error () Bool
  false)
"#;
        let model = ay_chc::InvariantModel::parse_smtlib(raw_model, &problem)
            .expect("complete but non-inductive model parses");
        let model_smtlib = model.to_smtlib(&problem);
        let envelope = Envelope {
            schema: ay_chc::CHC_QF_INVARIANT_MODEL_ARTIFACT_SCHEMA,
            schema_version: 1,
            role: ay_chc::CHC_QF_INVARIANT_MODEL_ARTIFACT_ROLE,
            model_format: ay_chc::CHC_QF_INVARIANT_MODEL_ARTIFACT_MODEL_FORMAT,
            normalized_input_sha256: ay_chc::normalized_chc_input_sha256(&problem),
            predicate_count: u64::try_from(model.len()).expect("small predicate inventory"),
            model_sha256: trust_mc_core::EvidenceHash::sha256_bytes(model_smtlib.as_bytes()).value,
            model_smtlib,
        };
        let bytes = serde_json::to_vec(&envelope).expect("test envelope serializes");
        ay_chc::parse_qf_invariant_model_artifact(&problem, &bytes)
            .expect("invalid model must nevertheless pass strict canonical parsing");
        bytes
    }

    fn assert_proved_verification_uses_normalized_input(
        solved: &TypedChcPdrFullVerification,
        expected: &NativeTypedChcPdrNormalizedInput,
    ) {
        assert_eq!(solved.route, expected.route);
        assert_eq!(solved.cache_key.parts.normalized_input_hash, expected.normalized_input_hash);
        assert_eq!(solved.cache_key.parts.obligation_set_hash, expected.obligation_set_hash);

        let trust_mc_core::FullVerificationVerdict::Proved {
            evidence: trust_mc_core::FullProofEvidence::ChcPdr(proof),
        } = &solved.verdict
        else {
            panic!("normalization parity requires a proved CHC/PDR verdict");
        };
        assert_eq!(proof.obligation.normalized_input, expected.normalized_input);
        assert_eq!(proof.obligation.normalized_input_hash, expected.normalized_input_hash);
        assert_eq!(
            proof.metadata.normalized_input_hash.as_ref(),
            Some(&expected.normalized_input_hash)
        );

        let normalized_inputs = proof
            .artifacts
            .iter()
            .filter(|artifact| {
                artifact.kind == trust_mc_core::FullVerificationArtifactKind::NormalizedInput
            })
            .collect::<Vec<_>>();
        let [artifact] = normalized_inputs.as_slice() else {
            panic!("proved verification must carry exactly one normalized-input artifact");
        };
        assert_eq!(artifact.digest.as_ref(), Some(&expected.normalized_input_hash));
        assert_eq!(
            artifact.materialized_bytes(),
            Some(expected.normalized_input.as_bytes()),
            "materialized proof bytes must equal the pre-solve normalized request"
        );
    }

    #[cfg(feature = "ay-chc-native")]
    fn native_test_obligation_source(
        source_id: &str,
        public_obligation_id: &str,
        semantic_payload: &[u8],
    ) -> trust_ir::ProofObligationSourceIdentity {
        trust_ir::ProofObligationSourceIdentity::new(source_id, "assertion:0").with_public(
            trust_ir::PublicObligationIdentity {
                obligation_id: public_obligation_id.to_string(),
                semantic_digest: trust_ir::ProofDigest::sha256_domain(
                    "trust-mc-driver.native-test.public-obligation.v1",
                    semantic_payload,
                ),
            },
        )
    }

    #[cfg(feature = "ay-chc-native")]
    fn refresh_native_test_bundle_module_identity(bundle: &mut trust_ir::NativeVerificationBundle) {
        if bundle.module.target_info.is_none() {
            bundle.module.target_info = Some(trust_ir::TargetInfo {
                triple: "x86_64-unknown-linux-gnu".to_string(),
                pointer_size: 8,
                endianness: trust_ir::Endianness::Little,
                abi: Some("sysv64".to_string()),
                struct_passing: trust_ir::StructPassingPolicy::NativeC,
            });
        }
        let digest = bundle.module.stable_digest();
        bundle.trust_ir_module_digest = digest;
        for node in &mut bundle.lineage.nodes {
            if bundle.lineage.roots.contains(&node.id) {
                node.target_module = digest;
            }
        }
    }

    #[cfg(feature = "ay-chc-native")]
    fn compiler_style_safe_trust_ir_bundle() -> trust_ir::NativeVerificationBundle {
        use trust_ir::inst::ICmpOp;
        use trust_ir::ty::Ty;
        use trust_ir::{
            NativeAdapterInput, NativeAssertionId, NativeBundleProducer, NativeCompilerFactRef,
            NativeCompilerFacts, NativeMonomorphizationFact, NativeMonomorphizationId,
            NativeObligationCause, NativeObligationSource, NativeReplayAtom, NativeReplayAtomId,
            NativeReplayContext, NativeRequestId, NativeRequestProvenance, NativeToolIdentity,
            NativeVerificationBundle, NativeVerificationRequest, ObligationKind, ProofDigest,
            ProofFormula, ProofId, ProofLineageId, ProofLineageManifest, ProofLineageNode,
            ProofObligation, ProofReplayIdentity, ProofStatus, ProofTransform, ProofTransformStage,
            TrustMcNativeRequest, TrustMcVerificationMode,
        };
        use trust_ir_build::ModuleBuilder;

        let source_digest = ProofDigest::sha256([0x61; 32]);
        let trust_ir_module_digest = ProofDigest::sha256([0x62; 32]);

        let mut mb = ModuleBuilder::new("native_trust_ir_chc_safe_bundle");
        let ft = mb.add_func_type(vec![Ty::I32], vec![]);
        {
            let mut fb = mb.function("trust_ir_native_checked_branch", ft);
            let entry = fb.create_block();
            let then_block = fb.create_block();
            let exit_block = fb.create_block();

            fb.switch_to_block(entry);
            fb.set_entry(entry);
            let x = fb.add_block_param(entry, Ty::I32);
            let zero = fb.iconst(Ty::I32, 0);
            let is_non_negative = fb.icmp(ICmpOp::Sge, Ty::I32, x, zero);
            fb.condbr(is_non_negative, then_block, vec![is_non_negative], exit_block, vec![]);

            let branch_fact = fb.add_block_param(then_block, Ty::Bool);
            fb.switch_to_block(then_block);
            fb.assert(branch_fact);
            fb.ret(vec![]);

            fb.switch_to_block(exit_block);
            fb.ret(vec![]);
            fb.build();
        }

        let mut module = mb.build();
        let trust_mc_function = module
            .functions
            .iter()
            .find(|func| func.name == "trust_ir_native_checked_branch")
            .expect("fixture includes requested trust-mc function")
            .id;
        module.proof_obligations.push(
            ProofObligation::new(
                ProofId::new(0),
                ObligationKind::PanicFreedom,
                ProofStatus::Pending,
                "native trust_ir branch assertion is unreachable",
            )
            .with_formula(ProofFormula::smtlib2("trust_ir_native_checked_branch_safe", "Bool"))
            .with_function(trust_mc_function)
            .with_source(native_test_obligation_source(
                "rust:native_trust_ir_chc_safe_bundle::trust_ir_native_checked_branch",
                "vc:trust-mc-driver:safe:0",
                b"trust_ir_native_checked_branch_safe",
            )),
        );

        let mut lineage_node = ProofLineageNode::new(
            ProofLineageId::new(0),
            ProofTransform::new(
                ProofTransformStage::Frontend,
                "rustc-mir-to-trust_ir",
                "tRust",
                "native-request-schema-v1",
            ),
            source_digest,
            trust_ir_module_digest,
        );
        lineage_node.obligations.push(ProofId::new(0));

        let lineage = ProofLineageManifest {
            schema_version: ProofLineageManifest::SCHEMA_VERSION,
            nodes: vec![lineage_node],
            roots: vec![ProofLineageId::new(0)],
        };

        let mut bundle = NativeVerificationBundle::new(
            NativeBundleProducer::TRust,
            NativeAdapterInput::RustMir { body_digest: source_digest },
            trust_ir_module_digest,
            module,
            lineage,
        );
        let source_span = trust_ir::SourceSpan { file: 0, line: 18, col: 13 };
        bundle.compiler_facts = NativeCompilerFacts {
            monomorphizations: vec![NativeMonomorphizationFact {
                id: NativeMonomorphizationId::new(0),
                source_item: "native_trust_ir_chc_safe_bundle::trust_ir_native_checked_branch"
                    .to_owned(),
                symbol: "_RNvNtC6native26trust_ir_native_checked_branch".to_owned(),
                generic_args: Vec::new(),
                function: Some(trust_mc_function),
                stable_digest: ProofDigest::sha256([0x63; 32]),
            }],
            obligation_sources: vec![NativeObligationSource {
                obligation: ProofId::new(0),
                public_obligation_id: "vc:trust-mc-driver:safe:0".to_string(),
                function: Some(trust_mc_function),
                span: Some(source_span),
                assertion_id: Some(NativeAssertionId::new(0)),
                cause: NativeObligationCause::Assert,
                monomorphization: Some(NativeMonomorphizationId::new(0)),
                facts: vec![NativeCompilerFactRef::Monomorphization(
                    NativeMonomorphizationId::new(0),
                )],
            }],
            ..NativeCompilerFacts::default()
        };
        bundle.requests.push(NativeVerificationRequest::TrustMc(TrustMcNativeRequest {
            id: NativeRequestId::new(7),
            mode: TrustMcVerificationMode::Chc,
            function: trust_mc_function,
            obligations: vec![ProofId::new(0)],
            lineage_roots: vec![ProofLineageId::new(0)],
            options: {
                let mut options = trust_ir::TrustMcRequestOptions::default();
                options.chc.emit_horn_clauses = true;
                options
            },
            diagnostics: Default::default(),
            provenance: NativeRequestProvenance::trust_mc(
                NativeToolIdentity::new("trust-mc").with_version("chc-v1"),
            )
            .with_solver(NativeToolIdentity::new("ay-chc").with_version("native-v1"))
            .with_replay(
                ProofReplayIdentity::new("trust-mc", "trust_mc native typed CHC/PDR test replay")
                    .with_transcript_digest(ProofDigest::sha256([0x64; 32])),
            )
            .with_replay_context(
                NativeReplayContext::default()
                    .with_atom(
                        NativeReplayAtom::assumption(
                            NativeReplayAtomId::new(0),
                            ProofFormula::smtlib2("trust_ir_native_checked_branch_guard", "Bool"),
                        )
                        .with_obligation(ProofId::new(0))
                        .with_span(source_span),
                    )
                    .with_atom(
                        NativeReplayAtom::assertion(
                            NativeReplayAtomId::new(1),
                            ProofFormula::smtlib2("trust_ir_native_checked_branch_safe", "Bool"),
                        )
                        .with_obligation(ProofId::new(0))
                        .with_assertion_id(NativeAssertionId::new(0))
                        .with_span(source_span),
                    ),
            ),
        }));
        refresh_native_test_bundle_module_identity(&mut bundle);
        bundle
    }

    #[test]
    fn native_proof_transport_deserialization_caps_untrusted_vectors() {
        let artifact = NativeTypedProofArtifactRef {
            kind: trust_mc_core::FullVerificationArtifactKind::SolverTranscript,
            uri: "artifact://test/transcript".to_string(),
            digest: None,
            byte_len: None,
            materialization: None,
        };
        let transport = NativeTypedChcPdrProofTransport {
            schema_version: NativeTypedChcPdrProofTransport::SCHEMA_VERSION,
            suite: "test-suite".to_string(),
            backend: "test-backend".to_string(),
            request_id: 1,
            proof_id: Some(2),
            native_id: "test-native-id".to_string(),
            proof_status: NativeTypedProofStatus::Proved,
            proof_strength: NativeTypedProofStrength::ChcValidity,
            solver_artifacts: Vec::new(),
            replay_artifacts: Vec::new(),
            check_artifacts: Vec::new(),
            response_artifacts: Vec::new(),
            replay_check_status: None,
            diagnostics: Vec::new(),
        };
        let base = serde_json::to_value(transport).expect("serialize transport");
        let artifact = serde_json::to_value(artifact).expect("serialize artifact");

        for (field, max, element, expected) in [
            (
                "solver_artifacts",
                MAX_NATIVE_PROOF_ROLE_ARTIFACTS,
                artifact.clone(),
                "native proof role artifacts exceeds the 8-entry limit",
            ),
            (
                "replay_artifacts",
                MAX_NATIVE_PROOF_ROLE_ARTIFACTS,
                artifact.clone(),
                "native proof role artifacts exceeds the 8-entry limit",
            ),
            (
                "check_artifacts",
                MAX_NATIVE_PROOF_ROLE_ARTIFACTS,
                artifact.clone(),
                "native proof role artifacts exceeds the 8-entry limit",
            ),
            (
                "response_artifacts",
                MAX_NATIVE_PROOF_RESPONSE_ARTIFACTS,
                artifact,
                "native proof response artifacts exceeds the 16-entry limit",
            ),
            (
                "diagnostics",
                MAX_NATIVE_PROOF_DIAGNOSTICS,
                serde_json::Value::String("diagnostic".to_string()),
                "native proof diagnostics exceeds the 64-entry limit",
            ),
        ] {
            let mut hostile = base.clone();
            hostile[field] = serde_json::Value::Array(vec![element; max + 1]);
            let error = serde_json::from_value::<NativeTypedChcPdrProofTransport>(hostile)
                .expect_err("oversized native transport vector must fail closed");
            assert!(error.to_string().contains(expected), "{field}: {error}");
        }
    }

    #[test]
    fn finite_acyclic_bmc_provenance_is_explicit() {
        let provenance = NativeProofProvenance::finite_acyclic_bmc(5);

        assert_eq!(provenance.proof_mode, NativeProofMode::FiniteAcyclicBmc);
        assert_eq!(provenance.bmc_depth, Some(5));
        assert!(provenance.finite_acyclic);
        assert!(provenance.proof_mode.is_finite_acyclic_bmc());
        assert!(!provenance.proof_mode.is_bounded());
    }

    #[test]
    fn native_full_verification_classifier_rejects_public_chc_validity_candidate() {
        let proof =
            trust_mc_core::ChcPdrProofEvidence::try_chc_validity_candidate_from_linked_bytes(
                trust_mc_core_obligation(),
                trust_mc_core::ChcPdrStats { relation_count: 2, clause_count: 3 },
                ("artifact://trust_mc/solver-transcript.smt2", b"solver transcript"),
                ("artifact://trust_mc/replay.jsonl", b"replay log"),
                ("artifact://trust_mc/checked-proof.json", b"checked proof report"),
            )
            .expect("test proof artifacts are nonempty and bounded");
        let verdict = trust_mc_core::FullVerificationVerdict::Proved {
            evidence: trust_mc_core::FullProofEvidence::ChcPdr(proof),
        };

        assert!(!is_proof_grade_native_full_verification_verdict(&verdict));
        let trust_mc_core::ProofGradeVerdict::NotProofGrade { reasons, .. } =
            classify_native_full_verification_verdict(&verdict)
        else {
            panic!("public candidate bytes must not self-certify");
        };
        assert_eq!(
            reasons,
            vec![trust_mc_core::CHC_VALIDITY_FRESH_CONSUMER_REPLAY_REQUIRED.to_string()]
        );
        trust_mc_core::validated_chc_pdr_candidate(&verdict)
            .expect("candidate structure should remain available for private replay");
    }

    #[test]
    fn native_full_verification_classifier_rejects_diagnostic_bmc() {
        let verdict = trust_mc_core::FullVerificationVerdict::DiagnosticOnly {
            evidence: trust_mc_core::DiagnosticOnlyEvidence {
                problem_kind: trust_mc_core::FullVerificationProblemKind::DiagnosticBmc,
                summary: String::from("bounded diagnostic BMC returned SAFE at depth 8"),
                artifacts: Vec::new(),
            },
        };

        assert!(!is_proof_grade_native_full_verification_verdict(&verdict));
        let trust_mc_core::ProofGradeVerdict::NotProofGrade { problem_kind, reasons } =
            classify_native_full_verification_verdict(&verdict)
        else {
            panic!("diagnostic BMC must not classify as proof-grade");
        };
        assert_eq!(problem_kind, Some(trust_mc_core::FullVerificationProblemKind::DiagnosticBmc));
        assert!(reasons.iter().any(|reason| reason.contains("diagnostic-only evidence")));
        assert!(reasons.iter().any(|reason| reason.contains("diagnostic BMC is bounded evidence")));
    }

    #[test]
    fn normalized_typed_chc_pdr_input_is_deterministic_and_selects_trivial_route() {
        let obligation = typed_chc_obligation(false);
        let first = normalized_typed_chc_pdr_input(&obligation)
            .expect("valid trivial typed CHC should normalize");
        let second = normalized_typed_chc_pdr_input(&obligation.clone())
            .expect("an exact request clone should normalize identically");

        assert_eq!(first.route, TypedChcPdrRoute::TriviallySafe);
        assert_eq!(first, second);
        assert_eq!(
            first.normalized_input_hash,
            trust_mc_core::EvidenceHash::sha256_bytes(first.normalized_input.as_bytes())
        );
        assert!(first.normalized_input.contains("trust_mc.typed-chc-pdr-obligation-set/v2"));
    }

    #[test]
    #[cfg(feature = "ay-chc-native")]
    fn normalized_typed_chc_pdr_input_tracks_semantics_not_constraint_storage() {
        let obligation = safe_nontrivial_typed_chc_obligation();
        let expected = normalized_typed_chc_pdr_input(&obligation)
            .expect("valid nontrivial typed CHC should normalize");
        assert_eq!(expected.route, TypedChcPdrRoute::PdrProof);

        // `Owned` and `Shared` are storage variants for the same ordered
        // constraints.  They must not produce different proof identities.
        let mut storage_variant = obligation.clone();
        let error_rule = storage_variant.vc.rules.last_mut().expect("fixture has an error rule");
        let shared_constraints: std::sync::Arc<[ay_bindings::Expr]> =
            error_rule.body.constraints.iter().cloned().collect::<Vec<_>>().into();
        error_rule.body = trust_mc_core::RuleBody::from_shared_base(
            error_rule.body.relation.clone(),
            shared_constraints,
            std::iter::empty(),
        );
        let storage_normalized = normalized_typed_chc_pdr_input(&storage_variant)
            .expect("semantically identical storage variant should normalize");
        assert_eq!(expected, storage_normalized);

        // Mutating the actual error condition must change the request-derived
        // identity before any proof or cache entry exists.
        let mut semantic_mutation = obligation;
        let error_rule = semantic_mutation.vc.rules.last_mut().expect("fixture has an error rule");
        error_rule.body = trust_mc_core::RuleBody::new(
            error_rule.body.relation.clone(),
            vec![ay_bindings::Expr::bool_const(true)],
        );
        let mutated = normalized_typed_chc_pdr_input(&semantic_mutation)
            .expect("valid semantic mutation should normalize");
        assert_eq!(mutated.route, TypedChcPdrRoute::PdrProof);
        assert_ne!(expected.normalized_input, mutated.normalized_input);
        assert_ne!(expected.normalized_input_hash, mutated.normalized_input_hash);
        assert_ne!(expected.obligation_set_hash, mutated.obligation_set_hash);
    }

    #[test]
    fn solve_typed_chc_pdr_trivial_safe_returns_public_candidate_status() {
        let request = trust_mc_core::ChcPdrSolveRequest::new(typed_chc_obligation(false));
        let solved = solve_typed_chc_pdr(request).expect("trivial CHC should be proved");

        assert_eq!(solved.obligation_id, "typed-obligation");
        assert_eq!(
            solved.status,
            trust_mc_core::ChcPdrSolveStatus::Unknown {
                reason: trust_mc_core::CHC_VALIDITY_FRESH_CONSUMER_REPLAY_REQUIRED.to_string(),
            }
        );
        assert_eq!(solved.stats, trust_mc_core::ChcPdrStats { relation_count: 2, clause_count: 1 });
        assert!(solved.diagnostics.iter().any(|line| line.contains("`error`")));
    }

    #[test]
    fn solve_typed_chc_pdr_full_trivial_safe_returns_reject_only_candidate() {
        let obligation = typed_chc_obligation(false);
        let expected_normalized = normalized_typed_chc_pdr_input(&obligation)
            .expect("pre-solve trivial request should normalize");
        let request = trust_mc_core::ChcPdrSolveRequest::new(obligation);
        let solved =
            solve_typed_chc_pdr_full_verification(request).expect("typed trivial CHC should solve");

        assert_eq!(solved.route, TypedChcPdrRoute::TriviallySafe);
        assert_proved_verification_uses_normalized_input(&solved, &expected_normalized);
        solved.cache_key.validate().expect("trivial full-verification cache key should validate");
        assert!(solved.artifact_directory.ends_with(&solved.cache_key.key.value));
        assert_eq!(
            solved.outcome.status,
            trust_mc_core::ChcPdrSolveStatus::Unknown {
                reason: trust_mc_core::CHC_VALIDITY_FRESH_CONSUMER_REPLAY_REQUIRED.to_string(),
            }
        );
        assert!(!is_proof_grade_native_full_verification_verdict(&solved.verdict));
        trust_mc_core::validated_chc_pdr_candidate(&solved.verdict)
            .expect("driver candidate structure should validate");
        assert!(solved.authorized_native_proof().is_err());
        let expected_cache_key = solved.cache_key.key.clone();

        let trust_mc_core::FullVerificationVerdict::Proved {
            evidence: trust_mc_core::FullProofEvidence::ChcPdr(proof),
        } = solved.verdict
        else {
            panic!("typed trivial CHC should produce CHC/PDR proof evidence");
        };
        assert_eq!(proof.metadata.cache_key.as_ref(), Some(&expected_cache_key));
        assert!(
            proof.artifacts.iter().any(|artifact| artifact.kind
                == trust_mc_core::FullVerificationArtifactKind::TypedChcProblem),
            "typed full verification evidence must include a typed CHC problem artifact"
        );
    }

    #[test]
    fn normalized_typed_chc_pdr_input_predicts_trivial_solve_identity_bytes() {
        let obligation = typed_chc_obligation(false);
        let expected = normalized_typed_chc_pdr_input(&obligation)
            .expect("valid trivial typed CHC should normalize");
        let again = normalized_typed_chc_pdr_input(&obligation.clone())
            .expect("an exact request clone should normalize identically");
        assert_eq!(expected, again, "pre-solve normalization must be deterministic");
        assert_eq!(expected.route, TypedChcPdrRoute::TriviallySafe);

        // The independent pre-solve derivation must equal every producer-authored
        // identity field a genuine solve publishes — this is the consumer-side
        // binding that makes a returned proof non-transplantable.
        let solved = solve_typed_chc_pdr_full_verification(trust_mc_core::ChcPdrSolveRequest::new(
            obligation,
        ))
        .expect("typed trivial CHC should solve");
        assert_eq!(solved.route, expected.route);
        assert_eq!(
            solved.cache_key.parts.normalized_input_hash, expected.normalized_input_hash,
            "cache-key normalized-input digest must equal the independent pre-solve derivation"
        );
        assert_eq!(
            solved.cache_key.parts.obligation_set_hash, expected.obligation_set_hash,
            "cache-key obligation-set digest must equal the independent pre-solve derivation"
        );
        let trust_mc_core::FullVerificationVerdict::Proved {
            evidence: trust_mc_core::FullProofEvidence::ChcPdr(proof),
        } = solved.verdict
        else {
            panic!("typed trivial CHC should produce CHC/PDR proof evidence");
        };
        assert_eq!(
            proof.obligation.normalized_input, expected.normalized_input,
            "evidence-layer canonical bytes must equal the pre-solve derivation"
        );
        assert_eq!(
            proof.obligation.normalized_input_hash, expected.normalized_input_hash,
            "evidence digest must equal the cache-key digest (trailing-newline skew regression)"
        );
    }

    #[test]
    fn solve_typed_chc_pdr_native_proof_grade_requires_native_metadata() {
        let request = trust_mc_core::ChcPdrSolveRequest::new(typed_chc_obligation(false));
        let err = solve_typed_chc_pdr_native_proof_grade(request)
            .expect_err("metadata-free typed proof must not satisfy native proof admission");

        let NativeSolveError::ProofGradeRejected { rejection } = err else {
            panic!("metadata-free proof should be rejected by native proof-grade admission");
        };
        assert_eq!(
            rejection.problem_kind,
            Some(trust_mc_core::FullVerificationProblemKind::ChcPdr)
        );
        assert!(
            rejection
                .reasons
                .iter()
                .any(|reason| reason.contains("missing native typed CHC obligation metadata"))
        );
    }

    #[test]
    fn typed_full_chc_routing_uses_typed_query_target_not_text_error_scan() {
        let request =
            trust_mc_core::ChcPdrSolveRequest::new(typed_chc_obligation_with_non_error_query());
        let solved = solve_typed_chc_pdr_full_verification(request)
            .expect("typed non-error query should route without SMT text classification");

        assert_eq!(
            solved.route,
            TypedChcPdrRoute::TriviallySafe,
            "typed route must ignore misleading non-query `error` rules"
        );
        solved.cache_key.validate().expect("typed routing cache key should validate");
        assert!(
            solved.outcome.diagnostics.iter().any(|line| line.contains("`panic_target`")),
            "diagnostics should name the typed query target"
        );
        assert!(!is_proof_grade_native_full_verification_verdict(&solved.verdict));
        trust_mc_core::validated_chc_pdr_candidate(&solved.verdict)
            .expect("typed query routing should emit a structurally valid candidate");
        assert!(solved.authorized_native_proof().is_err());
    }

    #[test]
    fn native_typed_chc_pdr_runner_solves_trivial_full_verification() {
        let runner = NativeTypedChcPdrRunner::new();
        let solved = runner
            .solve_full_verification(typed_chc_obligation(false))
            .expect("typed runner should solve trivial full verification");

        assert_eq!(runner.options().engine, trust_mc_core::ChcPdrEngine::Auto);
        assert_eq!(solved.route, TypedChcPdrRoute::TriviallySafe);
        solved.cache_key.validate().expect("runner cache key should validate");
        assert!(!is_proof_grade_native_full_verification_verdict(&solved.verdict));
        trust_mc_core::validated_chc_pdr_candidate(&solved.verdict)
            .expect("generic runner should retain reject-only candidate evidence");
        assert!(solved.authorized_native_proof().is_err());
    }

    #[test]
    fn native_typed_chc_pdr_runner_rejects_native_trivial_safe_proof_grade() {
        let runner = NativeTypedChcPdrRunner::new();
        let err = runner
            .solve_native_proof_grade(typed_native_chc_obligation(false))
            .expect_err("native metadata-bound trivial CHC proof must fail closed");

        match err {
            NativeSolveError::Unsupported(unsupported) => {
                assert_eq!(unsupported.operation, NativeOperation::Solve);
                assert_eq!(unsupported.reason, "native_trust_ir_trivial_safe_chc_not_proof_grade");
                assert!(unsupported.detail.contains("trust_ir-native-trust_mc-request-7-proof-0"));
                assert!(unsupported.detail.contains("`error`"));
            }
            NativeSolveError::InvalidInput { .. } => panic!("native metadata shape is valid"),
            NativeSolveError::SolverFailed { .. } => {
                panic!("trivial-safe guard runs before solver")
            }
            NativeSolveError::ProofGradeRejected { .. } => {
                panic!("trivial-safe native trust_ir must fail before proof admission")
            }
        }
    }

    // A public structural-completeness claim is serialized and forgeable. It may
    // permit candidate construction but can never mint private authority.
    #[test]
    fn public_structural_complete_marker_cannot_mint_private_authority() {
        let runner = NativeTypedChcPdrRunner::new();
        let obligation = typed_native_chc_obligation_structural_complete(false);
        let solved = runner
            .solve_full_verification(obligation.clone())
            .expect("forgeable marker may produce a reject-only candidate");
        assert_eq!(solved.route, TypedChcPdrRoute::TriviallySafe);
        assert_eq!(
            solved.outcome.status,
            trust_mc_core::ChcPdrSolveStatus::Unknown {
                reason: trust_mc_core::CHC_VALIDITY_FRESH_CONSUMER_REPLAY_REQUIRED.to_string(),
            }
        );
        assert!(trust_mc_core::validated_native_typed_chc_pdr_candidate(&solved.verdict).is_ok());
        assert!(solved.authorized_native_proof().is_err());
        let err = runner
            .solve_native_proof_grade(obligation)
            .expect_err("generic strict runner must not trust the public marker");
        assert!(matches!(err, NativeSolveError::ProofGradeRejected { .. }));
    }

    // LINCHPIN adversarial (c) — THE forgery gate; the reason this lane exists.
    // A CHC that omits the `error` rule for a reachable panic block remains
    // non-authoritative even when an attacker forges the public marker.
    #[test]
    fn forged_marker_on_dropped_assertion_stays_fail_closed() {
        let mut vc = trust_mc_core::ChcVc::new();
        vc.add_relation(trust_mc_core::RelationDecl::nullary("entry"));
        vc.add_relation(trust_mc_core::RelationDecl::nullary("panic_block"));
        vc.add_relation(trust_mc_core::RelationDecl::nullary("error"));
        vc.query = trust_mc_core::ChcQuery::new().with_target("error");
        // entry is a fact and entry -> panic_block is reachable...
        vc.add_rule(trust_mc_core::Rule::new(
            trust_mc_core::RuleBody::empty(),
            trust_mc_core::RelationApp::nullary("entry"),
        ));
        vc.add_rule(trust_mc_core::Rule::new(
            trust_mc_core::RuleBody::new(
                Some(trust_mc_core::RelationApp::nullary("entry")),
                vec![],
            ),
            trust_mc_core::RelationApp::nullary("panic_block"),
        ));
        // ...but the `error :- panic_block` edge was DROPPED. `is_trivially_safe`
        // is therefore true even though panic_block is genuinely reachable.
        let mut obligation = typed_native_chc_obligation(false);
        obligation.vc = vc;
        let metadata = obligation
            .native_metadata
            .take()
            .expect("obligation carries metadata")
            .with_structural_reachability_complete(true);
        obligation = obligation.with_native_metadata(metadata);
        assert!(
            obligation.is_trivially_safe(),
            "a dropped-assertion CHC reads as trivially-safe by rule-head scan alone"
        );
        assert!(
            obligation
                .native_metadata
                .as_ref()
                .expect("obligation carries metadata")
                .structural_reachability_complete,
            "the attack deliberately forges the diagnostic marker"
        );

        let runner = NativeTypedChcPdrRunner::new();
        let candidate = runner
            .solve_full_verification(obligation.clone())
            .expect("forged marker can at most produce a reject-only candidate");
        assert!(candidate.authorized_native_proof().is_err());
        assert!(candidate.native_proof_transport_record().is_err());
        let err = runner
            .solve_native_proof_grade(obligation)
            .expect_err("forged marker must not cross the private authority boundary");
        assert!(matches!(err, NativeSolveError::ProofGradeRejected { .. }));
    }

    #[test]
    fn typed_full_verification_cache_key_changes_with_options() {
        let auto = solve_typed_chc_pdr_full_verification(trust_mc_core::ChcPdrSolveRequest::new(
            typed_chc_obligation(false),
        ))
        .expect("default typed full verification should solve");
        let pdr = solve_typed_chc_pdr_full_verification(
            trust_mc_core::ChcPdrSolveRequest::new(typed_chc_obligation(false)).with_options(
                trust_mc_core::ChcPdrSolveOptions::default()
                    .with_engine(trust_mc_core::ChcPdrEngine::Pdr)
                    .with_timeout(Duration::from_secs(3)),
            ),
        )
        .expect("PDR-option typed full verification should solve");

        auto.cache_key.validate().expect("auto cache key should validate");
        pdr.cache_key.validate().expect("PDR cache key should validate");
        assert_ne!(auto.cache_key.key, pdr.cache_key.key);
        assert_ne!(auto.artifact_directory, pdr.artifact_directory);
    }

    #[test]
    #[cfg(feature = "ay-chc-native")]
    fn solve_typed_chc_pdr_full_nontrivial_safe_returns_direct_smt_candidate() {
        let obligation = safe_nontrivial_typed_chc_obligation();
        let expected_normalized = normalized_typed_chc_pdr_input(&obligation)
            .expect("pre-solve PDR request should normalize");
        let request = trust_mc_core::ChcPdrSolveRequest::new(obligation).with_options(
            trust_mc_core::ChcPdrSolveOptions::default()
                .with_engine(trust_mc_core::ChcPdrEngine::Pdr)
                .with_timeout(Duration::from_secs(10)),
        );
        let solved =
            solve_typed_chc_pdr_full_verification(request).expect("typed PDR proof should solve");

        assert_eq!(solved.route, TypedChcPdrRoute::PdrProof);
        assert_proved_verification_uses_normalized_input(&solved, &expected_normalized);
        solved.cache_key.validate().expect("typed PDR cache key should validate");
        assert!(solved.artifact_directory.ends_with(&solved.cache_key.key.value));
        assert_eq!(
            solved.outcome.status,
            trust_mc_core::ChcPdrSolveStatus::Unknown {
                reason: trust_mc_core::CHC_VALIDITY_FRESH_CONSUMER_REPLAY_REQUIRED.to_string(),
            }
        );
        assert!(!is_proof_grade_native_full_verification_verdict(&solved.verdict));
        let candidate = trust_mc_core::validated_chc_pdr_candidate(&solved.verdict)
            .expect("direct-SMT candidate structure should validate");
        assert_eq!(candidate.proof_kind, trust_mc_core::ChcPdrProofKind::ChcValidity);
        assert!(solved.authorized_native_proof().is_err());
        let expected_cache_key = solved.cache_key.key.clone();

        let trust_mc_core::FullVerificationVerdict::Proved {
            evidence: trust_mc_core::FullProofEvidence::ChcPdr(proof),
        } = solved.verdict
        else {
            panic!("typed PDR solve should produce CHC/PDR proof evidence");
        };
        assert_eq!(proof.kind, trust_mc_core::ChcPdrProofKind::ChcValidity);
        assert_eq!(proof.metadata.cache_key.as_ref(), Some(&expected_cache_key));
        assert!(proof.artifacts.iter().any(|artifact| artifact.kind
            == trust_mc_core::FullVerificationArtifactKind::TypedChcProblem));
        assert!(!proof.artifacts.iter().any(|artifact| artifact.kind
            == trust_mc_core::FullVerificationArtifactKind::PdrInvariantModel));
    }

    #[test]
    #[cfg(feature = "ay-chc-native")]
    fn native_typed_chc_pdr_runner_solves_nontrivial_pdr_without_compiler_api() {
        let runner = NativeTypedChcPdrRunner::with_options(
            trust_mc_core::ChcPdrSolveOptions::default()
                .with_engine(trust_mc_core::ChcPdrEngine::Pdr)
                .with_timeout(Duration::from_secs(10)),
        );
        let solved = runner
            .solve_full_verification(safe_nontrivial_typed_chc_obligation())
            .expect("library-only typed runner should solve native PDR evidence");

        assert_eq!(solved.route, TypedChcPdrRoute::PdrProof);
        solved.cache_key.validate().expect("runner PDR cache key should validate");
        assert_eq!(
            solved.outcome.status,
            trust_mc_core::ChcPdrSolveStatus::Unknown {
                reason: trust_mc_core::CHC_VALIDITY_FRESH_CONSUMER_REPLAY_REQUIRED.to_string(),
            },
            "generic direct-SMT solving must remain a source-unbound candidate"
        );
        assert!(!is_proof_grade_native_full_verification_verdict(&solved.verdict));
        assert!(solved.authorized_native_proof().is_err());
    }

    #[test]
    #[cfg(feature = "ay-chc-native")]
    fn exact_typed_pdr_fresh_replay_mints_affine_chc_authority() {
        let runner = NativeTypedChcPdrRunner::with_options(
            trust_mc_core::ChcPdrSolveOptions::default()
                .with_engine(trust_mc_core::ChcPdrEngine::Pdr)
                .with_timeout(Duration::from_secs(10)),
        );
        let solved = runner
            .solve_full_verification_with_fresh_exact_replay(safe_cyclic_typed_chc_obligation(
                "trust_ir-native-trust_mc-request-7-proof-0",
                10,
            ))
            .expect("safe cyclic CHC should solve and replay");

        assert_eq!(
            solved.outcome.status,
            trust_mc_core::ChcPdrSolveStatus::Unknown {
                reason: trust_mc_core::PDR_INVARIANT_FRESH_CONSUMER_REPLAY_REQUIRED.to_string(),
            },
            "public candidate status remains detached from private replay authority"
        );
        let authority = solved
            .authorized_native_proof()
            .expect("fresh strict replay should retain opaque CHC authority");
        assert_eq!(
            authority.transport_record().proof_strength,
            NativeTypedProofStrength::PdrInvariant
        );
        assert!(
            solved.clone().authorized_native_proof().is_err(),
            "cloning the public response must drop the affine private seal"
        );
    }

    #[test]
    #[cfg(feature = "ay-chc-native")]
    fn exact_typed_chc_validity_replay_mints_affine_chc_authority() {
        let runner = NativeTypedChcPdrRunner::with_options(
            trust_mc_core::ChcPdrSolveOptions::default()
                .with_engine(trust_mc_core::ChcPdrEngine::Pdr)
                .with_timeout(Duration::from_secs(10)),
        );
        let mut obligation = safe_nontrivial_typed_chc_obligation();
        obligation.obligation_id = "trust_ir-native-trust_mc-request-7-proof-0".to_string();
        obligation.native_metadata = typed_native_chc_obligation(false).native_metadata;
        let solved = runner
            .solve_full_verification_with_fresh_exact_replay(obligation)
            .expect("safe acyclic CHC should solve and replay");

        assert_eq!(
            solved.outcome.status,
            trust_mc_core::ChcPdrSolveStatus::Unknown {
                reason: trust_mc_core::CHC_VALIDITY_FRESH_CONSUMER_REPLAY_REQUIRED.to_string(),
            },
            "public candidate status remains detached from private replay authority"
        );
        let authority = solved
            .authorized_native_proof()
            .expect("fresh exhaustive replay should retain opaque CHC authority");
        assert_eq!(
            authority.transport_record().proof_strength,
            NativeTypedProofStrength::ChcValidity
        );
        assert!(
            solved.clone().authorized_native_proof().is_err(),
            "cloning the public response must drop the affine private seal"
        );
    }

    #[test]
    #[cfg(feature = "ay-chc-native")]
    fn exact_pdr_authority_rejects_live_mutations_and_foreign_verdict() {
        let runner = NativeTypedChcPdrRunner::with_options(
            trust_mc_core::ChcPdrSolveOptions::default()
                .with_engine(trust_mc_core::ChcPdrEngine::Pdr)
                .with_timeout(Duration::from_secs(10)),
        );
        let solve = || {
            runner
                .solve_full_verification_with_fresh_exact_replay(safe_cyclic_typed_chc_obligation(
                    "trust_ir-native-trust_mc-request-7-proof-0",
                    10,
                ))
                .expect("fixture replays")
        };

        let mut outcome_mutation = solve();
        outcome_mutation.outcome.diagnostics.push("forged post-replay diagnostic".to_string());
        assert!(outcome_mutation.authorized_native_proof().is_err());

        let mut cache_mutation = solve();
        let mut cache_parts = cache_mutation.cache_key.parts.clone();
        cache_parts.normalized_input_hash =
            trust_mc_core::EvidenceHash::sha256_bytes(b"foreign normalized input");
        cache_mutation.cache_key = trust_mc_core::FullVerificationCacheKey::from_parts(cache_parts);
        assert!(cache_mutation.authorized_native_proof().is_err());

        let mut artifact_mutation = solve();
        let trust_mc_core::FullVerificationVerdict::Proved {
            evidence: trust_mc_core::FullProofEvidence::ChcPdr(proof),
        } = &mut artifact_mutation.verdict
        else {
            panic!("fixture carries PDR evidence");
        };
        let model = proof
            .artifacts
            .iter_mut()
            .find(|artifact| {
                artifact.kind == trust_mc_core::FullVerificationArtifactKind::PdrInvariantModel
            })
            .expect("fixture carries a model");
        *model = trust_mc_core::FullVerificationArtifact::try_from_bytes(
            trust_mc_core::FullVerificationArtifactKind::PdrInvariantModel,
            "trust-mc://adversarial/mutated-model.json",
            b"{}",
        )
        .expect("small mutation materializes");
        assert!(artifact_mutation.authorized_native_proof().is_err());

        let foreign = runner
            .solve_full_verification(safe_cyclic_typed_chc_obligation(
                "trust_ir-native-trust_mc-request-7-proof-0",
                20,
            ))
            .expect("foreign candidate solves");
        let mut verdict_transplant = solve();
        verdict_transplant.verdict = foreign.verdict;
        assert!(verdict_transplant.authorized_native_proof().is_err());
    }

    #[test]
    #[cfg(feature = "ay-chc-native")]
    fn exact_pdr_replay_rejects_malformed_missing_duplicate_foreign_and_invalid_models() {
        let runner = NativeTypedChcPdrRunner::with_options(
            trust_mc_core::ChcPdrSolveOptions::default()
                .with_engine(trust_mc_core::ChcPdrEngine::Pdr)
                .with_timeout(Duration::from_secs(10)),
        );
        let obligation =
            safe_cyclic_typed_chc_obligation("trust_ir-native-trust_mc-request-7-proof-0", 10);
        let candidate = || {
            runner.solve_full_verification(obligation.clone()).expect("fixture candidate solves")
        };
        let seal = |verification: TypedChcPdrFullVerification| {
            verification.with_private_exact_typed_replay_authority(&obligation, runner.options())
        };

        let malformed = rebuild_pdr_candidate_with_model(candidate(), b"{");
        assert!(seal(malformed).authorized_native_proof().is_err());

        let mut missing = candidate();
        let trust_mc_core::FullVerificationVerdict::Proved {
            evidence: trust_mc_core::FullProofEvidence::ChcPdr(proof),
        } = &mut missing.verdict
        else {
            panic!("fixture carries PDR evidence");
        };
        proof.artifacts.retain(|artifact| {
            artifact.kind != trust_mc_core::FullVerificationArtifactKind::PdrInvariantModel
        });
        assert!(seal(missing).authorized_native_proof().is_err());

        let mut duplicate = candidate();
        let trust_mc_core::FullVerificationVerdict::Proved {
            evidence: trust_mc_core::FullProofEvidence::ChcPdr(proof),
        } = &mut duplicate.verdict
        else {
            panic!("fixture carries PDR evidence");
        };
        let extra = proof
            .artifacts
            .iter()
            .find(|artifact| {
                artifact.kind == trust_mc_core::FullVerificationArtifactKind::PdrInvariantModel
            })
            .expect("fixture model")
            .clone();
        proof.artifacts.push(extra);
        assert!(seal(duplicate).authorized_native_proof().is_err());

        let mut wrong_kind = candidate();
        let trust_mc_core::FullVerificationVerdict::Proved {
            evidence: trust_mc_core::FullProofEvidence::ChcPdr(proof),
        } = &mut wrong_kind.verdict
        else {
            panic!("fixture carries PDR evidence");
        };
        proof
            .artifacts
            .iter_mut()
            .find(|artifact| {
                artifact.kind == trust_mc_core::FullVerificationArtifactKind::PdrInvariantModel
            })
            .expect("fixture model")
            .kind = trust_mc_core::FullVerificationArtifactKind::DiagnosticTrace;
        assert!(seal(wrong_kind).authorized_native_proof().is_err());

        let foreign = runner
            .solve_full_verification(safe_cyclic_typed_chc_obligation(
                "trust_ir-native-trust_mc-request-7-proof-0",
                20,
            ))
            .expect("foreign candidate solves");
        let trust_mc_core::FullVerificationVerdict::Proved {
            evidence: trust_mc_core::FullProofEvidence::ChcPdr(foreign_proof),
        } = &foreign.verdict
        else {
            panic!("foreign fixture carries PDR evidence");
        };
        let foreign_bytes = foreign_proof
            .artifacts
            .iter()
            .find(|artifact| {
                artifact.kind == trust_mc_core::FullVerificationArtifactKind::PdrInvariantModel
            })
            .and_then(trust_mc_core::FullVerificationArtifact::materialized_bytes)
            .expect("foreign model")
            .to_vec();
        let foreign_model = rebuild_pdr_candidate_with_model(candidate(), &foreign_bytes);
        assert!(seal(foreign_model).authorized_native_proof().is_err());

        let invalid_bytes = invalid_but_canonical_pdr_model_bytes(&obligation);
        let invalid_model = rebuild_pdr_candidate_with_model(candidate(), &invalid_bytes);
        assert!(seal(invalid_model).authorized_native_proof().is_err());

        let mut mutated_obligation = obligation.clone();
        let error_rule = mutated_obligation.vc.rules.last_mut().expect("error rule");
        error_rule.body = trust_mc_core::RuleBody::new(
            error_rule.body.relation.clone(),
            vec![ay_bindings::Expr::bool_const(true)],
        );
        let mismatched = candidate()
            .with_private_exact_typed_replay_authority(&mutated_obligation, runner.options());
        assert!(mismatched.authorized_native_proof().is_err());
    }

    #[test]
    #[cfg(all(feature = "ay-chc-native", feature = "native-trust-ir-bundle"))]
    fn generic_and_whole_bundle_pdr_candidates_remain_reject_only() {
        let runner = NativeTypedChcPdrRunner::with_options(
            trust_mc_core::ChcPdrSolveOptions::default()
                .with_engine(trust_mc_core::ChcPdrEngine::Pdr)
                .with_timeout(Duration::from_secs(10)),
        );
        let obligation =
            safe_cyclic_typed_chc_obligation("trust_ir-native-trust_mc-request-7-proof-0", 10);
        let generic = runner
            .solve_full_verification(obligation.clone())
            .expect("generic PDR candidate solves");
        assert!(generic.authorized_native_proof().is_err());
        let candidate = trust_mc_core::validated_native_typed_chc_pdr_candidate(&generic.verdict)
            .expect("generic candidate validates structurally");
        assert_eq!(candidate.proof_kind, trust_mc_core::ChcPdrProofKind::PdrInvariant);

        let bundle = compiler_style_safe_trust_ir_bundle();
        let mut translated = trust_mc_trust_bmc::trust_mc_chc_pdr_obligations_from_native_bundle(
            &bundle,
            &trust_mc_trust_bmc::TranslateOptions::default(),
        )
        .expect("bundle translates")
        .into_iter()
        .next()
        .expect("one translated request");
        translated.obligation = obligation;
        let bundle_candidate = runner
            .solve_full_verification(translated.obligation.clone())
            .expect("replacement PDR candidate solves")
            .with_private_native_bundle_authority(&translated, runner.options());
        assert!(
            bundle_candidate.authorized_native_proof().is_err(),
            "N:1 whole-function PDR evidence must remain diagnostic without a row-membership receipt"
        );
    }

    #[test]
    #[cfg(feature = "ay-chc-native")]
    fn source_unbound_translated_chc_cannot_mint_direct_smt_authority() {
        let bundle = compiler_style_safe_trust_ir_bundle();
        let obligations = trust_mc_trust_bmc::trust_mc_chc_pdr_obligations_from_native_bundle(
            &bundle,
            &trust_mc_trust_bmc::TranslateOptions::default(),
        )
        .expect("typed native trust_ir bundle should translate to CHC/PDR obligations");

        assert_eq!(obligations.len(), 1);
        let translated = obligations.into_iter().next().expect("one translated obligation");
        assert_eq!(translated.request_id, trust_ir::NativeRequestId::new(7));
        assert_eq!(translated.obligations, vec![trust_ir::ProofId::new(0)]);
        assert_eq!(translated.lineage_roots, vec![trust_ir::ProofLineageId::new(0)]);
        assert_eq!(translated.obligation.function_name, "trust_ir_native_checked_branch");
        translated
            .obligation
            .validate()
            .expect("translated trust_ir CHC/PDR obligation should validate");
        assert!(
            !translated.obligation.is_trivially_safe(),
            "fixture must force native PDR instead of trivial CHC-validity routing"
        );
        assert!(
            translated.obligation.vc.rules.iter().any(|rule| rule.head.name == "error"),
            "fixture should contain a real typed error rule"
        );

        let runner = NativeTypedChcPdrRunner::with_options(
            trust_mc_core::ChcPdrSolveOptions::default()
                .with_engine(trust_mc_core::ChcPdrEngine::Pdr)
                .with_timeout(Duration::from_secs(10)),
        );
        let solved = runner
            .solve_full_verification(translated.obligation)
            .expect("native ay-chc should produce a source-unbound candidate");

        assert_eq!(solved.route, TypedChcPdrRoute::PdrProof);
        solved.cache_key.validate().expect("native trust_ir cache key should validate");
        assert!(
            solved.cache_key.parts.trust_ir_snapshot.is_some(),
            "trust_ir native metadata should contribute a compiler snapshot to the cache key"
        );
        // The exact CHC is acyclic and safe, but a detached translated
        // obligation does not carry the fresh bundle/module authority needed to
        // cross the compiler boundary.
        assert_eq!(
            solved.outcome.status,
            trust_mc_core::ChcPdrSolveStatus::Unknown {
                reason: trust_mc_core::CHC_VALIDITY_FRESH_CONSUMER_REPLAY_REQUIRED.to_string(),
            }
        );
        assert_eq!(
            solved.outcome.stats,
            trust_mc_core::ChcPdrStats { relation_count: 4, clause_count: 4 }
        );
        assert!(!is_proof_grade_native_full_verification_verdict(&solved.verdict));
        assert!(trust_mc_core::accepted_native_typed_chc_pdr_proof(&solved.verdict).is_err());
        assert!(solved.authorized_native_proof().is_err());
        let expected_cache_key = solved.cache_key.key.clone();

        let trust_mc_core::FullVerificationVerdict::Proved {
            evidence: trust_mc_core::FullProofEvidence::ChcPdr(proof),
        } = solved.verdict
        else {
            panic!("native trust_ir PDR solve should produce CHC/PDR proof evidence");
        };
        assert_eq!(proof.kind, trust_mc_core::ChcPdrProofKind::ChcValidity);
        assert_eq!(proof.metadata.cache_key.as_ref(), Some(&expected_cache_key));
        assert_eq!(proof.obligation.obligation_id, "trust_ir-native-trust_mc-request-7-proof-0");
        assert_eq!(proof.obligation.kind, trust_mc_core::MirObligationKind::Assertion);
        let metadata = proof
            .obligation
            .native_metadata
            .as_ref()
            .expect("native trust_ir proof should retain typed bundle metadata");
        assert_eq!(
            metadata.schema_version,
            trust_mc_core::NativeTypedChcObligationMetadata::SCHEMA_VERSION
        );
        assert_eq!(metadata.producer, "tRust");
        assert_eq!(metadata.adapter_input, "rust-mir");
        assert_eq!(metadata.native_request_id, 7);
        assert_eq!(metadata.verification_mode, "chc");
        assert_eq!(metadata.proof_obligation_ids, vec![0]);
        assert_eq!(metadata.lineage_root_ids, vec![0]);
        assert_eq!(
            metadata.compiler_facts_digest.as_ref().map(|digest| digest.algorithm.as_str()),
            Some("sha256")
        );
        assert_eq!(metadata.compiler_fact_counts.monomorphizations, 1);
        assert_eq!(metadata.compiler_fact_sources.len(), 1);
        assert_eq!(
            metadata.compiler_fact_sources[0].fact_refs,
            vec![trust_mc_core::NativeCompilerFactReference::new(
                trust_mc_core::NativeCompilerFactKind::Monomorphization,
                0
            )]
        );
        assert_eq!(
            metadata.source_digest.as_ref().map(|digest| digest.algorithm.as_str()),
            Some("sha256")
        );
        assert_eq!(metadata.trust_ir_module_digest.algorithm, "sha256");
        assert_eq!(metadata.lineage_manifest_digest.algorithm, "sha256");
        let replay_identity = metadata
            .replay_identity
            .as_ref()
            .expect("native trust_ir metadata should retain replay identity");
        assert_eq!(replay_identity.engine, "trust-mc");
        assert_eq!(replay_identity.transcript_digest.algorithm, "sha256");
        assert_eq!(metadata.replay_context.atoms.len(), 2);
        assert!(
            metadata.replay_context.atoms.iter().any(|atom| {
                atom.kind == trust_mc_core::NativeReplayAtomKindMetadata::Assertion
                    && atom.proof_obligation_id == Some(0)
                    && atom.assertion_id == Some(0)
                    && atom.span
                        == Some(trust_mc_core::NativeSourceSpanMetadata {
                            file: 0,
                            line: 18,
                            col: 13,
                        })
            }),
            "native trust_ir proof metadata should retain typed assertion replay bindings"
        );
        assert!(
            proof.artifacts.iter().all(|artifact| artifact.digest.is_some()),
            "proof-grade trust_ir evidence artifacts should be digest-backed"
        );
        assert!(
            proof.artifacts.iter().all(|artifact| artifact.byte_len.is_some()),
            "proof-grade trust_ir evidence artifacts should be hashed from concrete bytes"
        );
        assert!(proof.artifacts.iter().any(|artifact| artifact.kind
            == trust_mc_core::FullVerificationArtifactKind::TypedChcProblem));
        assert!(!proof.artifacts.iter().any(|artifact| artifact.kind
            == trust_mc_core::FullVerificationArtifactKind::PdrInvariantModel));
    }

    #[test]
    #[cfg(all(feature = "ay-chc-native", feature = "native-trust-ir-bundle"))]
    fn native_trust_ir_bundle_runner_returns_bound_obligation_and_evidence() {
        let bundle = compiler_style_safe_trust_ir_bundle();
        let runner = NativeTrustIrChcPdrRunner::with_solve_options(
            trust_mc_core::ChcPdrSolveOptions::default()
                .with_engine(trust_mc_core::ChcPdrEngine::Pdr)
                .with_timeout(Duration::from_secs(10)),
        );

        let evidence = runner
            .solve_bundle_native_proof_grade(&bundle)
            .expect("native trust_ir bundle runner should return opaque exact-module authority");

        assert_eq!(evidence.obligations.len(), 1);
        let proof = &evidence.obligations[0];
        assert_eq!(proof.translated.request_id, trust_ir::NativeRequestId::new(7));
        assert_eq!(proof.translated.obligations, vec![trust_ir::ProofId::new(0)]);
        assert_eq!(proof.translated.lineage_roots, vec![trust_ir::ProofLineageId::new(0)]);
        assert_eq!(proof.verification.route, TypedChcPdrRoute::PdrProof);
        assert_eq!(
            proof.verification.outcome.status,
            trust_mc_core::ChcPdrSolveStatus::Unknown {
                reason: trust_mc_core::CHC_VALIDITY_FRESH_CONSUMER_REPLAY_REQUIRED.to_string(),
            }
        );
        proof
            .verification
            .authorized_native_proof()
            .expect("live bundle response must retain opaque exact-module authority");
        assert!(
            trust_mc_core::accepted_native_typed_chc_pdr_proof(&proof.verification.verdict)
                .is_err()
        );
        assert_eq!(proof.transport.request_id, proof.translated.request_id.index());
        assert_eq!(proof.transport.proof_id, Some(0));
        assert_eq!(proof.transport.native_id, proof.translated.obligation.obligation_id);
        assert_eq!(proof.transport.native_id, "trust_ir-native-trust_mc-request-7-proof-0");
        assert_eq!(proof.transport.proof_status, NativeTypedProofStatus::Proved);
        assert_eq!(proof.transport.proof_strength, NativeTypedProofStrength::ChcValidity);
        assert!(proof.transport.solver_artifacts.iter().all(|artifact| artifact.digest.is_some()));
        assert!(
            proof.transport.solver_artifacts.iter().all(|artifact| artifact.byte_len.is_some())
        );
        assert!(proof.transport.replay_artifacts.iter().all(|artifact| artifact.digest.is_some()));
        assert!(
            proof.transport.replay_artifacts.iter().all(|artifact| artifact.byte_len.is_some())
        );
        assert!(proof.transport.check_artifacts.iter().all(|artifact| artifact.digest.is_some()));
        assert!(proof.transport.check_artifacts.iter().all(|artifact| artifact.byte_len.is_some()));
        let [solver_artifact] = proof.transport.solver_artifacts.as_slice() else {
            panic!("proof transport must expose exactly one solver transcript");
        };
        let [replay_artifact] = proof.transport.replay_artifacts.as_slice() else {
            panic!("proof transport must expose exactly one replay log");
        };
        let [check_artifact] = proof.transport.check_artifacts.as_slice() else {
            panic!("proof transport must expose exactly one checked report");
        };
        assert!(!solver_artifact.materialized_bytes().expect("solver bytes").is_empty());
        assert!(!replay_artifact.materialized_bytes().expect("replay bytes").is_empty());
        assert!(!check_artifact.materialized_bytes().expect("checked bytes").is_empty());
        let binding = solver_artifact.proof_binding_id().expect("proof-set binding");
        assert_eq!(replay_artifact.proof_binding_id(), Some(binding));
        assert_eq!(check_artifact.proof_binding_id(), Some(binding));
        let [normalized_input_reference] = solver_artifact.referenced_artifacts() else {
            panic!("solver transcript must reference exactly one normalized input");
        };
        assert_eq!(
            normalized_input_reference.kind,
            trust_mc_core::FullVerificationArtifactKind::NormalizedInput
        );
        let mut normalized_inputs = proof.transport.response_artifacts.iter().filter(|artifact| {
            artifact.kind == trust_mc_core::FullVerificationArtifactKind::NormalizedInput
        });
        let normalized_input = normalized_inputs
            .next()
            .expect("response artifacts must carry the referenced normalized input");
        assert!(
            normalized_inputs.next().is_none(),
            "response artifacts must carry exactly one normalized input"
        );
        assert_eq!(normalized_input.digest.as_ref(), Some(&normalized_input_reference.digest));
        assert!(!normalized_input.materialized_bytes().expect("normalized input bytes").is_empty());
        assert_eq!(normalized_input.proof_binding_id(), Some(binding));
        assert!(normalized_input.referenced_artifacts().is_empty());
        assert_eq!(
            replay_artifact.referenced_artifacts(),
            &[trust_mc_core::FullVerificationArtifactReference::new(
                trust_mc_core::FullVerificationArtifactKind::SolverTranscript,
                solver_artifact.digest.clone().expect("solver digest"),
            )]
        );
        assert_eq!(check_artifact.referenced_artifacts().len(), 2);
        assert!(check_artifact.referenced_artifacts().contains(
            &trust_mc_core::FullVerificationArtifactReference::new(
                trust_mc_core::FullVerificationArtifactKind::SolverTranscript,
                solver_artifact.digest.clone().expect("solver digest"),
            )
        ));
        assert!(check_artifact.referenced_artifacts().contains(
            &trust_mc_core::FullVerificationArtifactReference::new(
                trust_mc_core::FullVerificationArtifactKind::ReplayLog,
                replay_artifact.digest.clone().expect("replay digest"),
            )
        ));
        let replay_payload: serde_json::Value =
            serde_json::from_slice(replay_artifact.materialized_bytes().expect("replay bytes"))
                .expect("replay materialization is JSON");
        let check_payload: serde_json::Value =
            serde_json::from_slice(check_artifact.materialized_bytes().expect("checked bytes"))
                .expect("checked materialization is JSON");
        assert_eq!(
            replay_payload["referenced_solver_transcript"]["value"],
            solver_artifact.digest.as_ref().expect("solver digest").value
        );
        assert_eq!(
            check_payload["referenced_solver_transcript"]["value"],
            solver_artifact.digest.as_ref().expect("solver digest").value
        );
        assert_eq!(
            check_payload["referenced_replay_log"]["value"],
            replay_artifact.digest.as_ref().expect("replay digest").value
        );
        let mut tampered = replay_artifact.clone();
        tampered.digest = Some(trust_mc_core::EvidenceHash::sha256_bytes(b"wrong replay"));
        assert!(tampered.materialized_bytes().is_none());
        assert!(tampered.proof_binding_id().is_none());
        assert!(tampered.referenced_artifacts().is_empty());
        assert!(
            proof.transport.response_artifacts.iter().any(|artifact| {
                artifact.kind == trust_mc_core::FullVerificationArtifactKind::TypedChcProblem
                    && artifact.digest.is_some()
                    && artifact.byte_len.is_some()
            }),
            "transport should expose digest-backed response artifact descriptors"
        );
        assert_eq!(
            proof.transport.replay_check_status,
            Some(trust_mc_core::ProofReplayCheckStatus {
                replay: trust_mc_core::ProofReplayStatus::Unknown,
                check: trust_mc_core::ProofCheckStatus::Unknown,
            })
        );
        assert!(
            proof.verification.cache_key.parts.trust_ir_snapshot.is_some(),
            "native bundle metadata should contribute a stable trust_ir snapshot cache component"
        );
        proof
            .verification
            .authorized_native_proof()
            .expect("bundle runner should return opaque exact-module CHC-validity authority");
    }

    // Trust (T3, per-obligation transport delivery): a compiler-style bundle
    // with a PROVABLE request (id 7, the guarded-branch assert of the safe
    // fixture) and a REFUTABLE request (id 8, an unguarded `assert(x >= 0)` on
    // an unconstrained i32 param, so `error` is derivable). Both functions,
    // obligations, lineage nodes, and compiler facts are always present in the
    // module; `include_safe_request` controls whether the provable REQUEST is
    // pushed, so the same fixture yields the mixed bundle and the all-fail
    // bundle.
    #[cfg(all(feature = "ay-chc-native", feature = "native-trust-ir-bundle"))]
    fn mixed_outcome_trust_ir_bundle(
        include_safe_request: bool,
    ) -> trust_ir::NativeVerificationBundle {
        use trust_ir::inst::ICmpOp;
        use trust_ir::ty::Ty;
        use trust_ir::{
            NativeAdapterInput, NativeAssertionId, NativeBundleProducer, NativeCompilerFactRef,
            NativeCompilerFacts, NativeMonomorphizationFact, NativeMonomorphizationId,
            NativeObligationCause, NativeObligationSource, NativeReplayAtom, NativeReplayAtomId,
            NativeReplayContext, NativeRequestId, NativeRequestProvenance, NativeToolIdentity,
            NativeVerificationBundle, NativeVerificationRequest, ObligationKind, ProofDigest,
            ProofFormula, ProofId, ProofLineageId, ProofLineageManifest, ProofLineageNode,
            ProofObligation, ProofReplayIdentity, ProofStatus, ProofTransform, ProofTransformStage,
            TrustMcNativeRequest, TrustMcVerificationMode,
        };
        use trust_ir_build::ModuleBuilder;

        let source_digest = ProofDigest::sha256([0x71; 32]);
        let trust_ir_module_digest = ProofDigest::sha256([0x72; 32]);

        let mut mb = ModuleBuilder::new("native_trust_ir_chc_mixed_bundle");
        let ft = mb.add_func_type(vec![Ty::I32], vec![]);
        {
            let mut fb = mb.function("trust_ir_native_checked_branch", ft);
            let entry = fb.create_block();
            let then_block = fb.create_block();
            let exit_block = fb.create_block();

            fb.switch_to_block(entry);
            fb.set_entry(entry);
            let x = fb.add_block_param(entry, Ty::I32);
            let zero = fb.iconst(Ty::I32, 0);
            let is_non_negative = fb.icmp(ICmpOp::Sge, Ty::I32, x, zero);
            fb.condbr(is_non_negative, then_block, vec![is_non_negative], exit_block, vec![]);

            let branch_fact = fb.add_block_param(then_block, Ty::Bool);
            fb.switch_to_block(then_block);
            fb.assert(branch_fact);
            fb.ret(vec![]);

            fb.switch_to_block(exit_block);
            fb.ret(vec![]);
            fb.build();
        }
        {
            let mut fb = mb.function("trust_ir_native_unchecked_assert", ft);
            let entry = fb.create_block();
            fb.switch_to_block(entry);
            fb.set_entry(entry);
            let x = fb.add_block_param(entry, Ty::I32);
            let zero = fb.iconst(Ty::I32, 0);
            let is_non_negative = fb.icmp(ICmpOp::Sge, Ty::I32, x, zero);
            fb.assert(is_non_negative);
            fb.ret(vec![]);
            fb.build();
        }

        let mut module = mb.build();
        let safe_function = module
            .functions
            .iter()
            .find(|func| func.name == "trust_ir_native_checked_branch")
            .expect("fixture includes the safe trust-mc function")
            .id;
        let failing_function = module
            .functions
            .iter()
            .find(|func| func.name == "trust_ir_native_unchecked_assert")
            .expect("fixture includes the refutable trust-mc function")
            .id;
        module.proof_obligations.push(
            ProofObligation::new(
                ProofId::new(0),
                ObligationKind::PanicFreedom,
                ProofStatus::Pending,
                "native trust_ir branch assertion is unreachable",
            )
            .with_formula(ProofFormula::smtlib2("trust_ir_native_checked_branch_safe", "Bool"))
            .with_function(safe_function)
            .with_source(native_test_obligation_source(
                "rust:native_trust_ir_chc_mixed_bundle::trust_ir_native_checked_branch",
                "vc:trust-mc-driver:mixed-safe:0",
                b"trust_ir_native_checked_branch_safe",
            )),
        );
        module.proof_obligations.push(
            ProofObligation::new(
                ProofId::new(1),
                ObligationKind::PanicFreedom,
                ProofStatus::Pending,
                "native trust_ir unguarded assertion never fails",
            )
            .with_formula(ProofFormula::smtlib2("trust_ir_native_unchecked_assert_safe", "Bool"))
            .with_function(failing_function)
            .with_source(native_test_obligation_source(
                "rust:native_trust_ir_chc_mixed_bundle::trust_ir_native_unchecked_assert",
                "vc:trust-mc-driver:mixed-failing:1",
                b"trust_ir_native_unchecked_assert_safe",
            )),
        );

        let mut safe_lineage_node = ProofLineageNode::new(
            ProofLineageId::new(0),
            ProofTransform::new(
                ProofTransformStage::Frontend,
                "rustc-mir-to-trust_ir",
                "tRust",
                "native-request-schema-v1",
            ),
            source_digest,
            trust_ir_module_digest,
        );
        safe_lineage_node.obligations.push(ProofId::new(0));
        let mut failing_lineage_node = ProofLineageNode::new(
            ProofLineageId::new(1),
            ProofTransform::new(
                ProofTransformStage::Frontend,
                "rustc-mir-to-trust_ir",
                "tRust",
                "native-request-schema-v1",
            ),
            source_digest,
            trust_ir_module_digest,
        );
        failing_lineage_node.obligations.push(ProofId::new(1));

        let lineage = ProofLineageManifest {
            schema_version: ProofLineageManifest::SCHEMA_VERSION,
            nodes: vec![safe_lineage_node, failing_lineage_node],
            roots: vec![ProofLineageId::new(0), ProofLineageId::new(1)],
        };

        let mut bundle = NativeVerificationBundle::new(
            NativeBundleProducer::TRust,
            NativeAdapterInput::RustMir { body_digest: source_digest },
            trust_ir_module_digest,
            module,
            lineage,
        );
        let safe_span = trust_ir::SourceSpan { file: 0, line: 18, col: 13 };
        let failing_span = trust_ir::SourceSpan { file: 0, line: 42, col: 9 };
        bundle.compiler_facts = NativeCompilerFacts {
            monomorphizations: vec![
                NativeMonomorphizationFact {
                    id: NativeMonomorphizationId::new(0),
                    source_item: "native_trust_ir_chc_mixed_bundle::trust_ir_native_checked_branch"
                        .to_owned(),
                    symbol: "_RNvNtC5mixed26trust_ir_native_checked_branch".to_owned(),
                    generic_args: Vec::new(),
                    function: Some(safe_function),
                    stable_digest: ProofDigest::sha256([0x73; 32]),
                },
                NativeMonomorphizationFact {
                    id: NativeMonomorphizationId::new(1),
                    source_item:
                        "native_trust_ir_chc_mixed_bundle::trust_ir_native_unchecked_assert"
                            .to_owned(),
                    symbol: "_RNvNtC5mixed28trust_ir_native_unchecked_assert".to_owned(),
                    generic_args: Vec::new(),
                    function: Some(failing_function),
                    stable_digest: ProofDigest::sha256([0x74; 32]),
                },
            ],
            obligation_sources: vec![
                NativeObligationSource {
                    obligation: ProofId::new(0),
                    public_obligation_id: "vc:trust-mc-driver:mixed-safe:0".to_string(),
                    function: Some(safe_function),
                    span: Some(safe_span),
                    assertion_id: Some(NativeAssertionId::new(0)),
                    cause: NativeObligationCause::Assert,
                    monomorphization: Some(NativeMonomorphizationId::new(0)),
                    facts: vec![NativeCompilerFactRef::Monomorphization(
                        NativeMonomorphizationId::new(0),
                    )],
                },
                NativeObligationSource {
                    obligation: ProofId::new(1),
                    public_obligation_id: "vc:trust-mc-driver:mixed-failing:1".to_string(),
                    function: Some(failing_function),
                    span: Some(failing_span),
                    assertion_id: Some(NativeAssertionId::new(0)),
                    cause: NativeObligationCause::Assert,
                    monomorphization: Some(NativeMonomorphizationId::new(1)),
                    facts: vec![NativeCompilerFactRef::Monomorphization(
                        NativeMonomorphizationId::new(1),
                    )],
                },
            ],
            ..NativeCompilerFacts::default()
        };
        if include_safe_request {
            bundle.requests.push(NativeVerificationRequest::TrustMc(TrustMcNativeRequest {
                id: NativeRequestId::new(7),
                mode: TrustMcVerificationMode::Chc,
                function: safe_function,
                obligations: vec![ProofId::new(0)],
                lineage_roots: vec![ProofLineageId::new(0)],
                options: {
                    let mut options = trust_ir::TrustMcRequestOptions::default();
                    options.chc.emit_horn_clauses = true;
                    options
                },
                diagnostics: Default::default(),
                provenance: NativeRequestProvenance::trust_mc(
                    NativeToolIdentity::new("trust-mc").with_version("chc-v1"),
                )
                .with_solver(NativeToolIdentity::new("ay-chc").with_version("native-v1"))
                .with_replay(
                    ProofReplayIdentity::new(
                        "trust-mc",
                        "trust_mc native typed CHC/PDR test replay",
                    )
                    .with_transcript_digest(ProofDigest::sha256([0x75; 32])),
                )
                .with_replay_context(
                    NativeReplayContext::default()
                        .with_atom(
                            NativeReplayAtom::assumption(
                                NativeReplayAtomId::new(0),
                                ProofFormula::smtlib2(
                                    "trust_ir_native_checked_branch_guard",
                                    "Bool",
                                ),
                            )
                            .with_obligation(ProofId::new(0))
                            .with_span(safe_span),
                        )
                        .with_atom(
                            NativeReplayAtom::assertion(
                                NativeReplayAtomId::new(1),
                                ProofFormula::smtlib2(
                                    "trust_ir_native_checked_branch_safe",
                                    "Bool",
                                ),
                            )
                            .with_obligation(ProofId::new(0))
                            .with_assertion_id(NativeAssertionId::new(0))
                            .with_span(safe_span),
                        ),
                ),
            }));
        }
        bundle.requests.push(NativeVerificationRequest::TrustMc(TrustMcNativeRequest {
            id: NativeRequestId::new(8),
            mode: TrustMcVerificationMode::Chc,
            function: failing_function,
            obligations: vec![ProofId::new(1)],
            lineage_roots: vec![ProofLineageId::new(1)],
            options: {
                let mut options = trust_ir::TrustMcRequestOptions::default();
                options.chc.emit_horn_clauses = true;
                options
            },
            diagnostics: Default::default(),
            provenance: NativeRequestProvenance::trust_mc(
                NativeToolIdentity::new("trust-mc").with_version("chc-v1"),
            )
            .with_solver(NativeToolIdentity::new("ay-chc").with_version("native-v1"))
            .with_replay(
                ProofReplayIdentity::new("trust-mc", "trust_mc native typed CHC/PDR test replay")
                    .with_transcript_digest(ProofDigest::sha256([0x76; 32])),
            )
            .with_replay_context(
                NativeReplayContext::default().with_atom(
                    NativeReplayAtom::assertion(
                        NativeReplayAtomId::new(0),
                        ProofFormula::smtlib2("trust_ir_native_unchecked_assert_safe", "Bool"),
                    )
                    .with_obligation(ProofId::new(1))
                    .with_assertion_id(NativeAssertionId::new(0))
                    .with_span(failing_span),
                ),
            ),
        }));
        refresh_native_test_bundle_module_identity(&mut bundle);
        bundle
    }

    // Trust (T3): a mixed bundle must return Ok with BOTH sides populated —
    // the proved request keeps its full proof-grade evidence chain unchanged
    // (the soundness invariant), and the not-proved request is delivered as an
    // honest per-row reason instead of discarding the whole bundle.
    #[test]
    #[cfg(all(feature = "ay-chc-native", feature = "native-trust-ir-bundle"))]
    fn bundle_not_proved_rows_carry_reasons_and_keep_proved_siblings() {
        let bundle = mixed_outcome_trust_ir_bundle(true);
        let runner = NativeTrustIrChcPdrRunner::with_solve_options(
            trust_mc_core::ChcPdrSolveOptions::default()
                .with_engine(trust_mc_core::ChcPdrEngine::Pdr)
                .with_timeout(Duration::from_secs(10)),
        );

        let evidence = runner
            .solve_bundle_native_proof_grade(&bundle)
            .expect("mixed bundle must return Ok evidence, not fail on the refuted request");

        assert_eq!(evidence.obligations.len(), 1, "exactly the safe request proves");
        let proof = &evidence.obligations[0];
        assert_eq!(proof.transport.native_id, "trust_ir-native-trust_mc-request-7-proof-0");
        assert_eq!(proof.transport.proof_status, NativeTypedProofStatus::Proved);
        // The proved sibling keeps its live opaque authority and digest-backed
        // artifacts; its detached public candidate remains reject-only.
        proof
            .verification
            .authorized_native_proof()
            .expect("proved sibling must keep opaque exact-module authority");
        assert!(
            trust_mc_core::accepted_native_typed_chc_pdr_proof(&proof.verification.verdict)
                .is_err()
        );
        assert!(proof.transport.replay_artifacts.iter().all(|a| a.digest.is_some()));
        assert!(proof.transport.check_artifacts.iter().all(|a| a.digest.is_some()));

        assert_eq!(evidence.not_proved.len(), 1, "exactly the refuted request is not proved");
        let row = &evidence.not_proved[0];
        assert_eq!(
            row.translated.obligation.obligation_id,
            "trust_ir-native-trust_mc-request-8-proof-1"
        );
        assert!(
            row.reason.contains("counterexample evidence is not a proof"),
            "not-proved reason must carry the row's own fail-closed cause, got: {}",
            row.reason
        );
    }

    // Trust (T3): a bundle where NO request proves still returns Ok evidence
    // with an empty proved set and a fully populated not_proved map, so the
    // consumer can stamp every row with its own honest reason.
    #[test]
    #[cfg(all(feature = "ay-chc-native", feature = "native-trust-ir-bundle"))]
    fn bundle_with_no_proved_requests_returns_ok_with_full_not_proved_map() {
        let bundle = mixed_outcome_trust_ir_bundle(false);
        let runner = NativeTrustIrChcPdrRunner::with_solve_options(
            trust_mc_core::ChcPdrSolveOptions::default()
                .with_engine(trust_mc_core::ChcPdrEngine::Pdr)
                .with_timeout(Duration::from_secs(10)),
        );

        let evidence = runner
            .solve_bundle_native_proof_grade(&bundle)
            .expect("an all-not-proved bundle must still return Ok evidence");

        assert!(evidence.obligations.is_empty(), "no request proves in the all-fail bundle");
        assert_eq!(evidence.not_proved.len(), 1);
        assert_eq!(
            evidence.not_proved[0].translated.obligation.obligation_id,
            "trust_ir-native-trust_mc-request-8-proof-1"
        );
    }

    // Trust (T3, fail-closed pin): STRUCTURAL errors must still fail the whole
    // bundle. A request referencing a proof obligation that does not exist in
    // the module is corruption (bundle validation failure -> InvalidInput),
    // not solver inconclusiveness, and must never degrade into a not_proved
    // row.
    #[test]
    #[cfg(all(feature = "ay-chc-native", feature = "native-trust-ir-bundle"))]
    fn bundle_structural_translation_error_stays_fatal() {
        use trust_ir::{NativeVerificationRequest, ProofId};

        let mut bundle = mixed_outcome_trust_ir_bundle(true);
        for request in &mut bundle.requests {
            #[allow(irrefutable_let_patterns)]
            if let NativeVerificationRequest::TrustMc(request) = request {
                if request.id.index() == 8 {
                    request.obligations = vec![ProofId::new(9)];
                }
            }
        }
        let runner = NativeTrustIrChcPdrRunner::with_solve_options(
            trust_mc_core::ChcPdrSolveOptions::default()
                .with_engine(trust_mc_core::ChcPdrEngine::Pdr)
                .with_timeout(Duration::from_secs(10)),
        );

        let error = runner
            .solve_bundle_native_proof_grade(&bundle)
            .expect_err("a structurally corrupt bundle must fail closed with Err");
        assert!(
            matches!(error, NativeSolveError::InvalidInput { .. }),
            "structural corruption must surface as InvalidInput, got: {error:?}"
        );
    }

    // Trust (T3): pin the per-request collect-vs-fatal classification. Honest
    // "the solver did not prove this request" classes are collectible;
    // InvalidInput (malformed request / binding mismatch = corruption) stays
    // fatal.
    #[test]
    #[cfg(feature = "native-trust-ir-bundle")]
    fn per_request_not_proved_classification_keeps_structural_errors_fatal() {
        assert!(native_solve_error_is_per_request_not_proved(
            &NativeSolveError::ProofGradeRejected {
                rejection: trust_mc_core::ProofEvidenceRejection {
                    problem_kind: Some(trust_mc_core::FullVerificationProblemKind::ChcPdr),
                    reasons: vec!["counterexample evidence is not a proof".to_string()],
                },
            }
        ));
        assert!(native_solve_error_is_per_request_not_proved(&NativeSolveError::SolverFailed {
            reason: String::from("ay-chc engine failed on this request"),
        }));
        assert!(native_solve_error_is_per_request_not_proved(&NativeSolveError::Unsupported(
            NativeSolveUnsupported {
                operation: NativeOperation::Solve,
                reason: String::from("native_trust_ir_trivial_safe_chc_not_proof_grade"),
                detail: String::from("no Horn rule derives the query target"),
            }
        )));
        assert!(!native_solve_error_is_per_request_not_proved(&NativeSolveError::InvalidInput {
            field: String::from("native_trust_ir_bundle.evidence.native_id"),
            detail: String::from("transport native id mismatch"),
        }));
    }

    // Trust diagnostic: isolate whether the typed-CHC translation + ay prove a
    // u32 (unsigned/bitvector) guarded assert -- the `guarded` repro pattern --
    // without a 5-minute compiler rebuild. Mirrors the I32 fixture above but
    // uses Ty::U32 + ICmpOp::Ult and a `x < 100` guard threaded into the
    // asserted block. Dumps the horn SMT2 ay receives.
    #[cfg(all(feature = "ay-chc-native", feature = "native-trust-ir-bundle"))]
    fn u32_guarded_assert_trust_ir_bundle() -> trust_ir::NativeVerificationBundle {
        use trust_ir::inst::ICmpOp;
        use trust_ir::ty::Ty;
        use trust_ir::{
            NativeAdapterInput, NativeAssertionId, NativeBundleProducer, NativeCompilerFactRef,
            NativeCompilerFacts, NativeMonomorphizationFact, NativeMonomorphizationId,
            NativeObligationCause, NativeObligationSource, NativeRequestId,
            NativeRequestProvenance, NativeToolIdentity, NativeVerificationBundle,
            NativeVerificationRequest, ObligationKind, ProofDigest, ProofFormula, ProofId,
            ProofLineageId, ProofLineageManifest, ProofLineageNode, ProofObligation,
            ProofReplayIdentity, ProofStatus, ProofTransform, ProofTransformStage,
            TrustMcNativeRequest, TrustMcVerificationMode,
        };
        use trust_ir_build::ModuleBuilder;

        let source_digest = ProofDigest::sha256([0x71; 32]);
        let trust_ir_module_digest = ProofDigest::sha256([0x72; 32]);

        let mut mb = ModuleBuilder::new("u32_guarded_assert_bundle");
        let ft = mb.add_func_type(vec![Ty::U32], vec![]);
        {
            let mut fb = mb.function("u32_guarded", ft);
            let entry = fb.create_block();
            let then_block = fb.create_block();
            let exit_block = fb.create_block();

            fb.switch_to_block(entry);
            fb.set_entry(entry);
            let x = fb.add_block_param(entry, Ty::U32);
            let hundred = fb.iconst(Ty::U32, 100);
            let lt = fb.icmp(ICmpOp::Ult, Ty::U32, x, hundred);
            fb.condbr(lt, then_block, vec![lt], exit_block, vec![]);

            let branch_fact = fb.add_block_param(then_block, Ty::Bool);
            fb.switch_to_block(then_block);
            fb.assert(branch_fact);
            fb.ret(vec![]);

            fb.switch_to_block(exit_block);
            fb.ret(vec![]);
            fb.build();
        }

        let mut module = mb.build();
        let func_id = module
            .functions
            .iter()
            .find(|func| func.name == "u32_guarded")
            .expect("fixture includes requested function")
            .id;
        module.proof_obligations.push(
            ProofObligation::new(
                ProofId::new(0),
                ObligationKind::PanicFreedom,
                ProofStatus::Pending,
                "u32 guarded assert is unreachable on failure edge",
            )
            .with_formula(ProofFormula::smtlib2("u32_guarded_safe", "Bool"))
            .with_function(func_id)
            .with_source(native_test_obligation_source(
                "rust:u32_guarded_assert_bundle::u32_guarded",
                "vc:trust-mc-driver:u32-guarded:0",
                b"u32_guarded_safe",
            )),
        );

        let mut lineage_node = ProofLineageNode::new(
            ProofLineageId::new(0),
            ProofTransform::new(
                ProofTransformStage::Frontend,
                "rustc-mir-to-trust_ir",
                "tRust",
                "native-request-schema-v1",
            ),
            source_digest,
            trust_ir_module_digest,
        );
        lineage_node.obligations.push(ProofId::new(0));

        let lineage = ProofLineageManifest {
            schema_version: ProofLineageManifest::SCHEMA_VERSION,
            nodes: vec![lineage_node],
            roots: vec![ProofLineageId::new(0)],
        };

        let mut bundle = NativeVerificationBundle::new(
            NativeBundleProducer::TRust,
            NativeAdapterInput::RustMir { body_digest: source_digest },
            trust_ir_module_digest,
            module,
            lineage,
        );
        let source_span = trust_ir::SourceSpan { file: 0, line: 10, col: 9 };
        bundle.compiler_facts = NativeCompilerFacts {
            monomorphizations: vec![NativeMonomorphizationFact {
                id: NativeMonomorphizationId::new(0),
                source_item: "u32_guarded_assert_bundle::u32_guarded".to_owned(),
                symbol: "_RNvNtC4test9u32_guarded".to_owned(),
                generic_args: Vec::new(),
                function: Some(func_id),
                stable_digest: ProofDigest::sha256([0x73; 32]),
            }],
            obligation_sources: vec![NativeObligationSource {
                obligation: ProofId::new(0),
                public_obligation_id: "vc:trust-mc-driver:u32-guarded:0".to_string(),
                function: Some(func_id),
                span: Some(source_span),
                assertion_id: Some(NativeAssertionId::new(0)),
                cause: NativeObligationCause::Assert,
                monomorphization: Some(NativeMonomorphizationId::new(0)),
                facts: vec![NativeCompilerFactRef::Monomorphization(
                    NativeMonomorphizationId::new(0),
                )],
            }],
            ..NativeCompilerFacts::default()
        };
        bundle.requests.push(NativeVerificationRequest::TrustMc(TrustMcNativeRequest {
            id: NativeRequestId::new(0),
            mode: TrustMcVerificationMode::Chc,
            function: func_id,
            obligations: vec![ProofId::new(0)],
            lineage_roots: vec![ProofLineageId::new(0)],
            options: {
                let mut options = trust_ir::TrustMcRequestOptions::default();
                options.chc.emit_horn_clauses = true;
                options
            },
            diagnostics: Default::default(),
            provenance: NativeRequestProvenance::trust_mc(
                NativeToolIdentity::new("trust-mc").with_version("chc-v1"),
            )
            .with_solver(NativeToolIdentity::new("ay-chc").with_version("native-v1"))
            .with_replay(
                ProofReplayIdentity::new("trust-mc", "u32 guarded replay")
                    .with_transcript_digest(ProofDigest::sha256([0x74; 32])),
            ),
        }));
        refresh_native_test_bundle_module_identity(&mut bundle);
        bundle
    }

    #[test]
    #[cfg(all(feature = "ay-chc-native", feature = "native-trust-ir-bundle"))]
    fn diag_u32_guarded_assert_proves_through_pdr() {
        let bundle = u32_guarded_assert_trust_ir_bundle();
        let obligations = trust_mc_trust_bmc::trust_mc_chc_pdr_obligations_from_native_bundle(
            &bundle,
            &trust_mc_trust_bmc::TranslateOptions::default(),
        )
        .expect("u32 guarded bundle should translate");
        assert_eq!(obligations.len(), 1, "exactly one trust-mc obligation expected");
        let translated = obligations.into_iter().next().unwrap();
        eprintln!(
            "DIAG u32 guarded obligation_id={} function={}",
            translated.obligation.obligation_id, translated.obligation.function_name
        );
        eprintln!("DIAG u32 guarded HORN SMT2:\n{}", translated.obligation.vc.to_horn_smt2());
        eprintln!(
            "DIAG u32 guarded is_trivially_safe={}",
            translated.obligation.is_trivially_safe()
        );

        let runner = NativeTrustIrChcPdrRunner::with_solve_options(
            trust_mc_core::ChcPdrSolveOptions::default()
                .with_engine(trust_mc_core::ChcPdrEngine::Pdr)
                .with_timeout(Duration::from_secs(10)),
        );
        let evidence = runner
            .solve_bundle_native_proof_grade(&bundle)
            .expect("u32 guarded bundle should solve");
        assert_eq!(evidence.obligations.len(), 1);
        let solved = &evidence.obligations[0].verification;
        eprintln!("DIAG u32 guarded SOLVE STATUS = {:?}", solved.outcome.status);
        assert_eq!(
            solved.outcome.status,
            trust_mc_core::ChcPdrSolveStatus::Unknown {
                reason: trust_mc_core::CHC_VALIDITY_FRESH_CONSUMER_REPLAY_REQUIRED.to_string(),
            },
            "public status must remain a detached candidate"
        );
        solved
            .authorized_native_proof()
            .expect("fresh bundle path must retain opaque CHC-validity authority");
    }

    // Trust diagnostic: faithful reproduction of the compiler's `guarded`
    // lowering. Unlike `u32_guarded_assert_trust_ir_bundle` (which threads the
    // boolean guard and asserts it directly), this mirrors what
    // trust-ir-bridge/lower.rs actually emits for
    //   fn guarded(a:u32)->u32 { if a<100 { assert!(a<100); a } else {0} }
    // namely: outer `a<100` + condbr threading `a` (U32) into the then-block,
    // a *recomputed* `a<100` in the then-block, and a panic block that asserts
    // `false` under the (infeasible) path `a<100 && a>=100`. The panic is
    // genuinely unreachable, so a correct verifier must PROVE it.
    #[cfg(all(feature = "ay-chc-native", feature = "native-trust-ir-bundle"))]
    fn u32_compiler_shaped_guarded_bundle() -> trust_ir::NativeVerificationBundle {
        use trust_ir::inst::ICmpOp;
        use trust_ir::ty::Ty;
        use trust_ir::{
            NativeAdapterInput, NativeAssertionId, NativeBundleProducer, NativeCompilerFactRef,
            NativeCompilerFacts, NativeMonomorphizationFact, NativeMonomorphizationId,
            NativeObligationCause, NativeObligationSource, NativeRequestId,
            NativeRequestProvenance, NativeToolIdentity, NativeVerificationBundle,
            NativeVerificationRequest, ObligationKind, ProofDigest, ProofFormula, ProofId,
            ProofLineageId, ProofLineageManifest, ProofLineageNode, ProofObligation,
            ProofReplayIdentity, ProofStatus, ProofTransform, ProofTransformStage,
            TrustMcNativeRequest, TrustMcVerificationMode,
        };
        use trust_ir_build::ModuleBuilder;

        let source_digest = ProofDigest::sha256([0x71; 32]);
        let trust_ir_module_digest = ProofDigest::sha256([0x72; 32]);

        let mut mb = ModuleBuilder::new("u32_compiler_shaped_guarded_bundle");
        let ft = mb.add_func_type(vec![Ty::U32], vec![]);
        {
            let mut fb = mb.function("u32_guarded", ft);
            let entry = fb.create_block();
            let then_block = fb.create_block();
            let panic_block = fb.create_block();
            let cont_block = fb.create_block();
            let else_block = fb.create_block();

            // entry: x = param; lt1 = (x <u 100); if lt1 -> then(x) else -> else
            fb.switch_to_block(entry);
            fb.set_entry(entry);
            let x = fb.add_block_param(entry, Ty::U32);
            let hundred = fb.iconst(Ty::U32, 100);
            let lt1 = fb.icmp(ICmpOp::Ult, Ty::U32, x, hundred);
            fb.condbr(lt1, then_block, vec![x], else_block, vec![]);

            // then: x2 = param; lt2 = (x2 <u 100); if lt2 -> cont else -> panic
            let x2 = fb.add_block_param(then_block, Ty::U32);
            fb.switch_to_block(then_block);
            let hundred2 = fb.iconst(Ty::U32, 100);
            let lt2 = fb.icmp(ICmpOp::Ult, Ty::U32, x2, hundred2);
            fb.condbr(lt2, cont_block, vec![], panic_block, vec![]);

            // panic: assert(false) on the infeasible (x<100 && x>=100) edge.
            fb.switch_to_block(panic_block);
            let f = fb.bool_const(false);
            fb.assert(f);
            fb.unreachable();

            fb.switch_to_block(cont_block);
            fb.ret(vec![]);

            fb.switch_to_block(else_block);
            fb.ret(vec![]);
            fb.build();
        }

        let mut module = mb.build();
        let func_id = module
            .functions
            .iter()
            .find(|func| func.name == "u32_guarded")
            .expect("fixture includes requested function")
            .id;
        module.proof_obligations.push(
            ProofObligation::new(
                ProofId::new(0),
                ObligationKind::PanicFreedom,
                ProofStatus::Pending,
                "u32 guarded panic edge is unreachable",
            )
            .with_formula(ProofFormula::smtlib2("u32_guarded_safe", "Bool"))
            .with_function(func_id)
            .with_source(native_test_obligation_source(
                "rust:u32_compiler_shaped_guarded_bundle::u32_guarded",
                "vc:trust-mc-driver:u32-compiler-shaped:0",
                b"u32_guarded_safe",
            )),
        );

        let mut lineage_node = ProofLineageNode::new(
            ProofLineageId::new(0),
            ProofTransform::new(
                ProofTransformStage::Frontend,
                "rustc-mir-to-trust_ir",
                "tRust",
                "native-request-schema-v1",
            ),
            source_digest,
            trust_ir_module_digest,
        );
        lineage_node.obligations.push(ProofId::new(0));

        let lineage = ProofLineageManifest {
            schema_version: ProofLineageManifest::SCHEMA_VERSION,
            nodes: vec![lineage_node],
            roots: vec![ProofLineageId::new(0)],
        };

        let mut bundle = NativeVerificationBundle::new(
            NativeBundleProducer::TRust,
            NativeAdapterInput::RustMir { body_digest: source_digest },
            trust_ir_module_digest,
            module,
            lineage,
        );
        let source_span = trust_ir::SourceSpan { file: 0, line: 10, col: 9 };
        bundle.compiler_facts = NativeCompilerFacts {
            monomorphizations: vec![NativeMonomorphizationFact {
                id: NativeMonomorphizationId::new(0),
                source_item: "u32_compiler_shaped_guarded_bundle::u32_guarded".to_owned(),
                symbol: "_RNvNtC4test9u32_guarded".to_owned(),
                generic_args: Vec::new(),
                function: Some(func_id),
                stable_digest: ProofDigest::sha256([0x73; 32]),
            }],
            obligation_sources: vec![NativeObligationSource {
                obligation: ProofId::new(0),
                public_obligation_id: "vc:trust-mc-driver:u32-compiler-shaped:0".to_string(),
                function: Some(func_id),
                span: Some(source_span),
                assertion_id: Some(NativeAssertionId::new(0)),
                cause: NativeObligationCause::Assert,
                monomorphization: Some(NativeMonomorphizationId::new(0)),
                facts: vec![NativeCompilerFactRef::Monomorphization(
                    NativeMonomorphizationId::new(0),
                )],
            }],
            ..NativeCompilerFacts::default()
        };
        bundle.requests.push(NativeVerificationRequest::TrustMc(TrustMcNativeRequest {
            id: NativeRequestId::new(0),
            mode: TrustMcVerificationMode::Chc,
            function: func_id,
            obligations: vec![ProofId::new(0)],
            lineage_roots: vec![ProofLineageId::new(0)],
            options: {
                let mut options = trust_ir::TrustMcRequestOptions::default();
                options.chc.emit_horn_clauses = true;
                options
            },
            diagnostics: Default::default(),
            provenance: NativeRequestProvenance::trust_mc(
                NativeToolIdentity::new("trust-mc").with_version("chc-v1"),
            )
            .with_solver(NativeToolIdentity::new("ay-chc").with_version("native-v1"))
            .with_replay(
                ProofReplayIdentity::new("trust-mc", "u32 guarded replay")
                    .with_transcript_digest(ProofDigest::sha256([0x74; 32])),
            ),
        }));
        refresh_native_test_bundle_module_identity(&mut bundle);
        bundle
    }

    #[test]
    #[cfg(all(feature = "ay-chc-native", feature = "native-trust-ir-bundle"))]
    fn u32_compiler_shaped_guarded_bundle_proves_native_proof_grade() {
        let bundle = u32_compiler_shaped_guarded_bundle();
        let obligations = trust_mc_trust_bmc::trust_mc_chc_pdr_obligations_from_native_bundle(
            &bundle,
            &trust_mc_trust_bmc::TranslateOptions::default(),
        )
        .expect("compiler-shaped guarded bundle should translate");
        assert_eq!(obligations.len(), 1, "exactly one trust-mc obligation expected");
        let translated = obligations.into_iter().next().unwrap();
        eprintln!("DIAG compiler-shaped HORN SMT2:\n{}", translated.obligation.vc.to_horn_smt2());
        eprintln!(
            "DIAG compiler-shaped trivially_safe={}",
            translated.obligation.is_trivially_safe()
        );
        for engine in [
            trust_mc_core::ChcPdrEngine::Pdr,
            trust_mc_core::ChcPdrEngine::AdaptivePortfolio,
            trust_mc_core::ChcPdrEngine::Auto,
        ] {
            let runner = NativeTrustIrChcPdrRunner::with_solve_options(
                trust_mc_core::ChcPdrSolveOptions::default()
                    .with_engine(engine)
                    .with_timeout(Duration::from_secs(10)),
            );
            let evidence = runner.solve_bundle_native_proof_grade(&bundle).unwrap_or_else(|err| {
                panic!("compiler-shaped guarded obligation must solve, engine={engine:?}: {err:?}")
            });
            assert_eq!(evidence.obligations.len(), 1);
            let solved = &evidence.obligations[0].verification;
            eprintln!("compiler-shaped engine={engine:?} STATUS = {:?}", solved.outcome.status);
            assert_eq!(
                solved.outcome.status,
                trust_mc_core::ChcPdrSolveStatus::Unknown {
                    reason: trust_mc_core::CHC_VALIDITY_FRESH_CONSUMER_REPLAY_REQUIRED.to_string(),
                }
            );
            solved.authorized_native_proof().unwrap_or_else(|err| {
                panic!("compiler-shaped bundle must retain opaque authority, engine={engine:?}: {err:?}")
            });
        }
    }

    // LINCHPIN end-to-end: a genuinely panic-free function (single block, just
    // returns) whose whole-function panic-freedom obligation is discharged
    // through the REAL native-bundle transport path. `translate_chc` emits NO
    // error rule (the function has no panic site), so `is_trivially_safe` is
    // true; `native_chc_metadata` stamps the structural-completeness
    // certificate; and the live response carries opaque exact-module authority
    // over its otherwise reject-only public ChcValidity candidate.
    #[cfg(all(feature = "ay-chc-native", feature = "native-trust-ir-bundle"))]
    fn panic_free_compiler_bundle() -> trust_ir::NativeVerificationBundle {
        use trust_ir::ty::Ty;
        use trust_ir::{
            NativeAdapterInput, NativeAssertionId, NativeBundleProducer, NativeCompilerFactRef,
            NativeCompilerFacts, NativeMonomorphizationFact, NativeMonomorphizationId,
            NativeObligationCause, NativeObligationSource, NativeRequestId,
            NativeRequestProvenance, NativeToolIdentity, NativeVerificationBundle,
            NativeVerificationRequest, ObligationKind, ProofDigest, ProofFormula, ProofId,
            ProofLineageId, ProofLineageManifest, ProofLineageNode, ProofObligation,
            ProofReplayIdentity, ProofStatus, ProofTransform, ProofTransformStage,
            TrustMcNativeRequest, TrustMcVerificationMode,
        };
        use trust_ir_build::ModuleBuilder;

        let source_digest = ProofDigest::sha256([0x81; 32]);

        let mut mb = ModuleBuilder::new("panic_free_compiler_bundle");
        let ft = mb.add_func_type(vec![Ty::U32], vec![]);
        {
            let mut fb = mb.function("noop", ft);
            let entry = fb.create_block();
            fb.switch_to_block(entry);
            fb.set_entry(entry);
            let _x = fb.add_block_param(entry, Ty::U32);
            fb.ret(vec![]);
            fb.build();
        }

        let mut module = mb.build();
        let func_id = module
            .functions
            .iter()
            .find(|func| func.name == "noop")
            .expect("fixture includes requested function")
            .id;
        module.proof_obligations.push(
            ProofObligation::new(
                ProofId::new(0),
                ObligationKind::PanicFreedom,
                ProofStatus::Pending,
                "noop is panic-free",
            )
            .with_formula(ProofFormula::smtlib2("noop_safe", "Bool"))
            .with_function(func_id)
            .with_source(native_test_obligation_source(
                "rust:panic_free_compiler_bundle::noop",
                "vc:trust-mc-driver:panic-free:0",
                b"noop_safe",
            )),
        );

        let trust_ir_module_digest = module.stable_digest();

        let mut lineage_node = ProofLineageNode::new(
            ProofLineageId::new(0),
            ProofTransform::new(
                ProofTransformStage::Frontend,
                "rustc-mir-to-trust_ir",
                "tRust",
                "native-request-schema-v1",
            ),
            source_digest,
            trust_ir_module_digest,
        );
        lineage_node.obligations.push(ProofId::new(0));
        let lineage = ProofLineageManifest {
            schema_version: ProofLineageManifest::SCHEMA_VERSION,
            nodes: vec![lineage_node],
            roots: vec![ProofLineageId::new(0)],
        };

        let mut bundle = NativeVerificationBundle::new(
            NativeBundleProducer::TRust,
            NativeAdapterInput::RustMir { body_digest: source_digest },
            trust_ir_module_digest,
            module,
            lineage,
        );
        let source_span = trust_ir::SourceSpan { file: 0, line: 1, col: 1 };
        bundle.compiler_facts = NativeCompilerFacts {
            monomorphizations: vec![NativeMonomorphizationFact {
                id: NativeMonomorphizationId::new(0),
                source_item: "panic_free_compiler_bundle::noop".to_owned(),
                symbol: "_RNvNtC4test4noop".to_owned(),
                generic_args: Vec::new(),
                function: Some(func_id),
                stable_digest: ProofDigest::sha256([0x83; 32]),
            }],
            obligation_sources: vec![NativeObligationSource {
                obligation: ProofId::new(0),
                public_obligation_id: "vc:trust-mc-driver:panic-free:0".to_string(),
                function: Some(func_id),
                span: Some(source_span),
                assertion_id: Some(NativeAssertionId::new(0)),
                cause: NativeObligationCause::Assert,
                monomorphization: Some(NativeMonomorphizationId::new(0)),
                facts: vec![NativeCompilerFactRef::Monomorphization(
                    NativeMonomorphizationId::new(0),
                )],
            }],
            ..NativeCompilerFacts::default()
        };
        bundle.requests.push(NativeVerificationRequest::TrustMc(TrustMcNativeRequest {
            id: NativeRequestId::new(0),
            mode: TrustMcVerificationMode::Chc,
            function: func_id,
            obligations: vec![ProofId::new(0)],
            lineage_roots: vec![ProofLineageId::new(0)],
            options: {
                let mut options = trust_ir::TrustMcRequestOptions::default();
                options.chc.emit_horn_clauses = true;
                options
            },
            diagnostics: Default::default(),
            provenance: NativeRequestProvenance::trust_mc(
                NativeToolIdentity::new("trust-mc").with_version("chc-v1"),
            )
            .with_solver(NativeToolIdentity::new("ay-chc").with_version("native-v1"))
            .with_replay(
                ProofReplayIdentity::new("trust-mc", "noop replay")
                    .with_transcript_digest(ProofDigest::sha256([0x84; 32])),
            ),
        }));
        refresh_native_test_bundle_module_identity(&mut bundle);
        bundle
    }

    #[test]
    #[cfg(all(feature = "ay-chc-native", feature = "native-trust-ir-bundle"))]
    fn panic_free_whole_function_is_credited_through_native_bundle_transport() {
        let bundle = panic_free_compiler_bundle();
        let obligations = trust_mc_trust_bmc::trust_mc_chc_pdr_obligations_from_native_bundle(
            &bundle,
            &trust_mc_trust_bmc::TranslateOptions::default(),
        )
        .expect("panic-free bundle should translate");
        assert_eq!(obligations.len(), 1, "exactly one trust-mc obligation expected");
        let translated = obligations.into_iter().next().unwrap();

        // The complete-by-construction translator emits NO error rule for a
        // genuinely panic-free function, and stamps the completeness certificate.
        assert!(
            translated.obligation.is_trivially_safe(),
            "a genuinely panic-free function must translate to a trivially-safe CHC"
        );
        assert!(
            translated
                .obligation
                .native_metadata
                .as_ref()
                .expect("the real pipeline attaches native metadata")
                .structural_reachability_complete,
            "native_chc_metadata must certify structural completeness"
        );

        // Only the fresh bundle path may mint opaque exact-module authority.
        let runner = NativeTrustIrChcPdrRunner::with_solve_options(
            trust_mc_core::ChcPdrSolveOptions::default()
                .with_engine(trust_mc_core::ChcPdrEngine::Pdr)
                .with_timeout(Duration::from_secs(10)),
        );
        let evidence = runner
            .solve_bundle_native_proof_grade(&bundle)
            .expect("panic-free whole-function bundle must produce exact-module authority");
        assert_eq!(evidence.obligations.len(), 1);
        let solved = &evidence.obligations[0].verification;
        assert_eq!(solved.route, TypedChcPdrRoute::TriviallySafe);
        assert_eq!(
            solved.outcome.status,
            trust_mc_core::ChcPdrSolveStatus::Unknown {
                reason: trust_mc_core::CHC_VALIDITY_FRESH_CONSUMER_REPLAY_REQUIRED.to_string(),
            }
        );
        solved
            .authorized_native_proof()
            .expect("trivial structural derivation must retain opaque authority");
    }

    #[cfg(all(feature = "ay-chc-native", feature = "native-trust-ir-bundle"))]
    #[derive(Debug, Clone, Copy)]
    enum ProofAuthorityAttackShape {
        Assume,
        Undef,
        FreshHavocUndef,
        FreshHavocWithAssume,
        FreshHavocNonUndef,
        FreshHavocValueAssertion,
        ValidBorrowLoad,
        ValidBorrowStore,
        Borrow,
        BorrowMut,
        Wrapping,
        ExtractElement,
        Gep,
        PointerData,
        PointerMetadata,
        PointerFromParts,
        ScalarAlloca,
        UninitializedScalarAlloca,
        CrossBlockScalarAlloca,
        TypeMismatchedScalarAlloca,
        ExplicitlyAlignedScalarAlloca,
        ExplicitlyAlignedScalarAccess,
        AggregateAlloca,
        EscapingAggregateAlloca,
        TypeMismatchedAggregateAlloca,
        Alloca,
        IntToPtr,
        DialectOperation,
        NameOnlyWrappingCall,
    }

    #[cfg(all(feature = "ay-chc-native", feature = "native-trust-ir-bundle"))]
    fn proof_authority_attack_bundle(
        shape: ProofAuthorityAttackShape,
    ) -> trust_ir::NativeVerificationBundle {
        use trust_ir::inst::{BinOp, CastOp};
        use trust_ir::ty::Ty;
        use trust_ir::{FuncId, ProofAnnotation};
        use trust_ir_build::ModuleBuilder;

        let mut bundle = panic_free_compiler_bundle();
        let mut builder = ModuleBuilder::new(format!("proof_authority_attack_{shape:?}"));

        match shape {
            ProofAuthorityAttackShape::Assume => {
                let ty = builder.add_func_type(vec![], vec![]);
                let mut function = builder.function("attack", ty);
                let entry = function.create_block();
                function.switch_to_block(entry);
                function.set_entry(entry);
                let false_value = function.bool_const(false);
                function.assume(false_value);
                function.ret(vec![]);
                function.build();
            }
            ProofAuthorityAttackShape::Undef => {
                let ty = builder.add_func_type(vec![], vec![]);
                let mut function = builder.function("attack", ty);
                let entry = function.create_block();
                function.switch_to_block(entry);
                function.set_entry(entry);
                let _undefined = function.undef(Ty::U32);
                function.ret(vec![]);
                function.build();
            }
            ProofAuthorityAttackShape::FreshHavocUndef => {
                let ty = builder.add_func_type(vec![], vec![]);
                let mut function = builder.function("attack", ty);
                let entry = function.create_block();
                function.switch_to_block(entry);
                function.set_entry(entry);
                let _havoc =
                    function.undef_proven(Ty::U32, vec![ProofAnnotation::FreshSymbolicHavoc]);
                function.ret(vec![]);
                function.build();
            }
            ProofAuthorityAttackShape::FreshHavocWithAssume => {
                let ty = builder.add_func_type(vec![], vec![]);
                let mut function = builder.function("attack", ty);
                let entry = function.create_block();
                function.switch_to_block(entry);
                function.set_entry(entry);
                let havoc =
                    function.undef_proven(Ty::U32, vec![ProofAnnotation::FreshSymbolicHavoc]);
                let upper = function.iconst(Ty::U32, 10);
                let narrowed = function.icmp(trust_ir::inst::ICmpOp::Ule, Ty::U32, havoc, upper);
                function.assume(narrowed);
                function.ret(vec![]);
                function.build();
            }
            ProofAuthorityAttackShape::FreshHavocNonUndef => {
                let ty = builder.add_func_type(vec![], vec![]);
                let mut function = builder.function("attack", ty);
                let entry = function.create_block();
                function.switch_to_block(entry);
                function.set_entry(entry);
                let lhs = function.iconst(Ty::U32, 1);
                let rhs = function.iconst(Ty::U32, 2);
                let _sum = function.binop_proven(
                    BinOp::Add,
                    Ty::U32,
                    lhs,
                    rhs,
                    vec![ProofAnnotation::FreshSymbolicHavoc],
                );
                function.ret(vec![]);
                function.build();
            }
            ProofAuthorityAttackShape::FreshHavocValueAssertion => {
                let ty = builder.add_func_type(vec![], vec![]);
                let mut function = builder.function("attack", ty);
                let entry = function.create_block();
                function.switch_to_block(entry);
                function.set_entry(entry);
                let havoc =
                    function.undef_proven(Ty::U32, vec![ProofAnnotation::FreshSymbolicHavoc]);
                let seven = function.iconst(Ty::U32, 7);
                let value_claim = function.icmp(trust_ir::inst::ICmpOp::Eq, Ty::U32, havoc, seven);
                function.assert(value_claim);
                function.ret(vec![]);
                function.build();
            }
            ProofAuthorityAttackShape::ValidBorrowLoad => {
                let ty = builder.add_func_type(vec![Ty::Ptr], vec![]);
                let mut function = builder.function("attack", ty);
                let entry = function.create_block();
                function.switch_to_block(entry);
                function.set_entry(entry);
                let ptr = function.add_block_param(entry, Ty::Ptr);
                let _loaded =
                    function.load_proven(Ty::I32, ptr, vec![ProofAnnotation::ValidBorrow]);
                function.ret(vec![]);
                function.build();
            }
            ProofAuthorityAttackShape::ValidBorrowStore => {
                let ty = builder.add_func_type(vec![Ty::Ptr, Ty::I32], vec![]);
                let mut function = builder.function("attack", ty);
                let entry = function.create_block();
                function.switch_to_block(entry);
                function.set_entry(entry);
                let ptr = function.add_block_param(entry, Ty::Ptr);
                let value = function.add_block_param(entry, Ty::I32);
                function.store_proven(Ty::I32, ptr, value, vec![ProofAnnotation::ValidBorrow]);
                function.ret(vec![]);
                function.build();
            }
            ProofAuthorityAttackShape::Borrow | ProofAuthorityAttackShape::BorrowMut => {
                let ty = builder.add_func_type(vec![], vec![]);
                let mut function = builder.function("attack", ty);
                let entry = function.create_block();
                function.switch_to_block(entry);
                function.set_entry(entry);
                let ptr = function.null_ptr();
                let _borrow = if matches!(shape, ProofAuthorityAttackShape::Borrow) {
                    function.borrow(ptr)
                } else {
                    function.borrow_mut(ptr)
                };
                function.ret(vec![]);
                function.build();
            }
            ProofAuthorityAttackShape::Wrapping => {
                let ty = builder.add_func_type(vec![Ty::I32, Ty::I32], vec![]);
                let mut function = builder.function("attack", ty);
                let entry = function.create_block();
                function.switch_to_block(entry);
                function.set_entry(entry);
                let lhs = function.add_block_param(entry, Ty::I32);
                let rhs = function.add_block_param(entry, Ty::I32);
                let _sum = function.binop_proven(
                    BinOp::Add,
                    Ty::I32,
                    lhs,
                    rhs,
                    vec![ProofAnnotation::Wrapping],
                );
                function.ret(vec![]);
                function.build();
            }
            ProofAuthorityAttackShape::ExtractElement => {
                let element_ty = builder.add_type(Ty::U32);
                let array_ty = Ty::Array(element_ty, 4);
                let ty = builder.add_func_type(vec![array_ty.clone(), Ty::U32], vec![]);
                let mut function = builder.function("attack", ty);
                let entry = function.create_block();
                function.switch_to_block(entry);
                function.set_entry(entry);
                let array = function.add_block_param(entry, array_ty);
                let index = function.add_block_param(entry, Ty::U32);
                let _element = function.extract_element(Ty::U32, array, index);
                function.ret(vec![]);
                function.build();
            }
            ProofAuthorityAttackShape::Gep => {
                let ty = builder.add_func_type(vec![Ty::Ptr, Ty::I64], vec![]);
                let mut function = builder.function("attack", ty);
                let entry = function.create_block();
                function.switch_to_block(entry);
                function.set_entry(entry);
                let ptr = function.add_block_param(entry, Ty::Ptr);
                let index = function.add_block_param(entry, Ty::I64);
                let _derived = function.gep(Ty::I32, ptr, vec![index]);
                function.ret(vec![]);
                function.build();
            }
            ProofAuthorityAttackShape::PointerMetadata => {
                let pointer_ty = Ty::FatPtr(trust_ir::FatPtrKind::Str);
                let ty = builder.add_func_type(vec![pointer_ty.clone()], vec![]);
                let mut function = builder.function("attack", ty);
                let entry = function.create_block();
                function.switch_to_block(entry);
                function.set_entry(entry);
                let pointer = function.add_block_param(entry, pointer_ty.clone());
                let _metadata = function.ptr_metadata(pointer_ty, Ty::U64, pointer);
                function.ret(vec![]);
                function.build();
            }
            ProofAuthorityAttackShape::PointerData => {
                let pointer_ty = Ty::FatPtr(trust_ir::FatPtrKind::Str);
                let ty = builder.add_func_type(vec![pointer_ty.clone()], vec![]);
                let mut function = builder.function("attack", ty);
                let entry = function.create_block();
                function.switch_to_block(entry);
                function.set_entry(entry);
                let pointer = function.add_block_param(entry, pointer_ty.clone());
                let _data = function.ptr_data(pointer_ty, pointer);
                function.ret(vec![]);
                function.build();
            }
            ProofAuthorityAttackShape::PointerFromParts => {
                let pointer_ty = Ty::FatPtr(trust_ir::FatPtrKind::Str);
                let ty = builder.add_func_type(vec![Ty::Ptr, Ty::U64], vec![]);
                let mut function = builder.function("attack", ty);
                let entry = function.create_block();
                function.switch_to_block(entry);
                function.set_entry(entry);
                let data = function.add_block_param(entry, Ty::Ptr);
                let metadata = function.add_block_param(entry, Ty::U64);
                let _pointer = function.ptr_from_parts(pointer_ty, Ty::U64, data, metadata);
                function.ret(vec![]);
                function.build();
            }
            ProofAuthorityAttackShape::Alloca => {
                let ty = builder.add_func_type(vec![], vec![Ty::Ptr]);
                let mut function = builder.function("attack", ty);
                let entry = function.create_block();
                function.switch_to_block(entry);
                function.set_entry(entry);
                let ptr = function.alloca(Ty::I32);
                function.ret(vec![ptr]);
                function.build();
            }
            ProofAuthorityAttackShape::ScalarAlloca => {
                let ty = builder.add_func_type(vec![Ty::I32], vec![]);
                let mut function = builder.function("attack", ty);
                let entry = function.create_block();
                function.switch_to_block(entry);
                function.set_entry(entry);
                let value = function.add_block_param(entry, Ty::I32);
                let ptr = function.alloca(Ty::I32);
                function.store(Ty::I32, ptr, value);
                let _loaded = function.load(Ty::I32, ptr);
                function.ret(vec![]);
                function.build();
            }
            ProofAuthorityAttackShape::UninitializedScalarAlloca => {
                let ty = builder.add_func_type(vec![], vec![]);
                let mut function = builder.function("attack", ty);
                let entry = function.create_block();
                function.switch_to_block(entry);
                function.set_entry(entry);
                let ptr = function.alloca(Ty::I32);
                let _loaded = function.load(Ty::I32, ptr);
                function.ret(vec![]);
                function.build();
            }
            ProofAuthorityAttackShape::CrossBlockScalarAlloca => {
                let ty = builder.add_func_type(vec![], vec![]);
                let mut function = builder.function("attack", ty);
                let entry = function.create_block();
                let next = function.create_block();
                function.switch_to_block(entry);
                function.set_entry(entry);
                let ptr = function.alloca(Ty::I32);
                let value = function.iconst(Ty::I32, 1);
                function.store(Ty::I32, ptr, value);
                function.br(next, vec![]);
                function.switch_to_block(next);
                let _loaded = function.load(Ty::I32, ptr);
                function.ret(vec![]);
                function.build();
            }
            ProofAuthorityAttackShape::TypeMismatchedScalarAlloca => {
                let ty = builder.add_func_type(vec![Ty::U32], vec![]);
                let mut function = builder.function("attack", ty);
                let entry = function.create_block();
                function.switch_to_block(entry);
                function.set_entry(entry);
                let value = function.add_block_param(entry, Ty::U32);
                let ptr = function.alloca(Ty::I32);
                function.store(Ty::U32, ptr, value);
                function.ret(vec![]);
                function.build();
            }
            ProofAuthorityAttackShape::ExplicitlyAlignedScalarAlloca => {
                let ty = builder.add_func_type(vec![], vec![]);
                let mut function = builder.function("attack", ty);
                let entry = function.create_block();
                function.switch_to_block(entry);
                function.set_entry(entry);
                let _ptr = function.alloca_aligned(Ty::I32, 8);
                function.ret(vec![]);
                function.build();
            }
            ProofAuthorityAttackShape::ExplicitlyAlignedScalarAccess => {
                let ty = builder.add_func_type(vec![], vec![]);
                let mut function = builder.function("attack", ty);
                let entry = function.create_block();
                function.switch_to_block(entry);
                function.set_entry(entry);
                let ptr = function.alloca(Ty::I32);
                let _loaded = function.load_aligned(Ty::I32, ptr, 8);
                function.ret(vec![]);
                function.build();
            }
            ProofAuthorityAttackShape::AggregateAlloca => {
                let aggregate_ty = Ty::Tuple(vec![Ty::U32, Ty::U32]);
                let ty = builder.add_func_type(vec![aggregate_ty.clone()], vec![]);
                let mut function = builder.function("attack", ty);
                let entry = function.create_block();
                function.switch_to_block(entry);
                function.set_entry(entry);
                let value = function.add_block_param(entry, aggregate_ty.clone());
                let ptr = function.alloca(aggregate_ty.clone());
                function.store(aggregate_ty.clone(), ptr, value);
                let _loaded = function.load(aggregate_ty, ptr);
                function.ret(vec![]);
                function.build();
            }
            ProofAuthorityAttackShape::EscapingAggregateAlloca => {
                let aggregate_ty = Ty::Tuple(vec![Ty::U32, Ty::U32]);
                let ty = builder.add_func_type(vec![], vec![Ty::Ptr]);
                let mut function = builder.function("attack", ty);
                let entry = function.create_block();
                function.switch_to_block(entry);
                function.set_entry(entry);
                let ptr = function.alloca(aggregate_ty);
                function.ret(vec![ptr]);
                function.build();
            }
            ProofAuthorityAttackShape::TypeMismatchedAggregateAlloca => {
                let aggregate_ty = Ty::Tuple(vec![Ty::U32, Ty::U32]);
                let ty = builder.add_func_type(vec![Ty::U32], vec![]);
                let mut function = builder.function("attack", ty);
                let entry = function.create_block();
                function.switch_to_block(entry);
                function.set_entry(entry);
                let value = function.add_block_param(entry, Ty::U32);
                let ptr = function.alloca(aggregate_ty);
                function.store(Ty::U32, ptr, value);
                function.ret(vec![]);
                function.build();
            }
            ProofAuthorityAttackShape::IntToPtr => {
                let ty = builder.add_func_type(vec![], vec![]);
                let mut function = builder.function("attack", ty);
                let entry = function.create_block();
                function.switch_to_block(entry);
                function.set_entry(entry);
                let one = function.iconst(Ty::U64, 1);
                let _ptr = function.cast(CastOp::IntToPtr, Ty::U64, Ty::Ptr, one);
                function.ret(vec![]);
                function.build();
            }
            ProofAuthorityAttackShape::DialectOperation => {
                let ty = builder.add_func_type(vec![], vec![]);
                let mut function = builder.function("attack", ty);
                let entry = function.create_block();
                function.switch_to_block(entry);
                function.set_entry(entry);
                let _results = function
                    .dialect_op(trust_ir::dialect::trust_rust::thread_local_addr("crate::TLS"));
                function.ret(vec![]);
                function.build();
            }
            ProofAuthorityAttackShape::NameOnlyWrappingCall => {
                let caller_ty = builder.add_func_type(vec![], vec![]);
                let callee_ty = builder.add_func_type(vec![Ty::U32, Ty::U32], vec![Ty::U32]);
                {
                    let mut caller = builder.function("attack", caller_ty);
                    let entry = caller.create_block();
                    caller.switch_to_block(entry);
                    caller.set_entry(entry);
                    let lhs = caller.iconst(Ty::U32, 1);
                    let rhs = caller.iconst(Ty::U32, 2);
                    let _result = caller.call(FuncId::new(1), vec![lhs, rhs]);
                    caller.ret(vec![]);
                    caller.build();
                }
                {
                    let mut callee = builder.function("attacker::wrapping_add", callee_ty);
                    let entry = callee.create_block();
                    callee.switch_to_block(entry);
                    callee.set_entry(entry);
                    let lhs = callee.add_block_param(entry, Ty::U32);
                    let _rhs = callee.add_block_param(entry, Ty::U32);
                    let false_value = callee.bool_const(false);
                    callee.assert(false_value);
                    callee.ret(vec![lhs]);
                    callee.build();
                }
            }
        }

        let mut module = builder.build();
        module.proof_obligations = bundle.module.proof_obligations.clone();
        module.proof_certificates = bundle.module.proof_certificates.clone();
        module.obligation_diagnostics = bundle.module.obligation_diagnostics.clone();
        bundle.module = module;
        refresh_native_test_bundle_module_identity(&mut bundle);
        bundle
    }

    #[test]
    #[cfg(all(feature = "ay-chc-native", feature = "native-trust-ir-bundle"))]
    fn proof_grade_bundle_preflight_rejects_public_semantic_shortcuts() {
        for (shape, expected) in [
            (ProofAuthorityAttackShape::Assume, "unauthenticated Assume"),
            (ProofAuthorityAttackShape::Undef, "executes Undef"),
            (ProofAuthorityAttackShape::ValidBorrowLoad, "public ValidBorrow"),
            (ProofAuthorityAttackShape::ValidBorrowStore, "public ValidBorrow"),
            (ProofAuthorityAttackShape::Borrow, "borrow-checker validity"),
            (ProofAuthorityAttackShape::BorrowMut, "borrow-checker validity"),
            (ProofAuthorityAttackShape::Wrapping, "public Wrapping"),
            (ProofAuthorityAttackShape::ExtractElement, "uses ExtractElement"),
            (ProofAuthorityAttackShape::Gep, "uses GEP"),
            (ProofAuthorityAttackShape::PointerData, "pointer-part semantics"),
            (ProofAuthorityAttackShape::PointerMetadata, "pointer-part semantics"),
            (ProofAuthorityAttackShape::PointerFromParts, "pointer-part semantics"),
            (ProofAuthorityAttackShape::Alloca, "uses Alloca"),
            (ProofAuthorityAttackShape::IntToPtr, "uses cast IntToPtr"),
            (ProofAuthorityAttackShape::DialectOperation, "public dialect operation"),
            (
                ProofAuthorityAttackShape::NameOnlyWrappingCall,
                "name-only wrapping-intrinsic substitution",
            ),
        ] {
            let bundle = proof_authority_attack_bundle(shape);
            let error = validate_native_bundle_proof_authority_input(&bundle, None)
                .expect_err("public semantic shortcut must fail before authority minting");
            let NativeSolveError::InvalidInput { field, detail } = error else {
                panic!("{shape:?} must be a structural preflight rejection");
            };
            assert!(field.starts_with("native_trust_ir_bundle."), "{shape:?}: {field}");
            assert!(detail.contains(expected), "{shape:?}: {detail}");
        }
    }

    #[test]
    #[cfg(all(feature = "ay-chc-native", feature = "native-trust-ir-bundle"))]
    fn transparent_borrow_input_gate_obeys_the_explicit_opt_in() {
        let enabled = admit_transparent_borrow_instructions();
        for shape in [ProofAuthorityAttackShape::Borrow, ProofAuthorityAttackShape::BorrowMut] {
            let bundle = proof_authority_attack_bundle(shape);
            let result = validate_native_bundle_proof_authority_input(&bundle, None);
            if enabled {
                result.unwrap_or_else(|error| {
                    panic!("{shape:?} must pass when TRUST_ADMIT_BORROW_INST is set: {error}")
                });
            } else {
                let error =
                    result.expect_err("a transparent borrow must remain fail-closed by default");
                let NativeSolveError::InvalidInput { detail, .. } = error else {
                    panic!("{shape:?} must be rejected structurally");
                };
                assert!(detail.contains("borrow-checker validity"), "{shape:?}: {detail}");
            }
        }
    }

    #[test]
    #[cfg(all(feature = "ay-chc-native", feature = "native-trust-ir-bundle"))]
    fn single_cell_alloca_is_default_on_but_escape_and_type_punning_fail_closed() {
        for shape in [
            ProofAuthorityAttackShape::ScalarAlloca,
            ProofAuthorityAttackShape::AggregateAlloca,
            // CrossBlockScalarAlloca was pinned as a rejection when this gate was
            // written (2026-08-13) on the rationale that a cell whose accesses
            // leave its defining block "can go stale" — true of the per-block
            // `stack_cells` lane, and NOT true of this shape. `translate_chc`'s
            // mem2reg promotion (landed 2026-07-02, six weeks EARLIER, and simply
            // not accounted for by that gate) threads an un-aliased scalar cell
            // through every block relation and updates it on each store, so the
            // join-block Load reads the exact stored value. The gate's job is to
            // mirror the translator's exact lanes; there are two, and this is the
            // second. The stale-cell hazards it guards against are each still
            // pinned as rejections below: an uninitialized read
            // (`UninitializedScalarAlloca`), an unmodeled alignment claim, a
            // type-punned access, and an escaping pointer. `volatile` — which the
            // promotion analysis itself ignores, and which would leave a promoted
            // cell holding its pre-store value in a non-def block — is excluded by
            // `single_cell_alloca_is_admissible` and pinned in
            // trust-mc-trust-bmc's `rejects_volatile_access_on_a_promoted_cell`.
            ProofAuthorityAttackShape::CrossBlockScalarAlloca,
        ] {
            let admitted = proof_authority_attack_bundle(shape);
            validate_native_bundle_proof_authority_input(&admitted, None)
                .unwrap_or_else(|error| panic!("{shape:?} has an exact CHC model: {error}"));
        }

        for shape in [
            ProofAuthorityAttackShape::Alloca,
            // An uninitialized read stays fail-closed under BOTH lanes. The
            // translator seeds an un-stored cell with one stable fresh symbol,
            // which is arbitrary but self-consistent — strictly weaker than the
            // `undef` a real uninitialized read has, so two loads of one uninit
            // cell would be proved equal against a program that is UB.
            ProofAuthorityAttackShape::UninitializedScalarAlloca,
            ProofAuthorityAttackShape::TypeMismatchedScalarAlloca,
            ProofAuthorityAttackShape::ExplicitlyAlignedScalarAlloca,
            ProofAuthorityAttackShape::ExplicitlyAlignedScalarAccess,
            ProofAuthorityAttackShape::EscapingAggregateAlloca,
            ProofAuthorityAttackShape::TypeMismatchedAggregateAlloca,
        ] {
            let bundle = proof_authority_attack_bundle(shape);
            let error = validate_native_bundle_proof_authority_input(&bundle, None)
                .expect_err("a cell that can go stale must fail closed");
            let NativeSolveError::InvalidInput { field, detail } = error else {
                panic!("{shape:?} must be rejected structurally");
            };
            assert!(field.starts_with("native_trust_ir_bundle."), "{shape:?}: {field}");
            assert!(detail.contains("uses Alloca"), "{shape:?}: {detail}");
        }
    }

    /// Swap a freshly built module into the valid compiler-shaped bundle
    /// skeleton (obligations/requests reference the single `FuncId(0)`
    /// function, which the builder must therefore define exactly one of).
    #[cfg(all(feature = "ay-chc-native", feature = "native-trust-ir-bundle"))]
    fn swapped_module_bundle(
        builder: trust_ir_build::ModuleBuilder,
    ) -> trust_ir::NativeVerificationBundle {
        let mut bundle = panic_free_compiler_bundle();
        let mut module = builder.build();
        module.proof_obligations = bundle.module.proof_obligations.clone();
        module.proof_certificates = bundle.module.proof_certificates.clone();
        module.obligation_diagnostics = bundle.module.obligation_diagnostics.clone();
        bundle.module = module;
        refresh_native_test_bundle_module_identity(&mut bundle);
        bundle
    }

    /// A `NonNull`-shaped single-pointer-newtype struct registered as
    /// `StructId(0)`, for the pointer bit-identity cast fixtures.
    #[cfg(all(feature = "ay-chc-native", feature = "native-trust-ir-bundle"))]
    fn register_nonnull_shaped_struct(mb: &mut trust_ir_build::ModuleBuilder) -> trust_ir::ty::Ty {
        use trust_ir::ty::{FieldDef, StructDef, Ty};
        use trust_ir::value::StructId;
        let id = StructId::new(0);
        mb.add_struct(StructDef {
            repr: Default::default(),
            id,
            name: "NonNullShaped".to_owned(),
            fields: vec![FieldDef { name: "pointer".to_owned(), ty: Ty::Ptr, offset: Some(0) }],
            // The module validator demands layout evidence for struct-involved
            // bitcasts — mirror the bridge's registered `NonNull` layout.
            size: Some(8),
            align: Some(8),
        });
        Ty::Struct(id)
    }

    /// One-cast fixture: `attack(x: param_ty) { _ = cast(op, param_ty, dst); }`.
    #[cfg(all(feature = "ay-chc-native", feature = "native-trust-ir-bundle"))]
    fn single_cast_bundle(
        op: trust_ir::inst::CastOp,
        src_of: fn(&trust_ir::ty::Ty) -> trust_ir::ty::Ty,
        dst_of: fn(&trust_ir::ty::Ty) -> trust_ir::ty::Ty,
    ) -> trust_ir::NativeVerificationBundle {
        use trust_ir_build::ModuleBuilder;
        let mut builder = ModuleBuilder::new(format!("bit_identity_cast_{op:?}"));
        let newtype = register_nonnull_shaped_struct(&mut builder);
        let src = src_of(&newtype);
        let dst = dst_of(&newtype);
        let ty = builder.add_func_type(vec![src.clone()], vec![]);
        let mut function = builder.function("attack", ty);
        let entry = function.create_block();
        function.switch_to_block(entry);
        function.set_entry(entry);
        let x = function.add_block_param(entry, src.clone());
        let _cast = function.cast(op, src, dst, x);
        function.ret(vec![]);
        function.build();
        swapped_module_bundle(builder)
    }

    /// The exact pointer bit-identity cast shapes are admitted by the
    /// proof-grade preflight WITHOUT any authority — they are public,
    /// type-derived bit facts, translated value-preservingly (the semantics
    /// live in `trust_mc_trust_bmc::proof_grade_cast_is_admissible`'s lockstep
    /// legs; the value-level proof/refutation pair is the round-trip test
    /// below).
    #[test]
    #[cfg(all(feature = "ay-chc-native", feature = "native-trust-ir-bundle"))]
    fn proof_grade_preflight_admits_exact_pointer_bit_identity_casts() {
        use trust_ir::inst::CastOp;
        use trust_ir::ty::{FatPtrKind, Ty};
        let fat = |_: &Ty| Ty::FatPtr(FatPtrKind::Str);
        let cases: [(CastOp, fn(&Ty) -> Ty, fn(&Ty) -> Ty, &str); 6] = [
            (CastOp::Bitcast, |_| Ty::U64, |nn: &Ty| nn.clone(), "usize->newtype pack"),
            (CastOp::Bitcast, |nn: &Ty| nn.clone(), |_| Ty::U64, "newtype->usize unpack"),
            (CastOp::Bitcast, |_| Ty::Ptr, |nn: &Ty| nn.clone(), "thin->newtype wrap"),
            (CastOp::Bitcast, |nn: &Ty| nn.clone(), |_| Ty::Ptr, "newtype->thin unwrap"),
            (CastOp::Bitcast, fat, fat, "same-type fat reinterpret"),
            (CastOp::PtrToInt, |_| Ty::Ptr, |_| Ty::U64, "thin PtrToInt"),
        ];
        for (op, src_of, dst_of, what) in cases {
            let bundle = single_cast_bundle(op, src_of, dst_of);
            validate_native_bundle_proof_authority_input(&bundle, None)
                .unwrap_or_else(|error| panic!("{what} must be admitted: {error}"));
        }
    }

    /// Everything outside the enumerated bit-identity shapes keeps the
    /// fail-closed cast refusal — including the shapes adjacent to the admitted
    /// ones (narrow int pack, mismatched fat, a bare integer->`Ty::Ptr` forge
    /// spelled as Bitcast, fat-source PtrToInt). `IntToPtr` keeps its own pin
    /// in the attack-shape tables.
    #[test]
    #[cfg(all(feature = "ay-chc-native", feature = "native-trust-ir-bundle"))]
    fn proof_grade_preflight_keeps_out_of_scope_casts_refused() {
        use trust_ir::inst::CastOp;
        use trust_ir::ty::{FatPtrKind, Ty};
        // The fat->thin Bitcast spelling is refused one gate EARLIER (the
        // module validator's cast layout rule) — its honest proof-grade
        // spelling is `Inst::PtrData` under source authority.
        let cases: [(CastOp, fn(&Ty) -> Ty, fn(&Ty) -> Ty, &str, &str); 5] = [
            // Refused by the module validator's cast layout rule (32b -> 64b)
            // before the floor's own cast arm is even consulted.
            (CastOp::Bitcast, |_| Ty::U32, |nn: &Ty| nn.clone(), "narrow-int pack", "cast"),
            (
                CastOp::Bitcast,
                |_| Ty::FatPtr(FatPtrKind::Str),
                |_| Ty::FatPtr(FatPtrKind::TraitObject { trait_id: 0 }),
                "mismatched fat reinterpret",
                "uses cast",
            ),
            (
                CastOp::Bitcast,
                |_| Ty::U64,
                |_| Ty::Ptr,
                "bare int->ptr forge as Bitcast",
                "uses cast",
            ),
            // Also refused by the module validator ("cast ptrtoint from
            // fatptr<str> to u64 is invalid") before the floor's arm.
            (
                CastOp::PtrToInt,
                |_| Ty::FatPtr(FatPtrKind::Str),
                |_| Ty::U64,
                "fat PtrToInt",
                "cast",
            ),
            (
                CastOp::Bitcast,
                |_| Ty::FatPtr(FatPtrKind::Str),
                |_| Ty::Ptr,
                "fat->thin as Bitcast",
                "cast",
            ),
        ];
        for (op, src_of, dst_of, what, expected) in cases {
            let bundle = single_cast_bundle(op, src_of, dst_of);
            let Err(error) = validate_native_bundle_proof_authority_input(&bundle, None) else {
                panic!("{what} must stay refused");
            };
            let NativeSolveError::InvalidInput { field, detail } = error else {
                panic!("{what} must be a structural preflight rejection");
            };
            assert!(field.starts_with("native_trust_ir_bundle."), "{what}: {field}");
            assert!(detail.contains(expected), "{what}: {detail}");
        }
    }

    /// Value-level contract of the `fmt::Arguments` packing legs, through the
    /// production floor + translator + PDR: the usize -> NonNull -> usize round
    /// trip IS the identity (proves `bits == x`) and is ONLY the identity (the
    /// negated claim refutes). A havoc model of either leg proves neither.
    #[test]
    #[cfg(all(feature = "ay-chc-native", feature = "native-trust-ir-bundle"))]
    fn usize_newtype_pack_unpack_round_trip_is_exactly_the_identity() {
        use trust_ir::inst::{CastOp, ICmpOp};
        use trust_ir::ty::Ty;
        use trust_ir_build::ModuleBuilder;

        let build = |claim_identity: bool| {
            let mut builder = ModuleBuilder::new("pack_unpack_round_trip");
            let newtype = register_nonnull_shaped_struct(&mut builder);
            let ty = builder.add_func_type(vec![Ty::U64], vec![]);
            let mut function = builder.function("attack", ty);
            let entry = function.create_block();
            function.switch_to_block(entry);
            function.set_entry(entry);
            let x = function.add_block_param(entry, Ty::U64);
            let packed = function.cast(CastOp::Bitcast, Ty::U64, newtype.clone(), x);
            let bits = function.cast(CastOp::Bitcast, newtype.clone(), Ty::U64, packed);
            let claim = function.icmp(
                if claim_identity { ICmpOp::Eq } else { ICmpOp::Ne },
                Ty::U64,
                bits,
                x,
            );
            function.assert(claim);
            function.ret(vec![]);
            function.build();
            swapped_module_bundle(builder)
        };

        let runner = NativeTrustIrChcPdrRunner::with_solve_options(
            trust_mc_core::ChcPdrSolveOptions::default()
                .with_engine(trust_mc_core::ChcPdrEngine::Pdr)
                .with_timeout(Duration::from_secs(10)),
        );

        let proved = runner
            .solve_bundle_native_proof_grade(&build(true))
            .expect("identity claim must solve");
        assert_eq!(proved.obligations.len(), 1, "bits == x must PROVE");
        proved.obligations[0]
            .verification
            .authorized_native_proof()
            .expect("the identity proof must carry native proof authority");

        let refuted = runner
            .solve_bundle_native_proof_grade(&build(false))
            .expect("negated claim must still solve without a structural error");
        assert!(
            refuted.obligations.is_empty(),
            "bits != x is FALSE for every x and must never prove"
        );
        assert_eq!(
            refuted.not_proved.len() + refuted.refuted.len(),
            1,
            "the negated claim must be reported outside the proof channel"
        );
    }

    #[test]
    #[cfg(all(feature = "ay-chc-native", feature = "native-trust-ir-bundle"))]
    fn fresh_symbolic_havoc_admission_is_exact_and_grants_no_narrowing_authority() {
        let stamped = proof_authority_attack_bundle(ProofAuthorityAttackShape::FreshHavocUndef);
        validate_native_bundle_proof_authority_input(&stamped, None)
            .expect("the exact FreshSymbolicHavoc + Undef pair is unconstrained havoc");

        for (shape, expected) in [
            (ProofAuthorityAttackShape::FreshHavocWithAssume, "unauthenticated Assume"),
            (
                ProofAuthorityAttackShape::FreshHavocNonUndef,
                "FreshSymbolicHavoc on a non-Undef instruction",
            ),
        ] {
            let bundle = proof_authority_attack_bundle(shape);
            let error = validate_native_bundle_proof_authority_input(&bundle, None)
                .expect_err("the public marker must grant no semantic narrowing authority");
            let NativeSolveError::InvalidInput { field, detail } = error else {
                panic!("{shape:?} must be rejected structurally");
            };
            assert!(field.starts_with("native_trust_ir_bundle."), "{shape:?}: {field}");
            assert!(detail.contains(expected), "{shape:?}: {detail}");
        }

        // The marker is intentionally serializable and forgeable. Roundtrip
        // therefore cannot turn it into the live capability required by the
        // independent Assume gate.
        let narrowed =
            proof_authority_attack_bundle(ProofAuthorityAttackShape::FreshHavocWithAssume);
        let encoded = serde_json::to_vec(&narrowed).expect("serialize marked public bundle");
        let decoded: trust_ir::NativeVerificationBundle =
            serde_json::from_slice(&encoded).expect("deserialize marked public bundle");
        let error = validate_native_bundle_proof_authority_input(&decoded, None)
            .expect_err("serialized marker must not authenticate its forged narrowing");
        let NativeSolveError::InvalidInput { detail, .. } = error else {
            panic!("serialized narrowing must be rejected structurally");
        };
        assert!(detail.contains("unauthenticated Assume"), "{detail}");
    }

    #[test]
    #[cfg(all(feature = "ay-chc-native", feature = "native-trust-ir-bundle"))]
    fn fresh_symbolic_havoc_cannot_prove_a_value_specific_assertion() {
        let bundle =
            proof_authority_attack_bundle(ProofAuthorityAttackShape::FreshHavocValueAssertion);
        validate_native_bundle_proof_authority_input(&bundle, None)
            .expect("stamped Undef itself must pass the selective input gate");

        let translated = trust_mc_trust_bmc::trust_mc_chc_pdr_obligations_from_native_bundle(
            &bundle,
            &trust_mc_trust_bmc::TranslateOptions::default(),
        )
        .expect("fresh symbolic havoc bundle translates");
        assert_eq!(translated.len(), 1);
        assert!(
            translated[0].obligation.vc.rules.iter().any(|rule| rule.head.name == "error"),
            "the unconstrained value-specific assertion must retain a reachable error rule"
        );
        assert!(
            !translated[0].obligation.is_trivially_safe(),
            "fresh havoc must not collapse a value-specific assertion to structural safety"
        );

        let runner = NativeTrustIrChcPdrRunner::with_solve_options(
            trust_mc_core::ChcPdrSolveOptions::default()
                .with_engine(trust_mc_core::ChcPdrEngine::Pdr)
                .with_timeout(Duration::from_secs(10)),
        );
        let evidence = runner
            .solve_bundle_native_proof_grade(&bundle)
            .expect("the refutable bundle must return an honest non-proof outcome");
        assert!(
            evidence.obligations.is_empty(),
            "an arbitrary havoc value cannot prove it equals seven"
        );
        assert_eq!(
            evidence.not_proved.len() + evidence.refuted.len(),
            1,
            "the sole request must be reported outside the proof-authority channel"
        );
    }

    #[test]
    #[cfg(all(feature = "ay-chc-native", feature = "native-trust-ir-bundle"))]
    fn exact_source_generation_authority_admits_only_source_generated_semantics() {
        for shape in [
            ProofAuthorityAttackShape::Assume,
            ProofAuthorityAttackShape::PointerMetadata,
            ProofAuthorityAttackShape::Wrapping,
            // `ValidBorrow` on a Load/Store rides the same audited live-lowering
            // authority as the three above: the stamp derives from rustc's
            // reference typing, contributes no value fact (the loaded value is
            // still fresh havoc), and only discharges the bounds-model refusal.
            ProofAuthorityAttackShape::ValidBorrowLoad,
            ProofAuthorityAttackShape::ValidBorrowStore,
            // `PtrData` is the fat->thin data-lane read (the `as_ptr` leg of the
            // `fmt::Arguments` packing) — asserts nothing, modeled exactly.
            ProofAuthorityAttackShape::PointerData,
        ] {
            let mut bundle = proof_authority_attack_bundle(shape);
            let authority =
                trust_ir::SourceGenerationAuthority::mint_from_live_lowering(&mut bundle)
                    .unwrap_or_else(|error| {
                        panic!("{shape:?} fixture must mint authority: {error}")
                    });
            validate_native_bundle_proof_authority_input(&bundle, Some(&authority)).unwrap_or_else(
                |error| panic!("{shape:?} must pass the exact authority gate: {error}"),
            );
        }

        for (shape, expected) in [
            (ProofAuthorityAttackShape::Undef, "executes Undef"),
            (ProofAuthorityAttackShape::Borrow, "borrow-checker validity"),
            (ProofAuthorityAttackShape::BorrowMut, "borrow-checker validity"),
            (ProofAuthorityAttackShape::ExtractElement, "uses ExtractElement"),
            (ProofAuthorityAttackShape::Gep, "uses GEP"),
            (ProofAuthorityAttackShape::PointerFromParts, "pointer-part semantics"),
            (ProofAuthorityAttackShape::Alloca, "uses Alloca"),
            (ProofAuthorityAttackShape::IntToPtr, "uses cast IntToPtr"),
            (ProofAuthorityAttackShape::DialectOperation, "public dialect operation"),
            (
                ProofAuthorityAttackShape::NameOnlyWrappingCall,
                "name-only wrapping-intrinsic substitution",
            ),
        ] {
            let mut bundle = proof_authority_attack_bundle(shape);
            let authority =
                trust_ir::SourceGenerationAuthority::mint_from_live_lowering(&mut bundle)
                    .unwrap_or_else(|error| {
                        panic!("{shape:?} fixture must mint authority: {error}")
                    });
            let error = validate_native_bundle_proof_authority_input(&bundle, Some(&authority))
                .expect_err("source authority must not admit an unrelated semantic shortcut");
            let NativeSolveError::InvalidInput { field, detail } = error else {
                panic!("{shape:?} must be a structural preflight rejection");
            };
            assert!(field.starts_with("native_trust_ir_bundle."), "{shape:?}: {field}");
            assert!(detail.contains(expected), "{shape:?}: {detail}");
        }
    }

    #[test]
    #[cfg(all(feature = "ay-chc-native", feature = "native-trust-ir-bundle"))]
    fn source_generation_authority_is_send_sync_for_shared_parallel_dispatch() {
        fn assert_send_sync<T: Send + Sync>() {}
        assert_send_sync::<trust_ir::SourceGenerationAuthority>();
    }

    #[test]
    #[cfg(all(feature = "ay-chc-native", feature = "native-trust-ir-bundle"))]
    fn source_generation_authority_rejects_clone_roundtrip_cross_bundle_and_mutation() {
        fn expect_assume_rejection(
            bundle: &trust_ir::NativeVerificationBundle,
            authority: &trust_ir::SourceGenerationAuthority,
            case: &str,
        ) {
            let error = match validate_native_bundle_proof_authority_input(bundle, Some(authority))
            {
                Err(error) => error,
                Ok(()) => panic!("{case} must not retain source authority"),
            };
            let NativeSolveError::InvalidInput { field, detail } = error else {
                panic!("{case} must fail at the structural preflight");
            };
            assert_eq!(field, "native_trust_ir_bundle.module.functions.instructions", "{case}");
            assert!(detail.contains("unauthenticated Assume"), "{case}: {detail}");
        }

        let mut bundle = proof_authority_attack_bundle(ProofAuthorityAttackShape::Assume);
        let authority = trust_ir::SourceGenerationAuthority::mint_from_live_lowering(&mut bundle)
            .expect("fresh in-process fixture must mint authority");
        validate_native_bundle_proof_authority_input(&bundle, Some(&authority))
            .expect("the original exact bundle must be authorized");

        let cloned = bundle.clone();
        expect_assume_rejection(&cloned, &authority, "clone");

        let encoded = serde_json::to_vec(&bundle).expect("serialize authority-bearing bundle");
        let decoded: trust_ir::NativeVerificationBundle =
            serde_json::from_slice(&encoded).expect("deserialize bundle");
        expect_assume_rejection(&decoded, &authority, "serde roundtrip");

        let mut independently_built =
            proof_authority_attack_bundle(ProofAuthorityAttackShape::Assume);
        let foreign_authority =
            trust_ir::SourceGenerationAuthority::mint_from_live_lowering(&mut independently_built)
                .expect("independent fixture must mint its own authority");
        expect_assume_rejection(&bundle, &foreign_authority, "cross-bundle authority");
        expect_assume_rejection(&independently_built, &authority, "wrong authority");

        bundle.diagnostics.emit_proof_traces = !bundle.diagnostics.emit_proof_traces;
        expect_assume_rejection(&bundle, &authority, "post-mint mutation");
    }

    #[test]
    #[cfg(all(feature = "ay-chc-native", feature = "native-trust-ir-bundle"))]
    fn public_bundle_entrypoints_default_deny_and_thread_exact_source_authority() {
        let mut bundle = proof_authority_attack_bundle(ProofAuthorityAttackShape::Assume);
        let runner = NativeTrustIrChcPdrRunner::new();

        let default_error = runner
            .solve_bundle_native_proof_grade(&bundle)
            .expect_err("the ordinary public API must keep Assume fail-closed");
        let NativeSolveError::InvalidInput { field, detail } = default_error else {
            panic!("ordinary public API must reject Assume at its structural preflight");
        };
        assert_eq!(field, "native_trust_ir_bundle.module.functions.instructions");
        assert!(detail.contains("unauthenticated Assume"), "{detail}");

        let authority = trust_ir::SourceGenerationAuthority::mint_from_live_lowering(&mut bundle)
            .expect("fresh in-process fixture must mint authority");
        if let Err(error) =
            runner.solve_bundle_native_proof_grade_with_source_authority(&bundle, &authority)
        {
            if let NativeSolveError::InvalidInput { field, detail } = &error
                && detail.contains("unauthenticated Assume")
            {
                panic!(
                    "privileged public API failed to thread its exact authority at {field}: {detail}"
                );
            }
            // A later solver/translation outcome is not source-authority
            // admission. The regression guards only the public plumbing seam;
            // private preflight tests above exhaustively guard the relaxation.
        }
    }

    #[test]
    #[cfg(all(feature = "ay-chc-native", feature = "native-trust-ir-bundle"))]
    fn proof_grade_bundle_preflight_rejects_non_64_bit_target() {
        let mut bundle = panic_free_compiler_bundle();
        bundle.module.target_info.as_mut().expect("test target").pointer_size = 4;
        refresh_native_test_bundle_module_identity(&mut bundle);

        let error = NativeTrustIrChcPdrRunner::new()
            .solve_bundle_native_proof_grade(&bundle)
            .expect_err("32-bit target must not be checked with 64-bit pointer semantics");
        let NativeSolveError::InvalidInput { field, detail } = error else {
            panic!("target mismatch must be a structural preflight rejection");
        };
        assert_eq!(field, "native_trust_ir_bundle.module.target_info.pointer_size");
        assert!(detail.contains("declares 4-byte pointers"), "{detail}");
    }

    #[test]
    #[cfg(all(feature = "ay-chc-native", feature = "native-trust-ir-bundle"))]
    fn proof_grade_bundle_rejects_every_disabled_safety_option() {
        let bundle = panic_free_compiler_bundle();
        for disabled in [
            "check_signed_overflow",
            "check_unsigned_overflow",
            "check_div_by_zero",
            "check_memory_bounds",
        ] {
            let mut options = trust_mc_trust_bmc::TranslateOptions::default();
            match disabled {
                "check_signed_overflow" => options.check_signed_overflow = false,
                "check_unsigned_overflow" => options.check_unsigned_overflow = false,
                "check_div_by_zero" => options.check_div_by_zero = false,
                "check_memory_bounds" => options.check_memory_bounds = false,
                _ => unreachable!(),
            }
            let error = NativeTrustIrChcPdrRunner::new()
                .with_translate_options(options)
                .solve_bundle_native_proof_grade(&bundle)
                .expect_err("disabling any safety family must block authority minting");
            let NativeSolveError::InvalidInput { field, detail } = error else {
                panic!("{disabled} must fail at the translation-profile gate");
            };
            assert_eq!(field, "translate_options");
            assert!(detail.contains(disabled), "{disabled}: {detail}");
        }

        let mut non_safety_options = trust_mc_trust_bmc::TranslateOptions::default();
        non_safety_options.logic = Some("HORN".to_string());
        non_safety_options.timeout_ms = Some(10_000);
        let evidence = NativeTrustIrChcPdrRunner::new()
            .with_translate_options(non_safety_options)
            .solve_bundle_native_proof_grade(&bundle)
            .expect("logic/timeout customization must not disable a generated safety family");
        assert_eq!(evidence.obligations.len(), 1);
        evidence.obligations[0]
            .verification
            .authorized_native_proof()
            .expect("non-safety option customization must preserve opaque authority");
    }

    #[test]
    #[cfg(all(feature = "ay-chc-native", feature = "native-trust-ir-bundle"))]
    fn private_chc_validity_seal_rejects_mutation_reconstruction_and_transplant() {
        let solve_primary = || {
            NativeTrustIrChcPdrRunner::new()
                .solve_bundle_native_proof_grade(&compiler_style_safe_trust_ir_bundle())
                .expect("primary bundle should prove")
                .obligations
                .into_iter()
                .next()
                .expect("primary proof row")
                .verification
        };
        let original = solve_primary();
        original.authorized_native_proof().expect("fresh response must be authorized");
        assert!(
            original.clone().authorized_native_proof().is_err(),
            "cloning must deliberately drop affine CHC-validity authority"
        );

        let mut mutated_directory = solve_primary();
        mutated_directory.artifact_directory.push_str("-tampered");
        assert!(mutated_directory.authorized_native_proof().is_err());

        let mut mutated_diagnostics = solve_primary();
        mutated_diagnostics.outcome.diagnostics.push("forged diagnostic".to_string());
        assert!(mutated_diagnostics.authorized_native_proof().is_err());

        let serialized_verdict = serde_json::to_vec(&original.verdict).expect("serialize verdict");
        let reconstructed_verdict: trust_mc_core::FullVerificationVerdict =
            serde_json::from_slice(&serialized_verdict).expect("deserialize verdict");
        let reconstructed = TypedChcPdrFullVerification {
            route: original.route,
            cache_key: original.cache_key.clone(),
            artifact_directory: original.artifact_directory.clone(),
            outcome: original.outcome.clone(),
            verdict: reconstructed_verdict,
            private_native_proof_seal: None,
        };
        assert!(
            reconstructed.authorized_native_proof().is_err(),
            "reconstructing every public field must not reconstruct private authority"
        );

        let secondary = NativeTrustIrChcPdrRunner::new()
            .solve_bundle_native_proof_grade(&panic_free_compiler_bundle())
            .expect("secondary bundle should prove");
        let mut transplanted = solve_primary();
        transplanted.verdict = secondary.obligations[0].verification.verdict.clone();
        assert!(
            transplanted.authorized_native_proof().is_err(),
            "a valid verdict from another response must not transplant"
        );

        let raw_transport = original
            .native_proof_transport_record()
            .expect("live authority may emit a diagnostic snapshot");
        let serialized_transport =
            serde_json::to_vec(&raw_transport).expect("serialize diagnostic transport");
        let decoded_transport: NativeTypedChcPdrProofTransport =
            serde_json::from_slice(&serialized_transport).expect("deserialize transport");
        assert_eq!(decoded_transport, raw_transport);
        assert!(
            reconstructed.authorized_native_proof().is_err(),
            "a raw transport snapshot cannot restore the absent private seal"
        );
    }

    #[test]
    #[cfg(feature = "ay-chc-native")]
    fn solve_typed_chc_pdr_nontrivial_safe_runs_pdr() {
        let request =
            trust_mc_core::ChcPdrSolveRequest::new(safe_nontrivial_typed_chc_obligation())
                .with_options(
                    trust_mc_core::ChcPdrSolveOptions::default()
                        .with_engine(trust_mc_core::ChcPdrEngine::Pdr)
                        .with_timeout(Duration::from_secs(10)),
                );
        let solved = solve_typed_chc_pdr(request).expect("nontrivial safe CHC should be solved");

        assert_eq!(solved.obligation_id, "safe-nontrivial-typed-obligation");
        assert!(matches!(solved.status, trust_mc_core::ChcPdrSolveStatus::Unknown { .. }));
        assert!(solved.diagnostics.iter().any(|line| line.contains("private consumer replay")));
    }

    #[test]
    #[cfg(feature = "ay-chc-native")]
    fn solve_typed_chc_pdr_reachable_error_is_not_proved() {
        let request = trust_mc_core::ChcPdrSolveRequest::new(typed_chc_obligation(true))
            .with_options(
                trust_mc_core::ChcPdrSolveOptions::default()
                    .with_engine(trust_mc_core::ChcPdrEngine::Pdr)
                    .with_timeout(Duration::from_secs(10)),
            );
        let solved = solve_typed_chc_pdr(request).expect("reachable error should solve");

        assert_eq!(solved.obligation_id, "typed-obligation");
        assert!(
            !matches!(solved.status, trust_mc_core::ChcPdrSolveStatus::Proved { .. }),
            "reachable error must not be reported as proved"
        );
    }

    /// (α, plain path / mint site c) An ay-chc replay-verified refutation with
    /// an exact (zero-drop, zero-havoc) lowering mints a witness whose digests
    /// independently recompute from the retained request.
    ///
    /// The adaptive portfolio is used because the plain path has no direct-SMT
    /// shortcut and pure PDR cannot decide a false property (it returns
    /// Unknown; see `solve_typed_chc_pdr_reachable_error_is_not_proved`).
    #[test]
    #[cfg(feature = "ay-chc-native")]
    fn solve_typed_chc_pdr_reachable_error_mints_bound_refutation_witness() {
        let obligation = typed_chc_obligation(true);
        let engine = trust_mc_core::ChcPdrEngine::AdaptivePortfolio;
        let request = trust_mc_core::ChcPdrSolveRequest::new(obligation.clone()).with_options(
            trust_mc_core::ChcPdrSolveOptions::default()
                .with_engine(engine)
                .with_timeout(Duration::from_secs(10)),
        );
        let solved = solve_typed_chc_pdr(request).expect("reachable error should solve");

        let trust_mc_core::ChcPdrSolveStatus::Refuted { witness: Some(witness) } = &solved.status
        else {
            panic!("reachable error must refute with a witness, got {:?}", solved.status);
        };

        assert_eq!(witness.obligation_id, "typed-obligation");
        // Consumer-style independent recomputation of both digests from the
        // retained request, not from any solver-returned value.
        let expected = normalized_typed_chc_pdr_input(&obligation)
            .expect("retained refutable obligation should normalize");
        assert_eq!(expected.route, TypedChcPdrRoute::PdrProof);
        assert_eq!(witness.encoded_formula_sha256, expected.normalized_input_hash.value);
        assert_eq!(
            witness.semantic_config_sha256,
            typed_chc_pdr_semantic_config_sha256(engine, expected.route)
        );
        assert!(
            witness.concreteness.is_exact_with_zero_counts(),
            "exact-or-reject lowering must attest all-zero concreteness counts: {:?}",
            witness.concreteness
        );
        assert!(
            matches!(
                witness.verification,
                trust_mc_core::ChcPdrCexVerification::AyChcReplayVerified { .. }
            ),
            "plain-path refutations are ay-chc replay-verified: {:?}",
            witness.verification
        );
        assert!(
            witness.counterexample_json.contains("trust_mc.typed-chc-pdr-counterexample/v1"),
            "witness carries the existing counterexample artifact schema: {}",
            witness.counterexample_json
        );
    }

    /// (α, full path / mint site b) The full-verification direct-SMT shortcut
    /// refutes the same fixture and mints a DirectSmtModel witness with the
    /// same independently recomputable digest binding.
    #[test]
    #[cfg(feature = "ay-chc-native")]
    fn solve_typed_chc_pdr_full_reachable_error_mints_bound_refutation_witness() {
        let obligation = typed_chc_obligation(true);
        let request = trust_mc_core::ChcPdrSolveRequest::new(obligation.clone()).with_options(
            trust_mc_core::ChcPdrSolveOptions::default()
                .with_engine(trust_mc_core::ChcPdrEngine::Pdr)
                .with_timeout(Duration::from_secs(10)),
        );
        let solved = solve_typed_chc_pdr_full_verification(request)
            .expect("reachable error should fully verify");

        assert!(
            matches!(solved.verdict, trust_mc_core::FullVerificationVerdict::Failed { .. }),
            "full verification of a reachable error is Failed: {:?}",
            solved.verdict
        );
        let trust_mc_core::ChcPdrSolveStatus::Refuted { witness: Some(witness) } =
            &solved.outcome.status
        else {
            panic!("reachable error must refute with a witness, got {:?}", solved.outcome.status);
        };

        assert_eq!(witness.obligation_id, "typed-obligation");
        let expected = normalized_typed_chc_pdr_input(&obligation)
            .expect("retained refutable obligation should normalize");
        assert_eq!(witness.encoded_formula_sha256, expected.normalized_input_hash.value);
        assert_eq!(
            witness.semantic_config_sha256,
            typed_chc_pdr_semantic_config_sha256(trust_mc_core::ChcPdrEngine::Pdr, expected.route)
        );
        assert!(witness.concreteness.is_exact_with_zero_counts());
        assert_eq!(witness.verification, trust_mc_core::ChcPdrCexVerification::DirectSmtModel);
        assert!(witness.counterexample_json.contains("trust_mc.typed-chc-pdr-counterexample/v1"));
        let replay = independently_replay_typed_chc_pdr_refutation_witness(
            &obligation,
            trust_mc_core::ChcPdrEngine::Pdr,
            witness,
        )
        .expect("consumer must independently replay the direct-SMT trace and exact model");
        assert!(replay.contains("acyclic derivation"), "{replay}");
    }

    /// Consumer replay is fail-closed under every serialized authority input:
    /// formula/config bindings, proof class, trace, total model, concreteness,
    /// strict payload shape, and payload budget.
    #[test]
    #[cfg(feature = "ay-chc-native")]
    fn independent_direct_smt_refutation_replay_rejects_mutations() {
        let obligation = typed_chc_obligation(true);
        let request = trust_mc_core::ChcPdrSolveRequest::new(obligation.clone()).with_options(
            trust_mc_core::ChcPdrSolveOptions::default()
                .with_engine(trust_mc_core::ChcPdrEngine::Pdr)
                .with_timeout(Duration::from_secs(10)),
        );
        let solved = solve_typed_chc_pdr_full_verification(request)
            .expect("reachable error should fully verify");
        let trust_mc_core::ChcPdrSolveStatus::Refuted { witness: Some(witness) } =
            &solved.outcome.status
        else {
            panic!("reachable error must carry a refutation witness");
        };
        let original = witness.as_ref().clone();
        independently_replay_typed_chc_pdr_refutation_witness(
            &obligation,
            trust_mc_core::ChcPdrEngine::Pdr,
            &original,
        )
        .expect("unmodified witness replays");

        let rejects = |label: &str, mutated: &trust_mc_core::ChcPdrRefutationWitness| {
            assert!(
                independently_replay_typed_chc_pdr_refutation_witness(
                    &obligation,
                    trust_mc_core::ChcPdrEngine::Pdr,
                    mutated,
                )
                .is_err(),
                "{label} mutation must fail closed"
            );
        };

        let mut mutated = original.clone();
        mutated.encoded_formula_sha256 = "00".repeat(32);
        rejects("formula digest", &mutated);

        let mut mutated = original.clone();
        mutated.semantic_config_sha256 = "11".repeat(32);
        rejects("semantic configuration", &mutated);

        assert!(
            independently_replay_typed_chc_pdr_refutation_witness(
                &obligation,
                trust_mc_core::ChcPdrEngine::AdaptivePortfolio,
                &original,
            )
            .is_err(),
            "a consumer engine mismatch must fail closed"
        );

        let mut mutated = original.clone();
        mutated.verification =
            trust_mc_core::ChcPdrCexVerification::BoundedUnrollDirectSmtModel { k: 4 };
        rejects("proof class", &mutated);

        let mut mutated = original.clone();
        mutated.concreteness = trust_mc_core::ChcPdrEncodingConcreteness::ExactEncoding {
            translation_drops: 0,
            havocs: 1,
            undef_diagnostic_havocs: 0,
        };
        rejects("concreteness", &mutated);

        let mutate_payload =
            |witness: &mut trust_mc_core::ChcPdrRefutationWitness,
             mutate: &dyn Fn(&mut serde_json::Value)| {
                let mut payload: serde_json::Value =
                    serde_json::from_str(&witness.counterexample_json).expect("fixture payload");
                mutate(&mut payload);
                witness.counterexample_json = payload.to_string();
            };

        let mut mutated = original.clone();
        mutate_payload(&mut mutated, &|payload| {
            payload
                .as_object_mut()
                .expect("payload object")
                .insert("unrecognized_authority".to_string(), serde_json::json!(true));
        });
        rejects("unknown JSON field", &mutated);

        let mut mutated = original.clone();
        mutate_payload(&mut mutated, &|payload| {
            let trace = payload["derivation_clause_indices"].as_array_mut().expect("trace array");
            let repeated = trace.first().expect("nonempty trace").clone();
            trace.push(repeated);
        });
        rejects("derivation trace", &mutated);

        let mut mutated = original.clone();
        mutate_payload(&mut mutated, &|payload| {
            payload["witness_model"].as_object_mut().expect("model object").insert(
                "forged_extra_binding".to_string(),
                serde_json::json!({ "kind": "bool", "value": true }),
            );
        });
        rejects("model domain", &mutated);

        let mut mutated = original;
        mutated.counterexample_json = "x".repeat(MAX_REFUTATION_REPLAY_PAYLOAD_BYTES + 1);
        rejects("payload budget", &mutated);
    }

    /// (β) Nonzero lowering-exactness accounting — any counter, including
    /// "sound" havoc — must suppress witness minting entirely.
    #[test]
    #[cfg(feature = "ay-chc-native")]
    fn typed_chc_pdr_refutation_witness_requires_exact_lowering_accounting() {
        let hash = trust_mc_core::EvidenceHash::sha256_bytes(b"formula");
        let cex = serde_json::json!({ "schema": "trust_mc.typed-chc-pdr-counterexample/v1" });
        let mint = |lowering: Option<typed_chc_ay::TypedChcLoweringAccounting>| {
            typed_chc_pdr_refutation_witness(
                "typed-obligation",
                &hash,
                trust_mc_core::ChcPdrEngine::Pdr,
                TypedChcPdrRoute::PdrProof,
                &cex,
                trust_mc_core::ChcPdrCexVerification::DirectSmtModel,
                lowering,
            )
        };

        let exact = typed_chc_ay::TypedChcLoweringAccounting::default();
        let witness = mint(Some(exact)).expect("exact accounting mints a witness");
        assert!(witness.concreteness.is_exact_with_zero_counts());
        assert_eq!(witness.encoded_formula_sha256, hash.value);

        for dirty in [
            typed_chc_ay::TypedChcLoweringAccounting { translation_drops: 1, ..exact },
            typed_chc_ay::TypedChcLoweringAccounting { havocs: 1, ..exact },
            typed_chc_ay::TypedChcLoweringAccounting { undef_diagnostic_havocs: 1, ..exact },
        ] {
            assert!(
                mint(Some(dirty)).is_none(),
                "nonzero accounting must suppress the witness: {dirty:?}"
            );
        }
        assert!(mint(None).is_none(), "absent accounting must suppress the witness");
    }

    /// (γ) The semantic-configuration digest is deterministic and binds the
    /// engine and route.
    #[test]
    fn typed_chc_pdr_semantic_config_digest_is_deterministic_and_config_bound() {
        let digest = |engine, route| typed_chc_pdr_semantic_config_sha256(engine, route);
        let pdr = trust_mc_core::ChcPdrEngine::Pdr;
        let portfolio = trust_mc_core::ChcPdrEngine::AdaptivePortfolio;

        assert_eq!(
            digest(pdr, TypedChcPdrRoute::PdrProof),
            digest(pdr, TypedChcPdrRoute::PdrProof),
            "same configuration must digest identically"
        );
        assert_eq!(
            digest(pdr, TypedChcPdrRoute::PdrProof),
            trust_mc_core::EvidenceHash::sha256_bytes(
                typed_chc_pdr_semantic_config(pdr, TypedChcPdrRoute::PdrProof).as_bytes()
            )
            .value,
            "digest is the SHA-256 of the canonical serialization"
        );
        assert_ne!(
            digest(pdr, TypedChcPdrRoute::PdrProof),
            digest(portfolio, TypedChcPdrRoute::PdrProof),
            "engine must be bound into the digest"
        );
        assert_ne!(
            digest(pdr, TypedChcPdrRoute::PdrProof),
            digest(pdr, TypedChcPdrRoute::TriviallySafe),
            "route must be bound into the digest"
        );
        let value = digest(pdr, TypedChcPdrRoute::PdrProof);
        assert_eq!(value.len(), 64);
        assert!(value.bytes().all(|byte| byte.is_ascii_hexdigit() && !byte.is_ascii_uppercase()));
    }

    #[test]
    fn solve_typed_chc_pdr_rejects_placeholders() {
        let real = typed_chc_obligation(false);
        let placeholder = trust_mc_core::MirChcPdrObligation::router_placeholder(
            real.obligation_id,
            real.function_name,
            real.kind,
            real.vc,
        );
        let err = solve_typed_chc_pdr(trust_mc_core::ChcPdrSolveRequest::new(placeholder))
            .expect_err("router placeholders must not solve as proof input");

        match err {
            NativeSolveError::InvalidInput { field, detail } => {
                assert_eq!(field, "request.obligation");
                assert!(detail.contains("not MIR-derived"));
            }
            NativeSolveError::Unsupported(_) => panic!("placeholder should fail validation"),
            NativeSolveError::SolverFailed { .. } => panic!("placeholder should fail validation"),
            NativeSolveError::ProofGradeRejected { .. } => {
                panic!("placeholder should fail validation")
            }
        }
    }

    #[test]
    fn solve_native_keeps_chc_payloads_unsupported_after_validation() {
        let artifact = NativeEncodedArtifact::new(
            "obligation-1",
            "crate::harness",
            NativeVcKind::Chc,
            b"opaque-chc".to_vec(),
            NativeProofProvenance::unbounded(NativeProofMode::Chc),
        );
        let err = solve_native(NativeSolveRequest::new(artifact))
            .expect_err("CHC payload should fail closed for now");

        match err {
            NativeSolveError::Unsupported(unsupported) => {
                assert_eq!(unsupported.operation, NativeOperation::Solve);
                assert_eq!(unsupported.reason, "chc_native_payload_not_supported");
            }
            NativeSolveError::InvalidInput { .. } => panic!("request should validate"),
            NativeSolveError::SolverFailed { .. } => panic!("CHC payload should not reach solver"),
            NativeSolveError::ProofGradeRejected { .. } => {
                panic!("CHC payload should not reach proof admission")
            }
        }
    }

    #[test]
    #[cfg(any(feature = "ay-chc-native", feature = "ay-direct"))]
    fn solve_native_smtlib_bmc_unsat_is_proved() {
        let provenance = compiler_bmc_provenance(3);
        let request = NativeSolveRequest::new(sample_artifact(provenance.clone()));
        let solved = solve_native(request).expect("SMT-LIB BMC should solve natively");

        assert_eq!(solved.obligation_id, "obligation-1");
        assert_eq!(solved.verdict, NativeSolverVerdict::Proved);
        assert_eq!(solved.provenance, provenance);
        assert_eq!(solved.proof_certificate, None);
    }

    #[test]
    #[cfg(any(feature = "ay-chc-native", feature = "ay-direct"))]
    fn solve_native_smtlib_bmc_sat_is_failed() {
        let provenance = NativeProofProvenance::bmc(2);
        let artifact = NativeEncodedArtifact::new(
            "obligation-1",
            "crate::harness",
            NativeVcKind::Bmc,
            smtlib_bmc_payload(
                "obligation-1",
                "crate::harness",
                "(set-logic QF_LIA)\n(assert true)\n(check-sat)\n",
                &provenance,
            ),
            provenance,
        );
        let solved = solve_native(NativeSolveRequest::new(artifact))
            .expect("satisfiable SMT-LIB BMC should solve natively");

        assert_eq!(solved.verdict, NativeSolverVerdict::Failed);
    }

    #[test]
    fn solve_native_rejects_payload_provenance_mismatch() {
        let artifact_provenance = NativeProofProvenance::bmc(3);
        let payload_provenance = NativeProofProvenance::bmc(4);
        let artifact = NativeEncodedArtifact::new(
            "obligation-1",
            "crate::harness",
            NativeVcKind::Bmc,
            smtlib_bmc_payload(
                "obligation-1",
                "crate::harness",
                "(set-logic QF_LIA)\n(assert false)\n(check-sat)\n",
                &payload_provenance,
            ),
            artifact_provenance,
        );

        let err = solve_native(NativeSolveRequest::new(artifact))
            .expect_err("payload/artifact provenance mismatch must be rejected");

        assert!(
            matches!(err, NativeSolveError::InvalidInput { field, .. } if field == "artifact.payload.provenance.bmc_depth")
        );
    }

    #[test]
    fn solve_native_rejects_proof_certificate_request_for_bmc() {
        let request = NativeSolveRequest::new(sample_artifact(NativeProofProvenance::bmc(3)))
            .with_proof_certificate(true);
        let err = solve_native(request).expect_err("proof certificates are not implemented yet");

        assert!(
            matches!(err, NativeSolveError::Unsupported(unsupported) if unsupported.reason == "proof_certificate_not_supported")
        );
    }

    #[test]
    fn solve_native_rejects_empty_payload() {
        let artifact = NativeEncodedArtifact::new(
            "obligation-1",
            "crate::harness",
            NativeVcKind::Bmc,
            Vec::new(),
            NativeProofProvenance::bmc(3),
        );
        let err = solve_native(NativeSolveRequest::new(artifact))
            .expect_err("empty payload must be rejected");

        assert!(
            matches!(err, NativeSolveError::InvalidInput { field, .. } if field == "artifact.payload")
        );
    }

    // ---- G2 real-call IC3 loop lane (FIX_PLAN Test plan) ----

    /// `op` helper mirroring ay's `ic3_lane/tests.rs`: wrap operands in `Arc`.
    #[cfg(feature = "ay-chc-native")]
    fn chc_op(o: ay_chc::ChcOp, args: Vec<ay_chc::ChcExpr>) -> ay_chc::ChcExpr {
        ay_chc::ChcExpr::Op(o, args.into_iter().map(std::sync::Arc::new).collect())
    }

    /// Rebuild ay's `bv64_real_ssa_cfg` fixture (ay-chc `ic3_lane/tests.rs:444`):
    /// the real targo-lowered multi-block cyclic SSA CFG for the count-parity
    /// realcall loop. `step == 1` is the genuine parity loop (Safe, a validating
    /// invariant exists); `step == 2` is the false control (acc toggles while the
    /// count parity is pinned, so `acc != count[0]` is reachable and NO
    /// validating invariant exists).
    #[cfg(feature = "ay-chc-native")]
    fn bv64_real_ssa_cfg(step: u128) -> ay_chc::ChcProblem {
        use ay_chc::{ChcExpr, ChcOp, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause};
        let mut p = ay_chc::ChcProblem::new();
        let w = ChcSort::BitVec;
        let s5 = vec![ChcSort::Bool, w(64), w(64), ChcSort::Bool, w(64)];
        let s4 = vec![ChcSort::Bool, w(64), ChcSort::Bool, w(64)];
        let bb0 = p.declare_predicate("bb0", vec![ChcSort::Bool, w(64)]);
        let bb1 = p.declare_predicate("bb1", s5.clone());
        let bb2 = p.declare_predicate("bb2", s4.clone());
        let bb3 = p.declare_predicate("bb3", s5.clone());
        let bb4 = p.declare_predicate("bb4", s5);
        let error = p.declare_predicate("error", vec![]);

        let v = |n: &str, s: ChcSort| ChcExpr::Var(ChcVar::new(n, s));
        let parity = |c: &ChcExpr| {
            chc_op(
                ChcOp::Eq,
                vec![
                    chc_op(ChcOp::BvAnd, vec![c.clone(), ChcExpr::BitVec(1, 64)]),
                    ChcExpr::BitVec(1, 64),
                ],
            )
        };

        // [0] bb0(c13,c15) :- true
        p.add_clause(HornClause::new(
            ClauseBody::empty(),
            ClauseHead::Predicate(bb0, vec![v("c13", ChcSort::Bool), v("c15", w(64))]),
        ));
        // [1] enter: bb1(u0,u2,v39,false,0) :- bb0(c13,c15)
        p.add_clause(HornClause::new(
            ClauseBody::predicates_only(vec![(
                bb0,
                vec![v("c13", ChcSort::Bool), v("c15", w(64))],
            )]),
            ClauseHead::Predicate(
                bb1,
                vec![
                    v("u0", ChcSort::Bool),
                    v("u2", w(64)),
                    v("v39", w(64)),
                    ChcExpr::Bool(false),
                    ChcExpr::BitVec(0, 64),
                ],
            ),
        ));
        let bb1_body = || {
            (
                bb1,
                vec![
                    v("t12", ChcSort::Bool),
                    v("t14", w(64)),
                    v("t39", w(64)),
                    v("c13", ChcSort::Bool),
                    v("c15", w(64)),
                ],
            )
        };
        let c13 = v("c13", ChcSort::Bool);
        let c15 = v("c15", w(64));
        // [2] assert-FAIL: bb3(..) :- bb1(..), Not(c13 == parity(c15))
        p.add_clause(HornClause::new(
            ClauseBody::new(
                vec![bb1_body()],
                Some(chc_op(ChcOp::Not, vec![chc_op(ChcOp::Eq, vec![c13.clone(), parity(&c15)])])),
            ),
            ClauseHead::Predicate(
                bb3,
                vec![
                    v("t12", ChcSort::Bool),
                    v("t14", w(64)),
                    v("t39", w(64)),
                    c13.clone(),
                    c15.clone(),
                ],
            ),
        ));
        // [3] assert-OK: bb2(..) :- bb1(..), (c13 == parity(c15))
        p.add_clause(HornClause::new(
            ClauseBody::new(
                vec![bb1_body()],
                Some(chc_op(ChcOp::Eq, vec![c13.clone(), parity(&c15)])),
            ),
            ClauseHead::Predicate(
                bb2,
                vec![v("t12", ChcSort::Bool), v("t14", w(64)), c13.clone(), c15.clone()],
            ),
        ));
        // [4] update: bb4(t12,t14, count+step, !acc, c15) :- bb2(t12,t14,c13,c15)
        let acc_next = chc_op(
            ChcOp::Ite,
            vec![c13.clone(), chc_op(ChcOp::Not, vec![ChcExpr::Bool(true)]), ChcExpr::Bool(true)],
        );
        let count_next = chc_op(ChcOp::BvAdd, vec![c15.clone(), ChcExpr::BitVec(step, 64)]);
        p.add_clause(HornClause::new(
            ClauseBody::predicates_only(vec![(
                bb2,
                vec![v("t12", ChcSort::Bool), v("t14", w(64)), c13.clone(), c15.clone()],
            )]),
            ClauseHead::Predicate(
                bb4,
                vec![v("t12", ChcSort::Bool), v("t14", w(64)), count_next, acc_next, c15.clone()],
            ),
        ));
        // [5] error() :- bb3(..)
        p.add_clause(HornClause::new(
            ClauseBody::predicates_only(vec![(
                bb3,
                vec![
                    v("t12", ChcSort::Bool),
                    v("t14", w(64)),
                    v("t39", w(64)),
                    c13.clone(),
                    c15.clone(),
                ],
            )]),
            ClauseHead::Predicate(error, vec![]),
        ));
        // [7] loop back: bb1(t12,t14,t39,c13, t39) :- bb4(t12,t14,t39,c13,c15)
        p.add_clause(HornClause::new(
            ClauseBody::predicates_only(vec![(
                bb4,
                vec![
                    v("t12", ChcSort::Bool),
                    v("t14", w(64)),
                    v("t39", w(64)),
                    c13.clone(),
                    c15.clone(),
                ],
            )]),
            ClauseHead::Predicate(
                bb1,
                vec![
                    v("t12", ChcSort::Bool),
                    v("t14", w(64)),
                    v("t39", w(64)),
                    c13,
                    v("t39", w(64)),
                ],
            ),
        ));
        // [8] false :- error()
        p.add_clause(HornClause::new(
            ClauseBody::predicates_only(vec![(error, vec![])]),
            ClauseHead::False,
        ));
        p
    }

    /// Build the lane's calling context (obligation/stats/normalized-input/
    /// cache-key/artifact-dir) for a standalone lane unit test.
    #[cfg(feature = "ay-chc-native")]
    #[allow(clippy::type_complexity)]
    fn ic3_lane_test_context(
        problem: &ay_chc::ChcProblem,
    ) -> (
        trust_mc_core::MirChcPdrObligation,
        trust_mc_core::ChcPdrStats,
        String,
        trust_mc_core::FullVerificationCacheKey,
        String,
    ) {
        let obligation = typed_chc_obligation(false);
        let stats = obligation.stats();
        let normalized_input = ay_encode::normalized_chc_input(problem);
        let options = trust_mc_core::ChcPdrSolveOptions::default();
        let normalized = native_typed_chc_pdr_normalized_input(
            &obligation,
            TypedChcPdrRoute::PdrProof,
            normalized_input.clone(),
        );
        let cache_key = typed_full_verification_cache_key(&obligation, &options, &normalized);
        let artifact_directory = typed_artifact_directory(&cache_key);
        (obligation, stats, normalized_input, cache_key, artifact_directory)
    }

    #[test]
    #[cfg(feature = "ay-chc-native")]
    fn ic3_loop_lane_admits_bv64_realcall_parity() {
        // step == 1: the genuine count-parity realcall loop. The IC3 lane must
        // synthesize a loop invariant that survives BOTH re-validations (the
        // explicit `validate_external_invariant_model` gate AND the internal one
        // inside `prove_with_external_model`) and be transported as a reject-only
        // `PdrInvariant` candidate for the compiler's fresh private replay gate.
        let problem = bv64_real_ssa_cfg(1);
        assert!(problem.has_cycles(), "the realcall loop CFG must be cyclic");
        let (obligation, stats, normalized_input, cache_key, artifact_directory) =
            ic3_lane_test_context(&problem);

        let verification = try_ic3_loop_lane(
            &problem,
            &obligation,
            stats,
            &normalized_input,
            &cache_key,
            &artifact_directory,
            TypedChcPdrRoute::PdrProof,
            Duration::from_secs(60),
        )
        .expect("IC3 loop lane must admit the true bv64 realcall parity loop");

        assert_eq!(verification.route, TypedChcPdrRoute::PdrProof);
        assert!(matches!(
            verification.outcome.status,
            trust_mc_core::ChcPdrSolveStatus::Unknown { .. }
        ));
        assert!(!is_proof_grade_native_full_verification_verdict(&verification.verdict));
        let trust_mc_core::FullVerificationVerdict::Proved {
            evidence: trust_mc_core::FullProofEvidence::ChcPdr(proof),
        } = verification.verdict
        else {
            panic!("lane should produce CHC/PDR proof evidence");
        };
        assert_eq!(proof.kind, trust_mc_core::ChcPdrProofKind::PdrInvariant);
        let invariant_artifact = proof
            .artifacts
            .iter()
            .find(|artifact| {
                artifact.kind == trust_mc_core::FullVerificationArtifactKind::PdrInvariantModel
            })
            .expect("lane evidence must carry the PDR invariant model artifact");
        let invariant_bytes = invariant_artifact
            .materialized_bytes()
            .expect("PDR invariant model must be materialized");
        let invariant_json: serde_json::Value = serde_json::from_slice(invariant_bytes)
            .expect("PDR invariant model must be AY's versioned JSON envelope");
        assert_eq!(invariant_json["schema"], ay_chc::CHC_QF_INVARIANT_MODEL_ARTIFACT_SCHEMA);
        ay_chc::parse_qf_invariant_model_artifact(&problem, invariant_bytes)
            .expect("transported IC3 invariant must pass AY's strict canonical parser");
    }

    #[test]
    #[cfg(feature = "ay-chc-native")]
    fn ic3_loop_lane_rejects_false_parity() {
        // NEGATIVE CONTROL — the required soundness guardrail. step == 2: acc
        // toggles but the count parity is pinned, so `acc != count[0]` is
        // reachable and the loop is NOT safe. Re-validation MUST reject any
        // candidate, so the lane returns None and NEVER a Proved verdict. If this
        // ever returns Some/Proved, the lane is unsound — STOP.
        let problem = bv64_real_ssa_cfg(2);
        assert!(problem.has_cycles(), "the false loop CFG is still cyclic");
        let (obligation, stats, normalized_input, cache_key, artifact_directory) =
            ic3_lane_test_context(&problem);

        let verification = try_ic3_loop_lane(
            &problem,
            &obligation,
            stats,
            &normalized_input,
            &cache_key,
            &artifact_directory,
            TypedChcPdrRoute::PdrProof,
            Duration::from_secs(60),
        );

        assert!(
            verification.is_none(),
            "IC3 loop lane must REJECT the false +2 parity loop (re-validation fails)"
        );
    }

    // ===== Bounded-unroll refutation lane (shift-reduction BMC) =====

    /// What the loop body adds to the accumulator each iteration.
    #[cfg(feature = "ay-chc-native")]
    #[derive(Clone, Copy)]
    enum LoopAddend {
        /// `t += x` for the entry parameter `x` (i128 reduction shape).
        Param,
        /// `t += x << 4` for the entry parameter `x` (the shift-reduction
        /// fixture shape: `t += (x as u8) << 4`).
        ShiftedParam,
        /// `t += c` for a constant `c` (input-independent overflow depth).
        Const(i128),
    }

    /// Build the trust-ir mirror of the gate's loop-reduction fixtures:
    ///
    /// ```text
    /// fn loop_accumulator(x: T) -> T {
    ///     let mut t: T = 0;
    ///     let mut i: u64 = 0;
    ///     while i < iterations { t += addend; i += 1; }
    ///     t
    /// }
    /// ```
    ///
    /// as a typed CHC obligation (the exact translation the native bundle
    /// path produces for the requested function). The `t += addend` unsigned/
    /// signed overflow VC is the L0 obligation under test.
    #[cfg(feature = "ay-chc-native")]
    fn loop_accumulator_obligation(
        acc_ty: trust_ir::ty::Ty,
        iterations: i128,
        addend: LoopAddend,
    ) -> trust_mc_core::MirChcPdrObligation {
        use trust_ir::inst::{BinOp, ICmpOp};
        use trust_ir::ty::Ty;
        use trust_ir_build::ModuleBuilder;

        let mut mb = ModuleBuilder::new("bounded_unroll_fixture");
        let param_tys = match addend {
            LoopAddend::Const(_) => vec![],
            _ => vec![acc_ty.clone()],
        };
        let ft = mb.add_func_type(param_tys, vec![acc_ty.clone()]);
        {
            let mut fb = mb.function("loop_accumulator", ft);
            let entry = fb.create_block();
            let header = fb.create_block();
            let body = fb.create_block();
            let exit = fb.create_block();

            fb.switch_to_block(entry);
            fb.set_entry(entry);
            let addend_value = match addend {
                LoopAddend::Param => fb.add_block_param(entry, acc_ty.clone()),
                LoopAddend::ShiftedParam => {
                    let x = fb.add_block_param(entry, acc_ty.clone());
                    let four = fb.iconst(acc_ty.clone(), 4);
                    // `x << 4`: truncating shift (bits out are dropped), the
                    // constant amount keeps its own shift-amount VC unsat.
                    fb.binop(BinOp::Shl, acc_ty.clone(), x, four)
                }
                LoopAddend::Const(c) => fb.iconst(acc_ty.clone(), c),
            };
            let zero_i = fb.iconst(Ty::U64, 0);
            let zero_t = fb.iconst(acc_ty.clone(), 0);
            fb.br(header, vec![zero_i, zero_t]);

            // Loop-carried state travels as explicit BLOCK ARGUMENTS on every
            // edge (the shape the CHC translator threads exactly); a
            // dominance-scoped cross-block reference would instead be encoded
            // as a fresh (havoc'd) variable and the grounding gate would
            // decline the whole fixture.
            let i = fb.add_block_param(header, Ty::U64);
            let t = fb.add_block_param(header, acc_ty.clone());
            fb.switch_to_block(header);
            let bound = fb.iconst(Ty::U64, iterations);
            let in_loop = fb.icmp(ICmpOp::Ult, Ty::U64, i, bound);
            fb.condbr(in_loop, body, vec![i, t], exit, vec![t]);

            let i_body = fb.add_block_param(body, Ty::U64);
            let t_body = fb.add_block_param(body, acc_ty.clone());
            fb.switch_to_block(body);
            // The obligation under test: loop-carried accumulator add.
            let t_next = fb.add(acc_ty.clone(), t_body, addend_value);
            let one = fb.iconst(Ty::U64, 1);
            let i_next = fb.add(Ty::U64, i_body, one);
            fb.br(header, vec![i_next, t_next]);

            let t_exit = fb.add_block_param(exit, acc_ty.clone());
            fb.switch_to_block(exit);
            fb.ret(vec![t_exit]);
            fb.build();
        }
        let module = mb.build();
        let function = module.functions[0].id;
        let vc = trust_mc_trust_bmc::trust_ir_function_to_chc_vc(
            &module,
            function,
            &trust_mc_trust_bmc::TranslateOptions::default(),
        )
        .expect("fixture function translates");
        let mut obligation = trust_mc_core::MirChcPdrObligation::new(
            "bounded-unroll-fixture",
            "loop_accumulator",
            trust_mc_core::MirObligationKind::Assertion,
            vc,
        );
        // Mirror the native-bundle translator's metadata: the VC above IS its
        // complete-by-construction lowering, and the bounded-unroll lane
        // self-gates on this marker (see the lane's eligibility comment).
        obligation.native_metadata = Some(
            trust_mc_core::NativeTypedChcObligationMetadata::new(
                "tRust",
                "trust_ir-module",
                None,
                trust_mc_core::NativeArtifactDigest::new("sha256", "00".repeat(32)),
                trust_mc_core::NativeArtifactDigest::new("sha256", "11".repeat(32)),
                0,
                "chc",
                0,
                vec![],
                vec![],
            )
            .with_structural_reachability_complete(true),
        );
        obligation
    }

    /// Drive the bounded-unroll lane exactly as `solve_typed_chc_pdr_full_with_ay`'s
    /// Unknown arm does, without paying for the primary PDR solve.
    #[cfg(feature = "ay-chc-native")]
    fn run_bounded_unroll_lane(
        obligation: &trust_mc_core::MirChcPdrObligation,
        ladder: &[u32],
    ) -> Option<TypedChcPdrFullVerification> {
        let request = trust_mc_core::ChcPdrSolveRequest::new(obligation.clone()).with_options(
            trust_mc_core::ChcPdrSolveOptions::default()
                .with_engine(trust_mc_core::ChcPdrEngine::Pdr),
        );
        let prepared = prepare_validated_typed_chc_pdr_input(obligation).expect("fixture prepares");
        assert_eq!(prepared.normalized.route, TypedChcPdrRoute::PdrProof);
        let problem = prepared.problem.expect("PdrProof route retains the lowered problem");
        let stats = obligation.stats();
        let cache_key =
            typed_full_verification_cache_key(obligation, &request.options, &prepared.normalized);
        let artifact_directory = typed_artifact_directory(&cache_key);
        try_bounded_unroll_refutation_lane_with_ladder(
            &problem,
            &request,
            stats,
            &prepared.normalized.normalized_input_hash,
            prepared.normalized.route,
            &cache_key,
            &artifact_directory,
            prepared.lowering,
            Duration::from_secs(120),
            ladder,
        )
    }

    /// Collect every bit-vector value of the given width from a direct-SMT
    /// witness model (the typed JSON rendering of `smt_value_to_json`).
    #[cfg(feature = "ay-chc-native")]
    fn collect_bitvec_model_values(model: &serde_json::Value, width: u64, out: &mut Vec<u128>) {
        match model {
            serde_json::Value::Object(map) => {
                if map.get("kind").and_then(serde_json::Value::as_str) == Some("bit_vec")
                    && map.get("width").and_then(serde_json::Value::as_u64) == Some(width)
                {
                    if let Some(value) = map.get("value").and_then(serde_json::Value::as_str) {
                        if let Ok(value) = value.parse::<u128>() {
                            out.push(value);
                        }
                    }
                }
                for value in map.values() {
                    collect_bitvec_model_values(value, width, out);
                }
            }
            serde_json::Value::Array(values) => {
                for value in values {
                    collect_bitvec_model_values(value, width, out);
                }
            }
            _ => {}
        }
    }

    /// Mirror of the u8 shift-reduction fixture semantics (`t += (x << 4)` over
    /// 64 iterations, Rust shift/overflow semantics): the 1-based iteration at
    /// which the accumulator add first overflows, `None` if it never does.
    #[cfg(feature = "ay-chc-native")]
    fn u8_shift_reduction_overflow_iteration(x: u8) -> Option<usize> {
        let addend = x << 4; // truncating: bits shifted out are dropped, no panic
        let mut t: u8 = 0;
        for iteration in 1..=64usize {
            match t.checked_add(addend) {
                Some(next) => t = next,
                None => return Some(iteration),
            }
        }
        None
    }

    /// Mirror of the i128 accumulator fixture semantics (`t += x` over 4
    /// iterations): the 1-based iteration of the first signed overflow.
    #[cfg(feature = "ay-chc-native")]
    fn i128_accumulator_overflow_iteration(x: i128) -> Option<usize> {
        let mut t: i128 = 0;
        for iteration in 1..=4usize {
            match t.checked_add(x) {
                Some(next) => t = next,
                None => return Some(iteration),
            }
        }
        None
    }

    /// Unpack a lane result into (witness, k, parsed witness model).
    #[cfg(feature = "ay-chc-native")]
    fn unpack_bounded_unroll_refutation(
        verification: &TypedChcPdrFullVerification,
    ) -> (&trust_mc_core::ChcPdrRefutationWitness, u64, serde_json::Value) {
        let trust_mc_core::ChcPdrSolveStatus::Refuted { witness: Some(witness) } =
            &verification.outcome.status
        else {
            panic!("lane result must be Refuted with witness, got {:?}", verification.outcome);
        };
        let trust_mc_core::ChcPdrCexVerification::BoundedUnrollDirectSmtModel { k } =
            witness.verification
        else {
            panic!("lane witness must carry the bounded-unroll kind: {:?}", witness.verification);
        };
        let counterexample: serde_json::Value =
            serde_json::from_str(&witness.counterexample_json).expect("witness payload is JSON");
        assert_eq!(
            counterexample.get("source").and_then(serde_json::Value::as_str),
            Some("direct-smt-bounded-unroll-error-derivation"),
        );
        assert_eq!(counterexample.get("unroll_k").and_then(serde_json::Value::as_u64), Some(k));
        let model = counterexample.get("witness_model").expect("witness model present").clone();
        (witness, k, model)
    }

    /// The u8 shift-reduction loop (`t += x << 4` over `[_; 64]`-shaped
    /// iteration) genuinely overflows for some inputs; the lane must refute it
    /// with a machine-checked witness whose input CONCRETELY overflows when the
    /// fixture semantics are executed (the ground-truth oracle: execution, not
    /// solver output).
    #[test]
    #[cfg(feature = "ay-chc-native")]
    fn bounded_unroll_lane_refutes_u8_shift_reduction_overflow() {
        let obligation =
            loop_accumulator_obligation(trust_ir::ty::Ty::U8, 64, LoopAddend::ShiftedParam);
        let verification =
            run_bounded_unroll_lane(&obligation, &bounded_unroll::BOUNDED_UNROLL_K_LADDER)
                .expect("u8 shift-reduction overflow must refute inside the ladder");
        assert!(
            matches!(verification.verdict, trust_mc_core::FullVerificationVerdict::Failed { .. }),
            "refutation carries a Failed verdict: {:?}",
            verification.verdict
        );
        let (witness, k, model) = unpack_bounded_unroll_refutation(&verification);

        let replay = independently_replay_typed_chc_pdr_refutation_witness(
            &obligation,
            trust_mc_core::ChcPdrEngine::Pdr,
            witness,
        )
        .expect("consumer must independently rebuild and replay the bounded unroll");
        assert!(replay.contains(&format!("k={k}")), "{replay}");

        // Digest binding: the witness binds the ORIGINAL problem's normalized
        // input, which the consumer recomputes from its own retained request.
        let expected = normalized_typed_chc_pdr_input(&obligation).expect("normalizes");
        assert_eq!(witness.encoded_formula_sha256, expected.normalized_input_hash.value);
        assert!(witness.concreteness.is_exact_with_zero_counts());

        // Concrete replay (ground-truth oracle): the witness model constrains
        // the input `x` so the violated add is reachable within k back edges;
        // executing the mirrored Rust semantics at a model input must really
        // overflow within k+1 body executions. `x` is among the model's u8
        // values, so the existential scan below is guaranteed to include it —
        // and any hit is itself a real overflowing input drawn from the model.
        let mut candidates = Vec::new();
        collect_bitvec_model_values(&model, 8, &mut candidates);
        assert!(!candidates.is_empty(), "witness model carries u8 assignments: {model}");
        let earliest = candidates
            .iter()
            .filter_map(|&value| {
                u8::try_from(value).ok().and_then(u8_shift_reduction_overflow_iteration)
            })
            .min();
        let earliest = earliest.expect(
            "at least one u8 value in the witness model must concretely overflow the mirrored \
             fixture semantics — a witness that does not replay is a lane bug",
        );
        assert!(
            earliest <= usize::try_from(k).expect("production bounded-unroll k fits usize") + 1,
            "the concrete overflow (iteration {earliest}) must be reachable within the \
             unroll budget k={k}"
        );
    }

    /// The bounded proof class, budget and exact rebuilt path are authority
    /// inputs rather than labels. Consumer replay must reject any mutation.
    #[test]
    #[cfg(feature = "ay-chc-native")]
    fn independent_bounded_unroll_refutation_replay_rejects_mutations() {
        let obligation =
            loop_accumulator_obligation(trust_ir::ty::Ty::U8, 64, LoopAddend::ShiftedParam);
        let verification =
            run_bounded_unroll_lane(&obligation, &bounded_unroll::BOUNDED_UNROLL_K_LADDER)
                .expect("fixture refutes");
        let (witness, k, _) = unpack_bounded_unroll_refutation(&verification);
        let original = witness.clone();
        independently_replay_typed_chc_pdr_refutation_witness(
            &obligation,
            trust_mc_core::ChcPdrEngine::Pdr,
            &original,
        )
        .expect("unmodified bounded witness replays");

        let rejects = |label: &str, mutated: &trust_mc_core::ChcPdrRefutationWitness| {
            assert!(
                independently_replay_typed_chc_pdr_refutation_witness(
                    &obligation,
                    trust_mc_core::ChcPdrEngine::Pdr,
                    mutated,
                )
                .is_err(),
                "{label} mutation must fail closed"
            );
        };

        let mut mutated = original.clone();
        mutated.verification = trust_mc_core::ChcPdrCexVerification::DirectSmtModel;
        rejects("proof class", &mutated);

        let mut mutated = original.clone();
        mutated.verification =
            trust_mc_core::ChcPdrCexVerification::BoundedUnrollDirectSmtModel { k: 2 };
        let mut payload: serde_json::Value =
            serde_json::from_str(&mutated.counterexample_json).expect("fixture payload");
        payload["unroll_k"] = serde_json::json!(2);
        mutated.counterexample_json = payload.to_string();
        rejects("out-of-ladder budget", &mutated);

        let mut mutated = original.clone();
        mutated.verification =
            trust_mc_core::ChcPdrCexVerification::BoundedUnrollDirectSmtModel { k };
        let mut payload: serde_json::Value =
            serde_json::from_str(&mutated.counterexample_json).expect("fixture payload");
        payload["unroll_k"] = serde_json::json!(if k == 4 { 16 } else { 4 });
        mutated.counterexample_json = payload.to_string();
        rejects("payload/class budget", &mutated);

        let mut mutated = original.clone();
        let mut payload: serde_json::Value =
            serde_json::from_str(&mutated.counterexample_json).expect("fixture payload");
        let trace = payload["derivation_clause_indices"].as_array_mut().expect("trace array");
        let repeated = trace.first().expect("nonempty trace").clone();
        trace.push(repeated);
        mutated.counterexample_json = payload.to_string();
        rejects("transition trace", &mutated);

        let mut mutated = original;
        let mut payload: serde_json::Value =
            serde_json::from_str(&mutated.counterexample_json).expect("fixture payload");
        let model = payload["witness_model"].as_object_mut().expect("model object");
        let removed = model.keys().next().cloned().expect("nonempty model");
        model.remove(&removed);
        mutated.counterexample_json = payload.to_string();
        rejects("partial model", &mutated);
    }

    /// The i128 reduction (`t += x` over `[i128; 4]`) genuinely overflows for
    /// large elements; the lane must refute it and the witness input must
    /// concretely overflow under the mirrored semantics.
    #[test]
    #[cfg(feature = "ay-chc-native")]
    fn bounded_unroll_lane_refutes_i128_accumulator_overflow() {
        let obligation = loop_accumulator_obligation(trust_ir::ty::Ty::I128, 4, LoopAddend::Param);
        let verification =
            run_bounded_unroll_lane(&obligation, &bounded_unroll::BOUNDED_UNROLL_K_LADDER)
                .expect("i128 accumulator overflow must refute inside the ladder");
        let (witness, k, model) = unpack_bounded_unroll_refutation(&verification);

        let expected = normalized_typed_chc_pdr_input(&obligation).expect("normalizes");
        assert_eq!(witness.encoded_formula_sha256, expected.normalized_input_hash.value);
        assert!(witness.concreteness.is_exact_with_zero_counts());

        let mut candidates = Vec::new();
        collect_bitvec_model_values(&model, 128, &mut candidates);
        assert!(!candidates.is_empty(), "witness model carries i128 assignments: {model}");
        let earliest = candidates
            .iter()
            .filter_map(|&value| {
                // Reinterpret the unsigned model value as two's-complement i128.
                i128_accumulator_overflow_iteration(value as i128)
            })
            .min()
            .expect(
                "at least one i128 value in the witness model must concretely overflow the \
                 mirrored fixture semantics",
            );
        assert!(
            earliest <= usize::try_from(k).expect("production bounded-unroll k fits usize") + 1
        );
    }

    /// A safe bounded loop (`u64 t += 1` over 10 iterations, no reachable
    /// overflow) must NOT be refuted — and this lane can never prove it either
    /// (its return type has no Proved arm); the safe proof must keep coming
    /// from the structural/PDR lanes.
    #[test]
    #[cfg(feature = "ay-chc-native")]
    fn bounded_unroll_lane_never_refutes_a_safe_loop() {
        let obligation =
            loop_accumulator_obligation(trust_ir::ty::Ty::U64, 10, LoopAddend::Const(1));
        assert!(
            run_bounded_unroll_lane(&obligation, &bounded_unroll::BOUNDED_UNROLL_K_LADDER)
                .is_none(),
            "a safe loop must yield no refutation at any rung"
        );
    }

    /// A violation reachable only BEYOND every ladder rung must stay Unknown
    /// (honest incompleteness): the under-approximation never over-claims in
    /// either direction. `u8 t += 64` first overflows on the 4th add (3 back
    /// edges), which a k=2 ladder cannot reach.
    #[test]
    #[cfg(feature = "ay-chc-native")]
    fn bounded_unroll_lane_stays_unknown_beyond_its_budget() {
        let obligation =
            loop_accumulator_obligation(trust_ir::ty::Ty::U8, 64, LoopAddend::Const(64));
        assert!(
            run_bounded_unroll_lane(&obligation, &[2]).is_none(),
            "a violation deeper than every rung must not be refuted"
        );
        // The same violation IS caught once the ladder covers its depth,
        // pinning that the miss above is a budget property, not a lane bug.
        let verification =
            run_bounded_unroll_lane(&obligation, &[4]).expect("depth-4 violation refutes at k=4");
        let (_, k, _) = unpack_bounded_unroll_refutation(&verification);
        assert_eq!(k, 4);
        // And the production ladder covers the gate fixtures' depths (u8
        // shift-reduction needs 15 back edges, [u8; 64] full trips need 63).
        assert_eq!(bounded_unroll::BOUNDED_UNROLL_K_LADDER.last(), Some(&64));
    }

    /// Non-L0 obligation kinds (invariants, protocols) are outside this lane.
    #[test]
    #[cfg(feature = "ay-chc-native")]
    fn bounded_unroll_lane_declines_non_assertion_kinds() {
        let mut obligation =
            loop_accumulator_obligation(trust_ir::ty::Ty::U8, 64, LoopAddend::ShiftedParam);
        obligation.kind = trust_mc_core::MirObligationKind::Invariant;
        assert!(
            run_bounded_unroll_lane(&obligation, &bounded_unroll::BOUNDED_UNROLL_K_LADDER)
                .is_none(),
            "the lane is L0-only"
        );
    }

    /// A nonzero fail-closed-lowering-site count poisons any derivation (it may
    /// route through an admission-failure error rule), so the lane declines
    /// before solving — same gate as the direct and PDR refutation arms.
    #[test]
    #[cfg(feature = "ay-chc-native")]
    fn bounded_unroll_lane_declines_fail_closed_lowering_sites() {
        let mut obligation =
            loop_accumulator_obligation(trust_ir::ty::Ty::U8, 64, LoopAddend::ShiftedParam);
        obligation.native_metadata = Some(
            trust_mc_core::NativeTypedChcObligationMetadata::new(
                "tRust",
                "trust_ir-module",
                None,
                trust_mc_core::NativeArtifactDigest::new("sha256", "00".repeat(32)),
                trust_mc_core::NativeArtifactDigest::new("sha256", "11".repeat(32)),
                0,
                "chc",
                0,
                vec![],
                vec![],
            )
            // Keep the eligibility marker so the decline is attributable to
            // the fail-closed count alone.
            .with_structural_reachability_complete(true)
            .with_fail_closed_lowering_site_count(1),
        );
        assert!(
            run_bounded_unroll_lane(&obligation, &bounded_unroll::BOUNDED_UNROLL_K_LADDER)
                .is_none(),
            "fail-closed lowering sites must suppress the refutation"
        );
    }

    /// Helper: metadata carrying a fail-closed count and (optionally) the
    /// distinct construct labels behind it.
    fn fail_closed_metadata(
        sites: u32,
        reasons: &[&str],
    ) -> trust_mc_core::NativeTypedChcObligationMetadata {
        trust_mc_core::NativeTypedChcObligationMetadata::new(
            "tRust",
            "trust_ir-module",
            None,
            trust_mc_core::NativeArtifactDigest::new("sha256", "00".repeat(32)),
            trust_mc_core::NativeArtifactDigest::new("sha256", "11".repeat(32)),
            0,
            "chc",
            0,
            vec![],
            vec![],
        )
        .with_structural_reachability_complete(true)
        .with_fail_closed_lowering_site_count(sites)
        .with_fail_closed_lowering_reasons(reasons.iter().map(|r| (*r).to_string()))
    }

    /// DIAGNOSTIC SURFACING. The demotion message named a COUNT and nothing
    /// else, so a "3 unsupported trust_ir construct(s)" obligation gave no way
    /// to learn WHICH constructs blocked it. The distinct reasons must now
    /// appear in the text, sorted and deduplicated.
    ///
    /// FAILS ON UNFIXED CODE: with the reason list dropped on the floor
    /// (`let _ = reasons;`), the message carries no `(constructs: …)` clause.
    #[test]
    fn demotion_reason_names_the_distinct_blocking_constructs() {
        let message = fail_closed_lowering_demotion_reason(
            3,
            &[String::from("Cast"), String::from("HeapAllocation"), String::from("IndirectCall")],
        );
        assert!(
            message.contains("3 unsupported trust_ir construct(s)"),
            "the count must survive verbatim: {message}"
        );
        assert!(
            message.contains("(constructs: Cast, HeapAllocation, IndirectCall)"),
            "the distinct reasons must be named: {message}"
        );
    }

    /// BACKWARD COMPATIBILITY. Absent metadata (and metadata predating the
    /// field) reads as an EMPTY reason list, and the message must then render
    /// byte-identically to the historical text — no dangling "(constructs: )".
    #[test]
    fn demotion_reason_without_reasons_is_byte_identical_to_the_historical_text() {
        let historical = "fail-closed lowering reachable: 2 unsupported trust_ir construct(s) \
                          lowered to unconditional error rules; refutation demoted to unknown";
        assert_eq!(fail_closed_lowering_demotion_reason(2, &[]), historical);

        // An obligation with no native metadata at all resolves to the same
        // empty slice (this is the "absent reads as nothing" contract).
        let mut obligation = typed_native_chc_obligation(/* structurally_complete */ false);
        obligation.native_metadata = None;
        assert!(fail_closed_lowering_reasons(&obligation).is_empty());
        assert_eq!(fail_closed_lowering_sites(&obligation), 0);
    }

    /// CANONICAL FORM. The metadata is serialized into hashed artifact bytes,
    /// so the recorded list must not depend on the order the translator emitted
    /// its diagnostics in. The builder sorts and dedups; two permutations of the
    /// same multiset must produce byte-identical metadata.
    #[test]
    fn recorded_reasons_are_sorted_deduplicated_and_order_independent() {
        let a = fail_closed_metadata(4, &["IndirectCall", "Cast", "IndirectCall", "Cast"]);
        let b = fail_closed_metadata(4, &["Cast", "IndirectCall", "Cast", "IndirectCall"]);
        assert_eq!(a.fail_closed_lowering_reasons, vec!["Cast", "IndirectCall"]);
        assert_eq!(a, b, "permuted diagnostics must yield identical metadata");
        assert_eq!(
            serde_json::to_string(&a).expect("serialize"),
            serde_json::to_string(&b).expect("serialize"),
        );
    }

    /// ZERO VERDICT EFFECT (the whole point of this being diagnostic-only).
    /// The COUNT is the only load-bearing value: a zero count with a fully
    /// populated reason list must NOT demote anything, and a nonzero count must
    /// demote with or without reasons. Nothing in the driver may branch on the
    /// reason list.
    ///
    /// This one is a NEGATIVE property — it passes before and after the change
    /// by design. Its teeth were checked by mutating the gate to read the reason
    /// list (`!reasons.is_empty()` in place of `sites > 0`), which makes the
    /// first assertion fail.
    #[test]
    #[cfg(feature = "ay-chc-native")]
    fn reason_labels_alone_never_demote_and_never_alter_the_gate() {
        let mut obligation =
            loop_accumulator_obligation(trust_ir::ty::Ty::U8, 64, LoopAddend::ShiftedParam);

        // (a) Reasons present, count ZERO — the lane must still run: a reason
        //     label carries no demotion power of its own.
        obligation.native_metadata =
            Some(fail_closed_metadata(0, &["Cast", "IndirectCall", "HeapAllocation"]));
        assert_eq!(fail_closed_lowering_sites(&obligation), 0);
        assert_eq!(fail_closed_lowering_reasons(&obligation).len(), 3);
        assert!(
            run_bounded_unroll_lane(&obligation, &bounded_unroll::BOUNDED_UNROLL_K_LADDER)
                .is_some(),
            "a zero count must not be demoted by the presence of reason labels"
        );

        // (b) Count nonzero, reasons EMPTY — still demoted (the count alone
        //     governs, exactly as before the field existed).
        obligation.native_metadata = Some(fail_closed_metadata(1, &[]));
        assert!(
            run_bounded_unroll_lane(&obligation, &bounded_unroll::BOUNDED_UNROLL_K_LADDER)
                .is_none(),
            "the count alone must still suppress the refutation"
        );

        // (c) Count nonzero, reasons present — demoted, and the message names
        //     them.
        obligation.native_metadata = Some(fail_closed_metadata(1, &["Switch"]));
        assert!(
            run_bounded_unroll_lane(&obligation, &bounded_unroll::BOUNDED_UNROLL_K_LADDER)
                .is_none(),
        );
        assert!(
            fail_closed_lowering_demotion_reason(
                fail_closed_lowering_sites(&obligation),
                fail_closed_lowering_reasons(&obligation),
            )
            .contains("(constructs: Switch)")
        );
    }

    /// Obligations that do not carry the native-bundle translator's
    /// complete-by-construction marker are outside the lane's modeled domain —
    /// notably the compiler's control-only whole-CFG default-admission CHC
    /// (nullary relations, no data constraints), whose "derivations" are mere
    /// control-feasibility and must never be surfaced as refutations.
    #[test]
    #[cfg(feature = "ay-chc-native")]
    fn bounded_unroll_lane_declines_without_completeness_marker() {
        let mut obligation =
            loop_accumulator_obligation(trust_ir::ty::Ty::U8, 64, LoopAddend::ShiftedParam);
        // (a) no native metadata at all.
        obligation.native_metadata = None;
        assert!(
            run_bounded_unroll_lane(&obligation, &bounded_unroll::BOUNDED_UNROLL_K_LADDER)
                .is_none(),
            "metadata-free obligations are outside the lane"
        );
        // (b) metadata present but the completeness claim absent.
        obligation.native_metadata = Some(trust_mc_core::NativeTypedChcObligationMetadata::new(
            "tRust",
            "trust_ir-module",
            None,
            trust_mc_core::NativeArtifactDigest::new("sha256", "00".repeat(32)),
            trust_mc_core::NativeArtifactDigest::new("sha256", "11".repeat(32)),
            0,
            "chc",
            0,
            vec![],
            vec![],
        ));
        assert!(
            run_bounded_unroll_lane(&obligation, &bounded_unroll::BOUNDED_UNROLL_K_LADDER)
                .is_none(),
            "an unclaimed encoding must not enter the refutation lane"
        );
    }

    /// End-to-end over the native bundle boundary: the loop-overflow request
    /// lands in the new `refuted` channel as a witnessed refutation (never in
    /// `obligations`, which is proof authority), and the witness digest matches
    /// a consumer-style fresh recomputation.
    #[test]
    #[cfg(all(feature = "ay-chc-native", feature = "native-trust-ir-bundle"))]
    fn native_bundle_delivers_witnessed_loop_refutation_on_refuted_channel() {
        let bundle = loop_overflow_trust_ir_bundle();
        let runner = NativeTrustIrChcPdrRunner::with_solve_options(
            trust_mc_core::ChcPdrSolveOptions::default()
                .with_engine(trust_mc_core::ChcPdrEngine::Pdr)
                .with_timeout(Duration::from_secs(8)),
        );
        let evidence =
            runner.solve_bundle_native_proof_grade(&bundle).expect("bundle solve completes");
        assert!(
            evidence.obligations.is_empty(),
            "a genuinely refutable obligation must never surface as proof authority"
        );
        assert_eq!(
            evidence.refuted.len(),
            1,
            "the witnessed refutation rides the refuted channel (not_proved: {:?})",
            evidence
                .not_proved
                .iter()
                .map(|row| (&row.translated.obligation.obligation_id, &row.reason))
                .collect::<Vec<_>>()
        );
        let row = &evidence.refuted[0];
        let trust_mc_core::ChcPdrSolveStatus::Refuted { witness: Some(witness) } =
            &row.verification.outcome.status
        else {
            panic!("refuted row carries the witness: {:?}", row.verification.outcome);
        };
        // Consumer-style independent recomputation of the encoded-formula
        // digest from the (freshly translated) typed obligation.
        let expected = normalized_typed_chc_pdr_input(&row.translated.obligation)
            .expect("translated obligation normalizes");
        assert_eq!(witness.encoded_formula_sha256, expected.normalized_input_hash.value);
        assert!(witness.concreteness.is_exact_with_zero_counts());
        // Only the bounded-unroll lane's witnesses ride the refuted channel
        // (see the diversion's SCOPE note): its mint is grounding-gated, so a
        // row on this channel always carries the bounded-unroll kind.
        assert!(
            matches!(
                witness.verification,
                trust_mc_core::ChcPdrCexVerification::BoundedUnrollDirectSmtModel { .. }
            ),
            "unexpected witness kind on the refuted channel: {:?}",
            witness.verification
        );
    }

    /// Compiler-style native bundle around the u8 shift-reduction loop mirror.
    #[cfg(all(feature = "ay-chc-native", feature = "native-trust-ir-bundle"))]
    fn loop_overflow_trust_ir_bundle() -> trust_ir::NativeVerificationBundle {
        use trust_ir::inst::{BinOp, ICmpOp};
        use trust_ir::ty::Ty;
        use trust_ir::{
            NativeAdapterInput, NativeAssertionId, NativeBundleProducer, NativeCompilerFactRef,
            NativeCompilerFacts, NativeMonomorphizationFact, NativeMonomorphizationId,
            NativeObligationCause, NativeObligationSource, NativeReplayAtom, NativeReplayAtomId,
            NativeReplayContext, NativeRequestId, NativeRequestProvenance, NativeToolIdentity,
            NativeVerificationBundle, NativeVerificationRequest, ObligationKind, ProofDigest,
            ProofFormula, ProofId, ProofLineageId, ProofLineageManifest, ProofLineageNode,
            ProofObligation, ProofReplayIdentity, ProofStatus, ProofTransform, ProofTransformStage,
            TrustMcNativeRequest, TrustMcVerificationMode,
        };
        use trust_ir_build::ModuleBuilder;

        let source_digest = ProofDigest::sha256([0x71; 32]);
        let trust_ir_module_digest = ProofDigest::sha256([0x72; 32]);

        let mut mb = ModuleBuilder::new("native_trust_ir_loop_overflow_bundle");
        let ft = mb.add_func_type(vec![Ty::U8], vec![Ty::U8]);
        {
            let mut fb = mb.function("shift_reduction_loop", ft);
            let entry = fb.create_block();
            let header = fb.create_block();
            let body = fb.create_block();
            let exit = fb.create_block();

            fb.switch_to_block(entry);
            fb.set_entry(entry);
            let x = fb.add_block_param(entry, Ty::U8);
            let four = fb.iconst(Ty::U8, 4);
            let addend = fb.binop(BinOp::Shl, Ty::U8, x, four);
            let zero_i = fb.iconst(Ty::U64, 0);
            let zero_t = fb.iconst(Ty::U8, 0);
            fb.br(header, vec![zero_i, zero_t]);

            // Explicit block-argument threading — see loop_accumulator_obligation.
            let i = fb.add_block_param(header, Ty::U64);
            let t = fb.add_block_param(header, Ty::U8);
            fb.switch_to_block(header);
            let bound = fb.iconst(Ty::U64, 64);
            let in_loop = fb.icmp(ICmpOp::Ult, Ty::U64, i, bound);
            fb.condbr(in_loop, body, vec![i, t], exit, vec![t]);

            let i_body = fb.add_block_param(body, Ty::U64);
            let t_body = fb.add_block_param(body, Ty::U8);
            fb.switch_to_block(body);
            let t_next = fb.add(Ty::U8, t_body, addend);
            let one = fb.iconst(Ty::U64, 1);
            let i_next = fb.add(Ty::U64, i_body, one);
            fb.br(header, vec![i_next, t_next]);

            let t_exit = fb.add_block_param(exit, Ty::U8);
            fb.switch_to_block(exit);
            fb.ret(vec![t_exit]);
            fb.build();
        }

        let mut module = mb.build();
        let trust_mc_function = module
            .functions
            .iter()
            .find(|func| func.name == "shift_reduction_loop")
            .expect("fixture includes requested trust-mc function")
            .id;
        module.proof_obligations.push(
            ProofObligation::new(
                ProofId::new(0),
                ObligationKind::PanicFreedom,
                ProofStatus::Pending,
                "loop-carried accumulator add does not overflow",
            )
            .with_formula(ProofFormula::smtlib2("shift_reduction_loop_safe", "Bool"))
            .with_function(trust_mc_function)
            .with_source(native_test_obligation_source(
                "rust:native_trust_ir_loop_overflow_bundle::shift_reduction_loop",
                "vc:trust-mc-driver:loop-overflow:0",
                b"shift_reduction_loop_safe",
            )),
        );

        let mut lineage_node = ProofLineageNode::new(
            ProofLineageId::new(0),
            ProofTransform::new(
                ProofTransformStage::Frontend,
                "rustc-mir-to-trust_ir",
                "tRust",
                "native-request-schema-v1",
            ),
            source_digest,
            trust_ir_module_digest,
        );
        lineage_node.obligations.push(ProofId::new(0));

        let lineage = ProofLineageManifest {
            schema_version: ProofLineageManifest::SCHEMA_VERSION,
            nodes: vec![lineage_node],
            roots: vec![ProofLineageId::new(0)],
        };

        let mut bundle = NativeVerificationBundle::new(
            NativeBundleProducer::TRust,
            NativeAdapterInput::RustMir { body_digest: source_digest },
            trust_ir_module_digest,
            module,
            lineage,
        );
        let source_span = trust_ir::SourceSpan { file: 0, line: 21, col: 9 };
        bundle.compiler_facts = NativeCompilerFacts {
            monomorphizations: vec![NativeMonomorphizationFact {
                id: NativeMonomorphizationId::new(0),
                source_item: "native_trust_ir_loop_overflow_bundle::shift_reduction_loop"
                    .to_owned(),
                symbol: "_RNvNtC6native20shift_reduction_loop".to_owned(),
                generic_args: Vec::new(),
                function: Some(trust_mc_function),
                stable_digest: ProofDigest::sha256([0x73; 32]),
            }],
            obligation_sources: vec![NativeObligationSource {
                obligation: ProofId::new(0),
                public_obligation_id: "vc:trust-mc-driver:loop-overflow:0".to_string(),
                function: Some(trust_mc_function),
                span: Some(source_span),
                assertion_id: Some(NativeAssertionId::new(0)),
                cause: NativeObligationCause::OverflowCheck,
                monomorphization: Some(NativeMonomorphizationId::new(0)),
                facts: vec![NativeCompilerFactRef::Monomorphization(
                    NativeMonomorphizationId::new(0),
                )],
            }],
            ..NativeCompilerFacts::default()
        };
        bundle.requests.push(NativeVerificationRequest::TrustMc(TrustMcNativeRequest {
            id: NativeRequestId::new(9),
            mode: TrustMcVerificationMode::Chc,
            function: trust_mc_function,
            obligations: vec![ProofId::new(0)],
            lineage_roots: vec![ProofLineageId::new(0)],
            options: {
                let mut options = trust_ir::TrustMcRequestOptions::default();
                options.chc.emit_horn_clauses = true;
                options
            },
            diagnostics: Default::default(),
            provenance: NativeRequestProvenance::trust_mc(
                NativeToolIdentity::new("trust-mc").with_version("chc-v1"),
            )
            .with_solver(NativeToolIdentity::new("ay-chc").with_version("native-v1"))
            .with_replay(
                ProofReplayIdentity::new("trust-mc", "trust_mc native typed CHC/PDR test replay")
                    .with_transcript_digest(ProofDigest::sha256([0x74; 32])),
            )
            .with_replay_context(
                NativeReplayContext::default().with_atom(
                    NativeReplayAtom::assertion(
                        NativeReplayAtomId::new(0),
                        ProofFormula::smtlib2("shift_reduction_loop_safe", "Bool"),
                    )
                    .with_obligation(ProofId::new(0))
                    .with_assertion_id(NativeAssertionId::new(0))
                    .with_span(source_span),
                ),
            ),
        }));
        refresh_native_test_bundle_module_identity(&mut bundle);
        bundle
    }
}
