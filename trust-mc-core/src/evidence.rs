// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Library-facing evidence types for MIR-derived CHC/PDR verification.
//!
//! This module is deliberately fail-closed: only MIR-derived CHC/PDR evidence
//! with canonical input, solver transcript, replay log, and checked proof
//! report digests classifies as proof-grade. BMC-shaped diagnostics and router
//! placeholders remain non-proving evidence.

use std::collections::BTreeSet;

use serde::de::{Error as _, SeqAccess, Visitor};
use serde::{Deserialize, Deserializer, Serialize};
use sha2::{Digest, Sha256};
use thiserror::Error;

const SHA256_HEX_LEN: usize = 64;
const PRODUCER: &str = "trust_mc-core";

/// Public PDR candidates remain non-authoritative until a private consumer
/// freshly replays the exact invariant against its own compiler-derived CHCs.
pub const PDR_INVARIANT_FRESH_CONSUMER_REPLAY_REQUIRED: &str =
    "PDR invariant candidates require fresh private consumer replay before proof-grade admission";

/// Public CHC-validity candidates remain non-authoritative until an exact
/// in-process derivation or a fresh private consumer replay grants authority.
pub const CHC_VALIDITY_FRESH_CONSUMER_REPLAY_REQUIRED: &str =
    "CHC validity candidates require fresh private consumer replay before proof-grade admission";

/// Maximum exact byte payload retained in one verification artifact.
///
/// Proof transports serialize these bytes, so the bound is enforced while
/// deserializing rather than after an unbounded allocation has already taken
/// place. Oversized diagnostic artifacts may still be represented by their
/// legacy digest/length descriptor, but cannot become proof-grade evidence.
pub const MAX_FULL_VERIFICATION_ARTIFACT_MATERIALIZATION_BYTES: usize = 16 * 1024 * 1024;
const MAX_LINKED_ARTIFACT_REFERENCES: usize = 8;
const MAX_PROOF_EVIDENCE_HASHES: usize = 8;
const MAX_PROOF_EVIDENCE_ARTIFACTS: usize = 16;
const MAX_MANIFEST_ARTIFACTS: usize = 64;

/// Stable SHA-256 evidence digest descriptor.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize)]
pub struct EvidenceHash {
    /// Hash algorithm. Currently always `sha256`.
    pub algorithm: String,
    /// Lowercase hexadecimal digest.
    pub value: String,
}

#[derive(Deserialize)]
struct EvidenceHashWire {
    #[serde(deserialize_with = "deserialize_sha256_algorithm")]
    algorithm: String,
    #[serde(deserialize_with = "deserialize_canonical_sha256_hex")]
    value: String,
}

impl<'de> Deserialize<'de> for EvidenceHash {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let wire = EvidenceHashWire::deserialize(deserializer)?;
        Ok(Self { algorithm: wire.algorithm, value: wire.value })
    }
}

fn deserialize_sha256_algorithm<'de, D>(deserializer: D) -> Result<String, D::Error>
where
    D: Deserializer<'de>,
{
    struct Sha256AlgorithmVisitor;

    impl Visitor<'_> for Sha256AlgorithmVisitor {
        type Value = String;

        fn expecting(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            formatter.write_str("the exact digest algorithm `sha256`")
        }

        fn visit_str<E>(self, value: &str) -> Result<Self::Value, E>
        where
            E: serde::de::Error,
        {
            if value != "sha256" {
                return Err(E::custom("evidence digest algorithm must be exactly `sha256`"));
            }
            Ok("sha256".to_string())
        }

        fn visit_string<E>(self, value: String) -> Result<Self::Value, E>
        where
            E: serde::de::Error,
        {
            self.visit_str(&value)
        }
    }

    deserializer.deserialize_str(Sha256AlgorithmVisitor)
}

fn deserialize_canonical_sha256_hex<'de, D>(deserializer: D) -> Result<String, D::Error>
where
    D: Deserializer<'de>,
{
    struct CanonicalSha256HexVisitor;

    impl Visitor<'_> for CanonicalSha256HexVisitor {
        type Value = String;

        fn expecting(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(formatter, "exactly {SHA256_HEX_LEN} lowercase hexadecimal characters")
        }

        fn visit_str<E>(self, value: &str) -> Result<Self::Value, E>
        where
            E: serde::de::Error,
        {
            if !is_canonical_sha256_hex(value) {
                return Err(E::custom(
                    "evidence digest must be exactly 64 lowercase hexadecimal characters",
                ));
            }
            Ok(value.to_string())
        }

        fn visit_string<E>(self, value: String) -> Result<Self::Value, E>
        where
            E: serde::de::Error,
        {
            self.visit_str(&value)
        }
    }

    deserializer.deserialize_str(CanonicalSha256HexVisitor)
}

fn is_canonical_sha256_hex(value: &str) -> bool {
    value.len() == SHA256_HEX_LEN
        && value.bytes().all(|byte| byte.is_ascii_hexdigit() && !byte.is_ascii_uppercase())
}

impl EvidenceHash {
    /// Hash bytes with SHA-256.
    #[must_use]
    pub fn sha256_bytes(bytes: &[u8]) -> Self {
        let digest = Sha256::digest(bytes);
        Self { algorithm: "sha256".to_string(), value: format!("{digest:x}") }
    }

    /// Build a validated canonical SHA-256 descriptor from hex.
    pub fn sha256_hex(hex: impl Into<String>) -> Result<Self, EvidenceHashError> {
        let value = hex.into().to_ascii_lowercase();
        if value.len() != SHA256_HEX_LEN {
            return Err(EvidenceHashError::InvalidLength {
                expected: SHA256_HEX_LEN,
                actual: value.len(),
            });
        }
        if !value.bytes().all(|byte| byte.is_ascii_hexdigit()) {
            return Err(EvidenceHashError::InvalidHex);
        }
        Ok(Self { algorithm: "sha256".to_string(), value })
    }

    #[must_use]
    fn is_canonical_sha256(&self) -> bool {
        self.algorithm == "sha256" && is_canonical_sha256_hex(&self.value)
    }
}

/// Invalid SHA-256 evidence digest metadata.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Error)]
pub enum EvidenceHashError {
    #[error("invalid SHA-256 evidence hash length: expected {expected}, got {actual}")]
    InvalidLength { expected: usize, actual: usize },
    #[error("invalid SHA-256 evidence hash: digest must be hexadecimal")]
    InvalidHex,
}

/// MIR-derived obligation kind carried at the library boundary.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum MirObligationKind {
    Assertion,
    ArithmeticSafety,
    Invariant,
    LoopInvariant,
    Termination,
    UnreachableCode,
    Protocol,
}

/// Where the obligation came from.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ObligationOrigin {
    /// Real MIR-derived obligation.
    MirDerived,
    /// Router placeholder or compatibility shim; never proof-grade.
    RouterPlaceholder,
}

/// Digest descriptor for typed native verification artifacts.
///
/// Unlike [`EvidenceHash`], this can describe non-cryptographic stable trust_ir
/// digests carried by `NativeVerificationBundle` lineage metadata.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct NativeArtifactDigest {
    pub algorithm: String,
    pub value: String,
}

impl NativeArtifactDigest {
    /// Build a digest descriptor from an explicit algorithm and lowercase
    /// hexadecimal value.
    #[must_use]
    pub fn new(algorithm: impl Into<String>, value: impl Into<String>) -> Self {
        Self { algorithm: algorithm.into(), value: value.into() }
    }
}

/// Typed compiler-fact family carried by trust_ir native verification bundles.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum NativeCompilerFactKind {
    AdtLayout,
    FatPointer,
    TraitObjectMetadata,
    PointerOffset,
    Cast,
    Monomorphization,
}

/// Durable reference to one typed compiler fact from a trust_ir native bundle.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct NativeCompilerFactReference {
    pub kind: NativeCompilerFactKind,
    pub id: u32,
}

impl NativeCompilerFactReference {
    #[must_use]
    pub const fn new(kind: NativeCompilerFactKind, id: u32) -> Self {
        Self { kind, id }
    }
}

/// Counts of typed compiler facts present in the source native bundle.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct NativeCompilerFactCounts {
    pub adt_layouts: usize,
    pub fat_pointers: usize,
    pub trait_object_metadata: usize,
    pub pointer_offsets: usize,
    pub casts: usize,
    pub monomorphizations: usize,
    pub obligation_sources: usize,
}

impl NativeCompilerFactCounts {
    #[must_use]
    pub const fn count_for(self, kind: NativeCompilerFactKind) -> usize {
        match kind {
            NativeCompilerFactKind::AdtLayout => self.adt_layouts,
            NativeCompilerFactKind::FatPointer => self.fat_pointers,
            NativeCompilerFactKind::TraitObjectMetadata => self.trait_object_metadata,
            NativeCompilerFactKind::PointerOffset => self.pointer_offsets,
            NativeCompilerFactKind::Cast => self.casts,
            NativeCompilerFactKind::Monomorphization => self.monomorphizations,
        }
    }
}

/// Native source location copied from trust_ir obligation-source metadata.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct NativeSourceSpanMetadata {
    pub file: u32,
    pub line: u32,
    pub col: u32,
}

/// Typed reason a native compiler fact source produced an obligation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum NativeObligationCauseMetadata {
    Precondition,
    Postcondition,
    Assert,
    BoundsCheck,
    OverflowCheck,
    LayoutCheck,
    CastCheck,
    PointerOffset,
    BorrowCheck,
    Translation,
    Panic,
    Other,
}

/// Compiler-fact references responsible for one proof obligation.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct NativeObligationCompilerFacts {
    pub proof_obligation_id: u32,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub function_id: Option<u32>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub span: Option<NativeSourceSpanMetadata>,
    pub cause: NativeObligationCauseMetadata,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub monomorphization_id: Option<u32>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub fact_refs: Vec<NativeCompilerFactReference>,
}

/// Replay identity required by trust_ir native verifier requests.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct NativeReplayIdentityMetadata {
    pub engine: String,
    pub invocation: String,
    pub transcript_digest: NativeArtifactDigest,
}

/// Verifier role for one typed native replay atom.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum NativeReplayAtomKindMetadata {
    Assumption,
    Assertion,
}

/// Digest-backed typed replay atom metadata from a trust_ir native request.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct NativeReplayAtomMetadata {
    pub atom_id: u32,
    pub kind: NativeReplayAtomKindMetadata,
    pub formula_schema: String,
    pub payload_digest: NativeArtifactDigest,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub proof_obligation_id: Option<u32>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub assertion_id: Option<u32>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub span: Option<NativeSourceSpanMetadata>,
}

/// Fail-closed replay-context mode unsupported by the producer.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct NativeUnsupportedModeMetadata {
    pub reason: String,
    pub detail: String,
}

/// Typed replay context copied from trust_ir native request provenance.
#[derive(Debug, Clone, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct NativeReplayContextMetadata {
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub atoms: Vec<NativeReplayAtomMetadata>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub unsupported_modes: Vec<NativeUnsupportedModeMetadata>,
}

/// Durable typed metadata for a native trust_ir CHC/PDR obligation.
///
/// This records the `NativeVerificationBundle` request and proof-lineage
/// identity plus schema-v3 compiler-fact and replay references alongside the
/// typed CHC candidate so a private consumer can bind its independent
/// derivation/replay back to the original native bundle without parsing SMT-LIB
/// labels or diagnostic text. The public metadata itself grants no authority.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativeTypedChcObligationMetadata {
    pub schema_version: u32,
    pub producer: String,
    pub adapter_input: String,
    pub source_digest: Option<NativeArtifactDigest>,
    pub trust_ir_module_digest: NativeArtifactDigest,
    pub lineage_manifest_digest: NativeArtifactDigest,
    pub native_request_id: u32,
    pub verification_mode: String,
    pub function_id: u32,
    pub proof_obligation_ids: Vec<u32>,
    pub lineage_root_ids: Vec<u32>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub compiler_facts_digest: Option<NativeArtifactDigest>,
    #[serde(default)]
    pub compiler_fact_counts: NativeCompilerFactCounts,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub compiler_fact_sources: Vec<NativeObligationCompilerFacts>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub replay_identity: Option<NativeReplayIdentityMetadata>,
    #[serde(default)]
    pub replay_context: NativeReplayContextMetadata,
    /// Diagnostic producer claim that the submitted CHC came from a structurally
    /// complete translation.
    ///
    /// This public, serialized boolean is forgeable and grants no proof
    /// authority. Consumers must establish completeness at a private fresh
    /// translation boundary and must not use this field as a capability.
    #[serde(default)]
    pub structural_reachability_complete: bool,
    /// Number of fail-closed lowering sites in the submitted CHC — constructs
    /// the translator could not model precisely and lowered to an
    /// UNCONDITIONALLY REACHABLE error rule (`add_unsupported_error`).
    ///
    /// Forgeable and DEMOTE-ONLY: a nonzero count may only turn a Refuted
    /// verdict into Unknown (a SAT derivation through such a rule is an
    /// admission failure, not a program counterexample); it can never mint or
    /// strengthen proof authority, and a forged zero changes nothing (the
    /// refutation arms still carry their own havoc-freedom demotion).
    #[serde(default)]
    pub fail_closed_lowering_site_count: u32,
    /// The DISTINCT typed reasons behind `fail_closed_lowering_site_count`, as
    /// stable construct labels (`"Cast"`, `"IndirectCall"`, `"HeapAllocation"`,
    /// …) sorted and deduplicated by the producer.
    ///
    /// PURE DIAGNOSTIC, strictly weaker than the count it annotates. The count
    /// alone already says "N unsupported trust_ir construct(s)" and leaves no
    /// way to know WHICH — this makes the demotion message actionable without
    /// parsing SMT-LIB or re-running the translator. Read by exactly one
    /// consumer: the demotion-reason text formatter.
    ///
    /// Forgeable and DEMOTE-ONLY, on the same terms as the count: it is never
    /// compared, thresholded or matched, and NO verdict, gate or acceptance
    /// check reads it. Absent metadata reads as EMPTY (the message then renders
    /// exactly as before); an arbitrary or adversarial value can only alter
    /// human-readable text on a verdict that the count has ALREADY demoted to
    /// Unknown, so it can neither mint nor strengthen proof authority.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub fail_closed_lowering_reasons: Vec<String>,
}

impl NativeTypedChcObligationMetadata {
    pub const SCHEMA_VERSION: u32 = 3;

    /// Build native typed CHC metadata with the current schema version.
    #[must_use]
    pub fn new(
        producer: impl Into<String>,
        adapter_input: impl Into<String>,
        source_digest: Option<NativeArtifactDigest>,
        trust_ir_module_digest: NativeArtifactDigest,
        lineage_manifest_digest: NativeArtifactDigest,
        native_request_id: u32,
        verification_mode: impl Into<String>,
        function_id: u32,
        proof_obligation_ids: Vec<u32>,
        lineage_root_ids: Vec<u32>,
    ) -> Self {
        Self {
            schema_version: Self::SCHEMA_VERSION,
            producer: producer.into(),
            adapter_input: adapter_input.into(),
            source_digest,
            trust_ir_module_digest,
            lineage_manifest_digest,
            native_request_id,
            verification_mode: verification_mode.into(),
            function_id,
            proof_obligation_ids,
            lineage_root_ids,
            compiler_facts_digest: None,
            compiler_fact_counts: NativeCompilerFactCounts::default(),
            compiler_fact_sources: Vec::new(),
            replay_identity: None,
            replay_context: NativeReplayContextMetadata::default(),
            // Fail-closed default: only the complete-by-construction native
            // translator (`native_chc_metadata`) may certify this true.
            structural_reachability_complete: false,
            fail_closed_lowering_site_count: 0,
            fail_closed_lowering_reasons: Vec::new(),
        }
    }

    /// Set the diagnostic structural-completeness claim.
    ///
    /// This is transport metadata only. Setting it never grants authority, even
    /// when the caller is an in-tree producer.
    #[must_use]
    pub fn with_structural_reachability_complete(mut self, complete: bool) -> Self {
        self.structural_reachability_complete = complete;
        self
    }

    /// Record how many fail-closed lowering sites (unconditional error rules
    /// from unsupported constructs) the submitted CHC contains. Demote-only
    /// transport metadata; see the field documentation.
    #[must_use]
    pub fn with_fail_closed_lowering_site_count(mut self, count: u32) -> Self {
        self.fail_closed_lowering_site_count = count;
        self
    }

    /// Record the DISTINCT construct labels behind the fail-closed lowering
    /// count. Sorted + deduplicated here so the value is canonical regardless of
    /// the order the translator emitted its diagnostics in (the metadata is
    /// serialized into artifact bytes, so a non-canonical order would make an
    /// otherwise-identical obligation hash differently).
    ///
    /// Pure diagnostic; see the field documentation. Nothing reads it but the
    /// demotion-reason text formatter.
    #[must_use]
    pub fn with_fail_closed_lowering_reasons(
        mut self,
        reasons: impl IntoIterator<Item = String>,
    ) -> Self {
        let mut reasons: Vec<String> = reasons.into_iter().collect();
        reasons.sort_unstable();
        reasons.dedup();
        self.fail_closed_lowering_reasons = reasons;
        self
    }

    /// Attach schema-v3 native compiler-fact metadata to this obligation.
    #[must_use]
    pub fn with_compiler_facts(
        mut self,
        digest: NativeArtifactDigest,
        counts: NativeCompilerFactCounts,
        sources: Vec<NativeObligationCompilerFacts>,
    ) -> Self {
        self.compiler_facts_digest = Some(digest);
        self.compiler_fact_counts = counts;
        self.compiler_fact_sources = sources;
        self
    }

    /// Attach schema-v3 native replay provenance to this obligation.
    #[must_use]
    pub fn with_replay_metadata(
        mut self,
        identity: NativeReplayIdentityMetadata,
        context: NativeReplayContextMetadata,
    ) -> Self {
        self.replay_identity = Some(identity);
        self.replay_context = context;
        self
    }

    /// Return the canonical obligation id for this native trust_ir trust_mc request.
    ///
    /// This mirrors `trust_mc-trust-bmc`'s typed request naming so downstream proof
    /// consumers can reject stale metadata without scraping SMT-LIB labels.
    #[must_use]
    pub fn expected_obligation_id(&self) -> String {
        match self.proof_obligation_ids.as_slice() {
            [only] => {
                format!("trust_ir-native-trust_mc-request-{}-proof-{only}", self.native_request_id)
            }
            _ => format!("trust_ir-native-trust_mc-request-{}", self.native_request_id),
        }
    }

    /// Validate native trust_ir metadata against the bound candidate obligation id.
    ///
    /// This intentionally checks only stable bundle identity/admission fields:
    /// schema version, producer/adapter identity, CHC mode, digest descriptors,
    /// obligation/lineage membership, and the canonical request/proof id.
    pub fn validate_for_obligation_id(&self, obligation_id: &str) -> Result<(), Vec<String>> {
        let mut errors = Vec::new();
        if self.schema_version != Self::SCHEMA_VERSION {
            errors.push(format!(
                "unsupported native typed CHC metadata schema version: expected {}, got {}",
                Self::SCHEMA_VERSION,
                self.schema_version
            ));
        }
        if self.producer.trim().is_empty() {
            errors.push("native typed CHC metadata is missing producer identity".to_string());
        }
        if self.adapter_input.trim().is_empty() {
            errors.push("native typed CHC metadata is missing adapter input identity".to_string());
        }
        if !matches!(self.verification_mode.as_str(), "chc" | "pdr") {
            errors.push(format!(
                "native typed CHC/PDR metadata verification mode must be `chc` or `pdr`, got `{}`",
                self.verification_mode
            ));
        }
        validate_native_artifact_digest(
            "trust_ir_module_digest",
            &self.trust_ir_module_digest,
            &mut errors,
        );
        validate_native_artifact_digest(
            "lineage_manifest_digest",
            &self.lineage_manifest_digest,
            &mut errors,
        );
        if let Some(source_digest) = &self.source_digest {
            validate_native_artifact_digest("source_digest", source_digest, &mut errors);
        }
        if self.proof_obligation_ids.is_empty() {
            errors.push(
                "native typed CHC metadata must bind at least one proof obligation id".to_string(),
            );
        }
        if self.lineage_root_ids.is_empty() {
            errors.push(
                "native typed CHC metadata must bind at least one lineage root id".to_string(),
            );
        }
        match &self.compiler_facts_digest {
            Some(digest) => {
                validate_native_artifact_digest("compiler_facts_digest", digest, &mut errors);
            }
            None => {
                errors
                    .push("native typed CHC metadata is missing compiler_facts digest".to_string());
            }
        }
        validate_native_compiler_fact_sources(self, &mut errors);
        validate_native_replay_metadata(self, &mut errors);
        let expected_obligation_id = self.expected_obligation_id();
        // Separator-insensitive: the compiler emits the suite token as the crate
        // name `trust-mc` (hyphen) while native metadata uses the identifier form
        // `trust_mc` (underscore). They denote the same obligation; request/proof
        // ids are numeric, so canonicalizing `-`→`_` cannot merge distinct ones.
        if obligation_id.replace('-', "_") != expected_obligation_id.replace('-', "_") {
            errors.push(format!(
                "native obligation id `{obligation_id}` does not match metadata identity \
                 `{expected_obligation_id}`"
            ));
        }

        if errors.is_empty() { Ok(()) } else { Err(errors) }
    }
}

fn validate_native_replay_metadata(
    metadata: &NativeTypedChcObligationMetadata,
    errors: &mut Vec<String>,
) {
    match &metadata.replay_identity {
        Some(identity) => {
            if identity.engine.trim().is_empty() {
                errors.push("native typed CHC metadata replay identity is missing engine".into());
            }
            if identity.invocation.trim().is_empty() {
                errors
                    .push("native typed CHC metadata replay identity is missing invocation".into());
            }
            validate_native_artifact_digest(
                "replay_identity.transcript_digest",
                &identity.transcript_digest,
                errors,
            );
        }
        None => errors.push("native typed CHC metadata is missing replay identity".to_string()),
    }

    for unsupported in &metadata.replay_context.unsupported_modes {
        errors.push(format!(
            "native typed CHC metadata contains unsupported replay mode `{}`: {}",
            unsupported.reason, unsupported.detail
        ));
    }

    let proof_obligations: BTreeSet<u32> = metadata.proof_obligation_ids.iter().copied().collect();
    let mut atom_ids = BTreeSet::new();
    for atom in &metadata.replay_context.atoms {
        if !atom_ids.insert(atom.atom_id) {
            errors.push(format!(
                "native typed CHC metadata has duplicate replay atom {}",
                atom.atom_id
            ));
        }
        if atom.formula_schema.trim().is_empty() {
            errors.push(format!(
                "native typed CHC metadata replay atom {} is missing formula schema",
                atom.atom_id
            ));
        }
        validate_native_artifact_digest(
            "replay_context.atom.payload_digest",
            &atom.payload_digest,
            errors,
        );
        if atom.kind == NativeReplayAtomKindMetadata::Assertion
            && atom.proof_obligation_id.is_none()
            && atom.assertion_id.is_none()
        {
            errors.push(format!(
                "native typed CHC metadata replay assertion atom {} is missing assertion binding",
                atom.atom_id
            ));
        }
        if atom.assertion_id.is_some() && atom.proof_obligation_id.is_none() {
            errors.push(format!(
                "native typed CHC metadata replay atom {} has assertion id without proof obligation",
                atom.atom_id
            ));
        }
        if atom.span.is_some() && atom.proof_obligation_id.is_none() {
            errors.push(format!(
                "native typed CHC metadata replay atom {} has source span without proof obligation",
                atom.atom_id
            ));
        }
        if let Some(obligation) = atom.proof_obligation_id
            && !proof_obligations.contains(&obligation)
        {
            errors.push(format!(
                "native typed CHC metadata replay atom {} references proof obligation {}, \
                 which is outside proof_obligation_ids {:?}",
                atom.atom_id, obligation, metadata.proof_obligation_ids
            ));
        }
    }
}

fn validate_native_compiler_fact_sources(
    metadata: &NativeTypedChcObligationMetadata,
    errors: &mut Vec<String>,
) {
    if metadata.compiler_fact_sources.len() > metadata.compiler_fact_counts.obligation_sources {
        errors.push(format!(
            "native typed CHC metadata carries {} compiler_facts obligation sources, \
             but counts report only {}",
            metadata.compiler_fact_sources.len(),
            metadata.compiler_fact_counts.obligation_sources
        ));
    }

    let proof_obligations: BTreeSet<u32> = metadata.proof_obligation_ids.iter().copied().collect();
    let mut source_obligations = BTreeSet::new();
    let mut refs_by_kind: BTreeSet<NativeCompilerFactReference> = BTreeSet::new();

    for source in &metadata.compiler_fact_sources {
        if !proof_obligations.contains(&source.proof_obligation_id) {
            errors.push(format!(
                "native typed CHC metadata compiler_facts source references proof obligation {}, \
                 which is outside proof_obligation_ids {:?}",
                source.proof_obligation_id, metadata.proof_obligation_ids
            ));
        }
        if !source_obligations.insert(source.proof_obligation_id) {
            errors.push(format!(
                "native typed CHC metadata has duplicate compiler_facts source for proof obligation {}",
                source.proof_obligation_id
            ));
        }

        let mut source_refs = BTreeSet::new();
        for fact_ref in &source.fact_refs {
            if !source_refs.insert(*fact_ref) {
                errors.push(format!(
                    "native typed CHC metadata has duplicate compiler_facts reference {:?} for proof obligation {}",
                    fact_ref, source.proof_obligation_id
                ));
            }
            refs_by_kind.insert(*fact_ref);
            let available = metadata.compiler_fact_counts.count_for(fact_ref.kind);
            if available == 0 {
                errors.push(format!(
                    "native typed CHC metadata references {:?} compiler fact {}, \
                     but compiler_fact_counts reports none for that kind",
                    fact_ref.kind, fact_ref.id
                ));
            } else if fact_ref.id as usize >= available {
                errors.push(format!(
                    "native typed CHC metadata references {:?} compiler fact {}, \
                     but compiler_fact_counts reports only ids 0..{} for that kind",
                    fact_ref.kind,
                    fact_ref.id,
                    available - 1
                ));
            }
        }
    }

    for obligation in &metadata.proof_obligation_ids {
        if !source_obligations.contains(obligation) {
            errors.push(format!(
                "native typed CHC metadata is missing compiler_facts source for proof obligation {obligation}"
            ));
        }
    }

    for kind in [
        NativeCompilerFactKind::AdtLayout,
        NativeCompilerFactKind::FatPointer,
        NativeCompilerFactKind::TraitObjectMetadata,
        NativeCompilerFactKind::PointerOffset,
        NativeCompilerFactKind::Cast,
        NativeCompilerFactKind::Monomorphization,
    ] {
        let referenced = refs_by_kind.iter().filter(|fact_ref| fact_ref.kind == kind).count();
        let available = metadata.compiler_fact_counts.count_for(kind);
        if referenced > available {
            errors.push(format!(
                "native typed CHC metadata references {referenced} distinct {:?} compiler facts, \
                 but compiler_fact_counts reports only {available}",
                kind
            ));
        }
    }
}

fn validate_native_artifact_digest(
    role: &str,
    digest: &NativeArtifactDigest,
    errors: &mut Vec<String>,
) {
    if digest.algorithm.trim().is_empty() {
        errors.push(format!("native typed CHC metadata {role} is missing a digest algorithm"));
    }
    if digest.value.trim().is_empty() {
        errors.push(format!("native typed CHC metadata {role} is missing a digest value"));
    } else if !digest.value.bytes().all(|byte| byte.is_ascii_hexdigit()) {
        errors.push(format!("native typed CHC metadata {role} digest must be hexadecimal"));
    } else if digest.value.bytes().any(|byte| byte.is_ascii_uppercase()) {
        errors.push(format!("native typed CHC metadata {role} digest must be lowercase"));
    }
}

/// Normalized MIR-derived CHC/PDR input carried by candidate/proof APIs.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct MirDerivedChcPdrObligation {
    pub obligation_id: String,
    pub kind: MirObligationKind,
    pub origin: ObligationOrigin,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub native_metadata: Option<NativeTypedChcObligationMetadata>,
    pub normalized_input: String,
    pub normalized_input_hash: EvidenceHash,
}

impl MirDerivedChcPdrObligation {
    /// Create a MIR-derived CHC/PDR obligation and compute its deterministic input hash.
    #[must_use]
    pub fn new(
        obligation_id: impl Into<String>,
        kind: MirObligationKind,
        input: impl AsRef<str>,
    ) -> Self {
        Self::with_origin(obligation_id, kind, ObligationOrigin::MirDerived, input)
    }

    /// Create a router placeholder obligation. Placeholders fail proof-grade classification.
    #[must_use]
    pub fn router_placeholder(
        obligation_id: impl Into<String>,
        kind: MirObligationKind,
        input: impl AsRef<str>,
    ) -> Self {
        Self::with_origin(obligation_id, kind, ObligationOrigin::RouterPlaceholder, input)
    }

    fn with_origin(
        obligation_id: impl Into<String>,
        kind: MirObligationKind,
        origin: ObligationOrigin,
        input: impl AsRef<str>,
    ) -> Self {
        let normalized_input = normalize_chc_pdr_input(input.as_ref());
        let normalized_input_hash = EvidenceHash::sha256_bytes(normalized_input.as_bytes());
        Self {
            obligation_id: obligation_id.into(),
            kind,
            origin,
            native_metadata: None,
            normalized_input,
            normalized_input_hash,
        }
    }

    /// Attach typed native-bundle provenance to this proof obligation.
    #[must_use]
    pub fn with_native_metadata(mut self, metadata: NativeTypedChcObligationMetadata) -> Self {
        self.native_metadata = Some(metadata);
        self
    }
}

/// Normalize solver input before hashing.
///
/// This preserves content order and comments, while canonicalizing line endings,
/// trimming trailing horizontal whitespace, and enforcing one trailing newline.
#[must_use]
pub fn normalize_chc_pdr_input(input: &str) -> String {
    let normalized = input.replace("\r\n", "\n").replace('\r', "\n");
    let mut lines: Vec<&str> = normalized.lines().collect();
    while lines.last().is_some_and(|line| line.trim().is_empty()) {
        lines.pop();
    }

    let mut out = lines.into_iter().map(str::trim_end).collect::<Vec<_>>().join("\n");
    out.push('\n');
    out
}

/// Native full-verification problem shape.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum FullVerificationProblemKind {
    ChcPdr,
    DiagnosticBmc,
}

/// CHC/PDR proof kinds strong enough for full verification when metadata validates.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ChcPdrProofKind {
    ChcValidity,
    PdrInvariant,
}

/// Stable CHC/PDR problem statistics carried by native evidence.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct ChcPdrStats {
    pub relation_count: usize,
    pub clause_count: usize,
}

/// Typed replay outcome recorded alongside digest-backed proof artifacts.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ProofReplayStatus {
    Replayed,
    Failed,
    Unknown,
}

/// Typed checker outcome recorded alongside digest-backed proof artifacts.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ProofCheckStatus {
    Accepted,
    Rejected,
    Unknown,
}

/// Replay/check status for proof-grade CHC/PDR evidence.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct ProofReplayCheckStatus {
    pub replay: ProofReplayStatus,
    pub check: ProofCheckStatus,
}

impl ProofReplayCheckStatus {
    /// Replay and proof-checking both succeeded.
    #[must_use]
    pub const fn accepted() -> Self {
        Self { replay: ProofReplayStatus::Replayed, check: ProofCheckStatus::Accepted }
    }
}

/// Proof metadata required before CHC/PDR evidence can become proof-grade.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct FullProofEvidenceMetadata {
    pub producer: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub cache_key: Option<EvidenceHash>,
    pub normalized_input_hash: Option<EvidenceHash>,
    #[serde(
        default,
        skip_serializing_if = "Vec::is_empty",
        deserialize_with = "deserialize_bounded_evidence_hashes"
    )]
    pub transcript_hashes: Vec<EvidenceHash>,
    #[serde(
        default,
        skip_serializing_if = "Vec::is_empty",
        deserialize_with = "deserialize_bounded_evidence_hashes"
    )]
    pub replay_log_hashes: Vec<EvidenceHash>,
    /// Hash-addressed checker output that binds the solver transcript/replay
    /// to the proof consumer's validation decision.
    ///
    /// Required for tRust #1083/#1041 publication-grade CHC/PDR evidence.
    #[serde(
        default,
        skip_serializing_if = "Vec::is_empty",
        deserialize_with = "deserialize_bounded_evidence_hashes"
    )]
    pub checked_report_hashes: Vec<EvidenceHash>,
    /// Typed replay/check decision for the digest-backed artifacts above.
    ///
    /// Required so proof consumers do not have to parse checked-report text to
    /// know whether replay ran and the checker accepted the evidence.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub replay_check_status: Option<ProofReplayCheckStatus>,
}

/// Native artifact kinds emitted by trust_mc full verification.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum FullVerificationArtifactKind {
    CompilerInput,
    ObligationSet,
    TypedBmcProblem,
    TypedChcProblem,
    SmtRendering,
    SolverBinary,
    VerificationOptions,
    ResourceLimits,
    NormalizedInput,
    SolverTranscript,
    PdrInvariantModel,
    ReplayLog,
    CheckedProofReport,
    CounterexampleTrace,
    DiagnosticTrace,
    EvidenceManifest,
}

/// Typed reference to an exact proof artifact consumed by another artifact.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct FullVerificationArtifactReference {
    pub kind: FullVerificationArtifactKind,
    pub digest: EvidenceHash,
}

impl FullVerificationArtifactReference {
    #[must_use]
    pub const fn new(kind: FullVerificationArtifactKind, digest: EvidenceHash) -> Self {
        Self { kind, digest }
    }
}

/// Content-addressed identity shared by one linked proof-artifact set.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize)]
#[serde(transparent)]
pub struct ProofArtifactBindingId(String);

impl ProofArtifactBindingId {
    const PREFIX: &'static str = "trust_mc-proof-set-sha256:";

    /// Return the stable, content-addressed proof-set identity.
    #[must_use]
    pub fn as_str(&self) -> &str {
        &self.0
    }

    fn from_sha256(hash: EvidenceHash) -> Self {
        debug_assert_eq!(hash.algorithm, "sha256");
        Self(format!("{}{}", Self::PREFIX, hash.value))
    }

    fn parse(value: &str) -> Result<Self, FullVerificationArtifactMaterializationError> {
        let Some(hex) = value.strip_prefix(Self::PREFIX) else {
            return Err(FullVerificationArtifactMaterializationError::InvalidProofBindingId);
        };
        if !is_canonical_sha256_hex(hex) {
            return Err(FullVerificationArtifactMaterializationError::InvalidProofBindingId);
        }
        Ok(Self(value.to_string()))
    }
}

impl<'de> Deserialize<'de> for ProofArtifactBindingId {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct ProofArtifactBindingIdVisitor;

        impl Visitor<'_> for ProofArtifactBindingIdVisitor {
            type Value = ProofArtifactBindingId;

            fn expecting(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                formatter.write_str(
                    "`trust_mc-proof-set-sha256:` followed by exactly 64 lowercase hex characters",
                )
            }

            fn visit_str<E>(self, value: &str) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                ProofArtifactBindingId::parse(value).map_err(E::custom)
            }

            fn visit_string<E>(self, value: String) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                self.visit_str(&value)
            }
        }

        deserializer.deserialize_str(ProofArtifactBindingIdVisitor)
    }
}

/// Exact, bounded artifact bytes and producer-authored proof linkage.
///
/// Fields are private so callers cannot manufacture a length or linkage that
/// disagrees with the retained payload. Use the accessors on this type or on
/// [`FullVerificationArtifact`].
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(try_from = "FullVerificationArtifactMaterializationWire")]
pub struct FullVerificationArtifactMaterialization {
    bytes: Vec<u8>,
    byte_len: u64,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    proof_binding_id: Option<ProofArtifactBindingId>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    referenced_artifacts: Vec<FullVerificationArtifactReference>,
}

#[derive(Deserialize)]
struct FullVerificationArtifactMaterializationWire {
    #[serde(deserialize_with = "deserialize_bounded_artifact_bytes")]
    bytes: Vec<u8>,
    byte_len: u64,
    #[serde(default)]
    proof_binding_id: Option<ProofArtifactBindingId>,
    #[serde(default, deserialize_with = "deserialize_bounded_artifact_references")]
    referenced_artifacts: Vec<FullVerificationArtifactReference>,
}

impl TryFrom<FullVerificationArtifactMaterializationWire>
    for FullVerificationArtifactMaterialization
{
    type Error = FullVerificationArtifactMaterializationError;

    fn try_from(wire: FullVerificationArtifactMaterializationWire) -> Result<Self, Self::Error> {
        let materialization = Self {
            bytes: wire.bytes,
            byte_len: wire.byte_len,
            proof_binding_id: wire.proof_binding_id,
            referenced_artifacts: wire.referenced_artifacts,
        };
        materialization.validate()?;
        Ok(materialization)
    }
}

impl FullVerificationArtifactMaterialization {
    fn from_bytes(bytes: &[u8]) -> Result<Self, FullVerificationArtifactMaterializationError> {
        if bytes.len() > MAX_FULL_VERIFICATION_ARTIFACT_MATERIALIZATION_BYTES {
            return Err(FullVerificationArtifactMaterializationError::PayloadTooLarge {
                max: MAX_FULL_VERIFICATION_ARTIFACT_MATERIALIZATION_BYTES,
                actual: bytes.len(),
            });
        }
        Ok(Self {
            bytes: bytes.to_vec(),
            byte_len: bytes.len() as u64,
            proof_binding_id: None,
            referenced_artifacts: Vec::new(),
        })
    }

    fn with_proof_linkage(
        mut self,
        proof_binding_id: ProofArtifactBindingId,
        referenced_artifacts: Vec<FullVerificationArtifactReference>,
    ) -> Result<Self, FullVerificationArtifactMaterializationError> {
        self.proof_binding_id = Some(proof_binding_id);
        self.referenced_artifacts = referenced_artifacts;
        self.validate()?;
        Ok(self)
    }

    /// Return the retained artifact bytes.
    #[must_use]
    pub fn bytes(&self) -> &[u8] {
        &self.bytes
    }

    /// Return the retained artifact byte length.
    #[must_use]
    pub const fn byte_len(&self) -> u64 {
        self.byte_len
    }

    /// Return the producer-authored, content-addressed proof-set identity.
    #[must_use]
    pub fn proof_binding_id(&self) -> Option<&ProofArtifactBindingId> {
        self.proof_binding_id.as_ref()
    }

    /// Return exact artifact digests this payload consumed or checked.
    #[must_use]
    pub fn referenced_artifacts(&self) -> &[FullVerificationArtifactReference] {
        &self.referenced_artifacts
    }

    fn validate(&self) -> Result<(), FullVerificationArtifactMaterializationError> {
        if self.bytes.len() > MAX_FULL_VERIFICATION_ARTIFACT_MATERIALIZATION_BYTES {
            return Err(FullVerificationArtifactMaterializationError::PayloadTooLarge {
                max: MAX_FULL_VERIFICATION_ARTIFACT_MATERIALIZATION_BYTES,
                actual: self.bytes.len(),
            });
        }
        if self.byte_len != self.bytes.len() as u64 {
            return Err(FullVerificationArtifactMaterializationError::ByteLengthMismatch {
                declared: self.byte_len,
                actual: self.bytes.len() as u64,
            });
        }
        if self.referenced_artifacts.len() > MAX_LINKED_ARTIFACT_REFERENCES {
            return Err(FullVerificationArtifactMaterializationError::TooManyArtifactReferences {
                max: MAX_LINKED_ARTIFACT_REFERENCES,
                actual: self.referenced_artifacts.len(),
            });
        }
        if !self.referenced_artifacts.is_empty() && self.proof_binding_id.is_none() {
            return Err(
                FullVerificationArtifactMaterializationError::ReferencesWithoutProofBinding,
            );
        }
        let mut seen = BTreeSet::new();
        for reference in &self.referenced_artifacts {
            if !reference.digest.is_canonical_sha256() {
                return Err(FullVerificationArtifactMaterializationError::InvalidReferencedDigest);
            }
            if !seen.insert((reference.kind, &reference.digest.algorithm, &reference.digest.value))
            {
                return Err(
                    FullVerificationArtifactMaterializationError::DuplicateReferencedDigest,
                );
            }
        }
        if !self.referenced_artifacts.windows(2).all(|pair| {
            artifact_reference_sort_key(&pair[0]) < artifact_reference_sort_key(&pair[1])
        }) {
            return Err(
                FullVerificationArtifactMaterializationError::NonCanonicalArtifactReferenceOrder,
            );
        }
        Ok(())
    }
}

/// Invalid or unsafe exact verification-artifact materialization.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum FullVerificationArtifactMaterializationError {
    #[error("artifact payload exceeds the {max}-byte materialization limit: got {actual} bytes")]
    PayloadTooLarge { max: usize, actual: usize },
    #[error("artifact materialization byte length mismatch: declared {declared}, actual {actual}")]
    ByteLengthMismatch { declared: u64, actual: u64 },
    #[error("artifact materialization requires a digest")]
    MissingDigest,
    #[error("artifact materialization digest does not match retained bytes")]
    DigestMismatch,
    #[error("artifact materialization length does not match descriptor length")]
    DescriptorLengthMismatch,
    #[error("proof-bearing {kind:?} payload must not be empty")]
    EmptyProofPayload { kind: FullVerificationArtifactKind },
    #[error("normalized input digest does not match the exact normalized input bytes")]
    NormalizedInputDigestMismatch,
    #[error("proof-grade normalized input must not be empty")]
    EmptyNormalizedInput,
    #[error("proof-grade evidence requires a MIR-derived obligation")]
    NonMirDerivedObligation,
    #[error("proof-grade evidence requires nonzero relation and clause counts")]
    InvalidProofStatistics,
    #[error("PDR invariant evidence requires the candidate constructor and an exact model")]
    PdrInvariantCandidateRequired,
    #[error("PDR invariant candidate must declare at least one predicate interpretation")]
    InvalidPdrInvariantCount,
    #[error("proof artifact binding id is not canonical")]
    InvalidProofBindingId,
    #[error("artifact references require a producer-authored proof binding id")]
    ReferencesWithoutProofBinding,
    #[error("artifact referenced digest is not canonical SHA-256")]
    InvalidReferencedDigest,
    #[error("artifact referenced digests contain a duplicate")]
    DuplicateReferencedDigest,
    #[error("artifact materialization has too many references: maximum {max}, got {actual}")]
    TooManyArtifactReferences { max: usize, actual: usize },
    #[error("artifact references are not in strict canonical kind/digest order")]
    NonCanonicalArtifactReferenceOrder,
    #[error("artifact materialization is unavailable")]
    MaterializationUnavailable,
}

fn artifact_reference_sort_key(
    reference: &FullVerificationArtifactReference,
) -> (FullVerificationArtifactKind, &str, &str) {
    (reference.kind, reference.digest.algorithm.as_str(), reference.digest.value.as_str())
}

fn deserialize_bounded_artifact_bytes<'de, D>(deserializer: D) -> Result<Vec<u8>, D::Error>
where
    D: Deserializer<'de>,
{
    struct BoundedBytesVisitor;

    impl<'de> Visitor<'de> for BoundedBytesVisitor {
        type Value = Vec<u8>;

        fn expecting(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(
                formatter,
                "at most {MAX_FULL_VERIFICATION_ARTIFACT_MATERIALIZATION_BYTES} artifact bytes"
            )
        }

        fn visit_bytes<E>(self, bytes: &[u8]) -> Result<Self::Value, E>
        where
            E: serde::de::Error,
        {
            if bytes.len() > MAX_FULL_VERIFICATION_ARTIFACT_MATERIALIZATION_BYTES {
                return Err(E::custom(format_args!(
                    "artifact payload exceeds the {}-byte materialization limit",
                    MAX_FULL_VERIFICATION_ARTIFACT_MATERIALIZATION_BYTES
                )));
            }
            Ok(bytes.to_vec())
        }

        fn visit_byte_buf<E>(self, bytes: Vec<u8>) -> Result<Self::Value, E>
        where
            E: serde::de::Error,
        {
            if bytes.len() > MAX_FULL_VERIFICATION_ARTIFACT_MATERIALIZATION_BYTES {
                return Err(E::custom(format_args!(
                    "artifact payload exceeds the {}-byte materialization limit",
                    MAX_FULL_VERIFICATION_ARTIFACT_MATERIALIZATION_BYTES
                )));
            }
            Ok(bytes)
        }

        fn visit_seq<A>(self, mut sequence: A) -> Result<Self::Value, A::Error>
        where
            A: SeqAccess<'de>,
        {
            if sequence
                .size_hint()
                .is_some_and(|size| size > MAX_FULL_VERIFICATION_ARTIFACT_MATERIALIZATION_BYTES)
            {
                return Err(A::Error::custom(format_args!(
                    "artifact payload exceeds the {}-byte materialization limit",
                    MAX_FULL_VERIFICATION_ARTIFACT_MATERIALIZATION_BYTES
                )));
            }
            let mut bytes = Vec::with_capacity(
                sequence
                    .size_hint()
                    .unwrap_or(0)
                    .min(MAX_FULL_VERIFICATION_ARTIFACT_MATERIALIZATION_BYTES),
            );
            while let Some(byte) = sequence.next_element()? {
                if bytes.len() == MAX_FULL_VERIFICATION_ARTIFACT_MATERIALIZATION_BYTES {
                    return Err(A::Error::custom(format_args!(
                        "artifact payload exceeds the {}-byte materialization limit",
                        MAX_FULL_VERIFICATION_ARTIFACT_MATERIALIZATION_BYTES
                    )));
                }
                bytes.push(byte);
            }
            Ok(bytes)
        }
    }

    deserializer.deserialize_byte_buf(BoundedBytesVisitor)
}

fn deserialize_bounded_vec<'de, D, T, const MAX: usize>(
    deserializer: D,
    description: &'static str,
) -> Result<Vec<T>, D::Error>
where
    D: Deserializer<'de>,
    T: Deserialize<'de>,
{
    struct BoundedVecVisitor<T, const MAX: usize> {
        description: &'static str,
        marker: std::marker::PhantomData<fn() -> T>,
    }

    impl<'de, T, const MAX: usize> Visitor<'de> for BoundedVecVisitor<T, MAX>
    where
        T: Deserialize<'de>,
    {
        type Value = Vec<T>;

        fn expecting(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
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

    deserializer.deserialize_seq(BoundedVecVisitor::<T, MAX> {
        description,
        marker: std::marker::PhantomData,
    })
}

fn deserialize_bounded_artifact_references<'de, D>(
    deserializer: D,
) -> Result<Vec<FullVerificationArtifactReference>, D::Error>
where
    D: Deserializer<'de>,
{
    deserialize_bounded_vec::<_, _, MAX_LINKED_ARTIFACT_REFERENCES>(
        deserializer,
        "artifact references",
    )
}

fn deserialize_bounded_evidence_hashes<'de, D>(
    deserializer: D,
) -> Result<Vec<EvidenceHash>, D::Error>
where
    D: Deserializer<'de>,
{
    deserialize_bounded_vec::<_, _, MAX_PROOF_EVIDENCE_HASHES>(
        deserializer,
        "proof evidence hashes",
    )
}

fn deserialize_bounded_proof_artifacts<'de, D>(
    deserializer: D,
) -> Result<Vec<FullVerificationArtifact>, D::Error>
where
    D: Deserializer<'de>,
{
    deserialize_bounded_vec::<_, _, MAX_PROOF_EVIDENCE_ARTIFACTS>(
        deserializer,
        "proof evidence artifacts",
    )
}

fn deserialize_bounded_manifest_artifacts<'de, D>(
    deserializer: D,
) -> Result<Vec<FullVerificationArtifact>, D::Error>
where
    D: Deserializer<'de>,
{
    deserialize_bounded_vec::<_, _, MAX_MANIFEST_ARTIFACTS>(deserializer, "verification artifacts")
}

/// Native full-verification artifact descriptor.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct FullVerificationArtifact {
    pub kind: FullVerificationArtifactKind,
    pub label: String,
    pub digest: Option<EvidenceHash>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub byte_len: Option<u64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    materialization: Option<FullVerificationArtifactMaterialization>,
}

#[derive(Deserialize)]
struct FullVerificationArtifactWire {
    kind: FullVerificationArtifactKind,
    label: String,
    digest: Option<EvidenceHash>,
    #[serde(default)]
    byte_len: Option<u64>,
    #[serde(default)]
    materialization: Option<FullVerificationArtifactMaterialization>,
}

impl<'de> Deserialize<'de> for FullVerificationArtifact {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let wire = FullVerificationArtifactWire::deserialize(deserializer)?;
        let artifact = Self {
            kind: wire.kind,
            label: wire.label,
            digest: wire.digest,
            byte_len: wire.byte_len,
            materialization: wire.materialization,
        };
        artifact.validate_materialization().map_err(D::Error::custom)?;
        Ok(artifact)
    }
}

impl FullVerificationArtifact {
    /// Create an artifact descriptor without digest metadata.
    #[must_use]
    pub fn new(kind: FullVerificationArtifactKind, label: impl Into<String>) -> Self {
        Self { kind, label: label.into(), digest: None, byte_len: None, materialization: None }
    }

    /// Create a digest-backed artifact by hashing its byte payload.
    #[must_use]
    pub fn from_bytes(
        kind: FullVerificationArtifactKind,
        label: impl Into<String>,
        bytes: &[u8],
    ) -> Self {
        let label = label.into();
        match Self::try_from_bytes(kind, label.clone(), bytes) {
            Ok(artifact) => artifact,
            Err(FullVerificationArtifactMaterializationError::PayloadTooLarge { .. }) => Self {
                kind,
                label,
                digest: Some(EvidenceHash::sha256_bytes(bytes)),
                byte_len: Some(bytes.len() as u64),
                materialization: None,
            },
            Err(error) => {
                debug_assert!(false, "unexpected artifact materialization error: {error}");
                Self {
                    kind,
                    label,
                    digest: Some(EvidenceHash::sha256_bytes(bytes)),
                    byte_len: Some(bytes.len() as u64),
                    materialization: None,
                }
            }
        }
    }

    /// Create a digest-backed artifact while requiring exact bounded bytes.
    pub fn try_from_bytes(
        kind: FullVerificationArtifactKind,
        label: impl Into<String>,
        bytes: &[u8],
    ) -> Result<Self, FullVerificationArtifactMaterializationError> {
        Self {
            kind,
            label: label.into(),
            digest: Some(EvidenceHash::sha256_bytes(bytes)),
            byte_len: Some(bytes.len() as u64),
            materialization: Some(FullVerificationArtifactMaterialization::from_bytes(bytes)?),
        }
        .validated()
    }

    /// Attach an existing digest.
    #[must_use]
    pub fn with_digest(mut self, digest: EvidenceHash) -> Self {
        self.digest = Some(digest);
        if self.validate_materialization().is_err() {
            self.materialization = None;
        }
        self
    }

    /// Attach an existing byte length.
    #[must_use]
    pub fn with_byte_len(mut self, byte_len: u64) -> Self {
        self.byte_len = Some(byte_len);
        if self.validate_materialization().is_err() {
            self.materialization = None;
        }
        self
    }

    /// Return a validated exact materialization, when retained.
    #[must_use]
    pub fn materialization(&self) -> Option<&FullVerificationArtifactMaterialization> {
        self.validate_materialization().ok()?;
        self.materialization.as_ref()
    }

    /// Return validated exact artifact bytes, when retained.
    #[must_use]
    pub fn materialized_bytes(&self) -> Option<&[u8]> {
        Some(self.materialization()?.bytes())
    }

    /// Return the validated retained byte length.
    #[must_use]
    pub fn materialized_byte_len(&self) -> Option<u64> {
        Some(self.materialization()?.byte_len())
    }

    /// Return the producer-authored proof binding, when present and valid.
    #[must_use]
    pub fn proof_binding_id(&self) -> Option<&ProofArtifactBindingId> {
        self.materialization()?.proof_binding_id()
    }

    /// Return digests this exact artifact payload consumed or checked.
    #[must_use]
    pub fn referenced_artifacts(&self) -> &[FullVerificationArtifactReference] {
        self.materialization()
            .map_or(&[], FullVerificationArtifactMaterialization::referenced_artifacts)
    }

    /// Validate the descriptor against its retained bytes and typed linkage.
    pub fn validate_materialization(
        &self,
    ) -> Result<(), FullVerificationArtifactMaterializationError> {
        let Some(materialization) = &self.materialization else {
            return Ok(());
        };
        materialization.validate()?;
        let Some(digest) = &self.digest else {
            return Err(FullVerificationArtifactMaterializationError::MissingDigest);
        };
        if digest != &EvidenceHash::sha256_bytes(materialization.bytes()) {
            return Err(FullVerificationArtifactMaterializationError::DigestMismatch);
        }
        if self.byte_len != Some(materialization.byte_len()) {
            return Err(FullVerificationArtifactMaterializationError::DescriptorLengthMismatch);
        }
        Ok(())
    }

    fn with_proof_linkage(
        mut self,
        proof_binding_id: ProofArtifactBindingId,
        referenced_artifacts: Vec<FullVerificationArtifactReference>,
    ) -> Result<Self, FullVerificationArtifactMaterializationError> {
        let materialization = self
            .materialization
            .take()
            .ok_or(FullVerificationArtifactMaterializationError::MaterializationUnavailable)?;
        self.materialization =
            Some(materialization.with_proof_linkage(proof_binding_id, referenced_artifacts)?);
        self.validated()
    }

    fn validated(self) -> Result<Self, FullVerificationArtifactMaterializationError> {
        self.validate_materialization()?;
        Ok(self)
    }
}

/// Content-addressed manifest for one native verification attempt.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ContentAddressedEvidenceManifest {
    pub schema_version: u32,
    pub cache_key: EvidenceHash,
    pub input: FullVerificationArtifact,
    pub obligation_set: FullVerificationArtifact,
    pub typed_problem: Option<FullVerificationArtifact>,
    pub smt_rendering: Option<FullVerificationArtifact>,
    pub solver_binary: Option<FullVerificationArtifact>,
    pub solver_transcript: Option<FullVerificationArtifact>,
    pub replay_log: Option<FullVerificationArtifact>,
    pub checked_report: Option<FullVerificationArtifact>,
    #[serde(
        default,
        skip_serializing_if = "Vec::is_empty",
        deserialize_with = "deserialize_bounded_manifest_artifacts"
    )]
    pub invariants: Vec<FullVerificationArtifact>,
    #[serde(
        default,
        skip_serializing_if = "Vec::is_empty",
        deserialize_with = "deserialize_bounded_manifest_artifacts"
    )]
    pub counterexamples: Vec<FullVerificationArtifact>,
    pub options: FullVerificationArtifact,
    pub resource_limits: FullVerificationArtifact,
}

/// Cache-key input for one native full-verification attempt.
///
/// The key is intentionally built from typed identity and digest components,
/// not from diagnostic text. It covers the verifier build, solver identity,
/// typed compiler input snapshot, proof mode/options/resources, normalized
/// solver input, and obligation set.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FullVerificationCacheKeyParts {
    pub trust_mc_version: String,
    pub trust_mc_commit: String,
    pub trust_mc_dirty: bool,
    pub ay_solver: FullVerificationArtifact,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub trust_ir_snapshot: Option<FullVerificationArtifact>,
    pub proof_mode: String,
    pub options: FullVerificationArtifact,
    pub resource_limits: FullVerificationArtifact,
    pub normalized_input_hash: EvidenceHash,
    pub obligation_set_hash: EvidenceHash,
}

/// Deterministic cache key for native full-verification evidence.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FullVerificationCacheKey {
    pub schema_version: u32,
    pub key: EvidenceHash,
    pub parts: FullVerificationCacheKeyParts,
}

impl FullVerificationCacheKey {
    pub const SCHEMA_VERSION: u32 = 1;

    /// Build a cache key from typed/digest-backed parts.
    #[must_use]
    pub fn from_parts(parts: FullVerificationCacheKeyParts) -> Self {
        let key = full_verification_cache_key(&parts);
        Self { schema_version: Self::SCHEMA_VERSION, key, parts }
    }

    /// Recompute the key from the stored parts.
    #[must_use]
    pub fn recompute_key(&self) -> EvidenceHash {
        full_verification_cache_key(&self.parts)
    }

    /// Validate identity fields, digest presence, and key consistency.
    pub fn validate(&self) -> Result<(), Vec<String>> {
        let mut errors = Vec::new();
        if self.schema_version != Self::SCHEMA_VERSION {
            errors.push(format!(
                "unsupported full-verification cache-key schema version: expected {}, got {}",
                Self::SCHEMA_VERSION,
                self.schema_version
            ));
        }
        if self.parts.trust_mc_version.trim().is_empty() {
            errors.push("cache key is missing trust_mc version identity".to_string());
        }
        if self.parts.trust_mc_commit.trim().is_empty() {
            errors.push("cache key is missing trust_mc commit identity".to_string());
        }
        if self.parts.proof_mode.trim().is_empty() {
            errors.push("cache key is missing proof mode".to_string());
        }
        require_artifact_digest("ay_solver", &self.parts.ay_solver, &mut errors);
        optional_artifact_digest(
            "trust_ir_snapshot",
            self.parts.trust_ir_snapshot.as_ref(),
            &mut errors,
        );
        require_artifact_digest("options", &self.parts.options, &mut errors);
        require_artifact_digest("resource_limits", &self.parts.resource_limits, &mut errors);
        if !self.parts.normalized_input_hash.is_canonical_sha256() {
            errors.push("cache key normalized input hash is not canonical SHA-256".to_string());
        }
        if !self.parts.obligation_set_hash.is_canonical_sha256() {
            errors.push("cache key obligation-set hash is not canonical SHA-256".to_string());
        }
        if !self.key.is_canonical_sha256() {
            errors.push("cache key digest is not canonical SHA-256".to_string());
        } else if self.key != self.recompute_key() {
            errors.push("cache key digest does not match cache-key parts".to_string());
        }

        if errors.is_empty() { Ok(()) } else { Err(errors) }
    }
}

/// Input parts for constructing a content-addressed manifest.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ContentAddressedEvidenceManifestParts {
    pub input: FullVerificationArtifact,
    pub obligation_set: FullVerificationArtifact,
    pub typed_problem: Option<FullVerificationArtifact>,
    pub smt_rendering: Option<FullVerificationArtifact>,
    pub solver_binary: Option<FullVerificationArtifact>,
    pub solver_transcript: Option<FullVerificationArtifact>,
    pub replay_log: Option<FullVerificationArtifact>,
    pub checked_report: Option<FullVerificationArtifact>,
    pub invariants: Vec<FullVerificationArtifact>,
    pub counterexamples: Vec<FullVerificationArtifact>,
    pub options: FullVerificationArtifact,
    pub resource_limits: FullVerificationArtifact,
}

impl ContentAddressedEvidenceManifest {
    pub const SCHEMA_VERSION: u32 = 1;

    /// Build a manifest with a cache key derived from every declared digest.
    #[must_use]
    pub fn from_parts(parts: ContentAddressedEvidenceManifestParts) -> Self {
        let cache_key = manifest_cache_key(&parts);
        Self {
            schema_version: Self::SCHEMA_VERSION,
            cache_key,
            input: parts.input,
            obligation_set: parts.obligation_set,
            typed_problem: parts.typed_problem,
            smt_rendering: parts.smt_rendering,
            solver_binary: parts.solver_binary,
            solver_transcript: parts.solver_transcript,
            replay_log: parts.replay_log,
            checked_report: parts.checked_report,
            invariants: parts.invariants,
            counterexamples: parts.counterexamples,
            options: parts.options,
            resource_limits: parts.resource_limits,
        }
    }

    /// Recompute the cache key from manifest contents.
    #[must_use]
    pub fn recompute_cache_key(&self) -> EvidenceHash {
        manifest_cache_key(&self.parts())
    }

    /// Validate required digests and cache-key consistency.
    pub fn validate(&self) -> Result<(), Vec<String>> {
        let mut errors = Vec::new();
        if self.schema_version != Self::SCHEMA_VERSION {
            errors.push(format!(
                "unsupported manifest schema version: expected {}, got {}",
                Self::SCHEMA_VERSION,
                self.schema_version
            ));
        }
        require_artifact_digest("input", &self.input, &mut errors);
        require_artifact_digest("obligation_set", &self.obligation_set, &mut errors);
        require_artifact_digest("options", &self.options, &mut errors);
        require_artifact_digest("resource_limits", &self.resource_limits, &mut errors);
        optional_artifact_digest("typed_problem", self.typed_problem.as_ref(), &mut errors);
        optional_artifact_digest("smt_rendering", self.smt_rendering.as_ref(), &mut errors);
        optional_artifact_digest("solver_binary", self.solver_binary.as_ref(), &mut errors);
        optional_artifact_digest("solver_transcript", self.solver_transcript.as_ref(), &mut errors);
        optional_artifact_digest("replay_log", self.replay_log.as_ref(), &mut errors);
        optional_artifact_digest("checked_report", self.checked_report.as_ref(), &mut errors);
        for artifact in &self.invariants {
            require_artifact_digest("invariant", artifact, &mut errors);
        }
        for artifact in &self.counterexamples {
            require_artifact_digest("counterexample", artifact, &mut errors);
        }
        if !self.cache_key.is_canonical_sha256() {
            errors.push("manifest cache key is not canonical SHA-256".to_string());
        } else if self.cache_key != self.recompute_cache_key() {
            errors.push("manifest cache key does not match manifest contents".to_string());
        }
        if errors.is_empty() { Ok(()) } else { Err(errors) }
    }

    fn parts(&self) -> ContentAddressedEvidenceManifestParts {
        ContentAddressedEvidenceManifestParts {
            input: self.input.clone(),
            obligation_set: self.obligation_set.clone(),
            typed_problem: self.typed_problem.clone(),
            smt_rendering: self.smt_rendering.clone(),
            solver_binary: self.solver_binary.clone(),
            solver_transcript: self.solver_transcript.clone(),
            replay_log: self.replay_log.clone(),
            checked_report: self.checked_report.clone(),
            invariants: self.invariants.clone(),
            counterexamples: self.counterexamples.clone(),
            options: self.options.clone(),
            resource_limits: self.resource_limits.clone(),
        }
    }
}

/// Typed evidence produced by trust_mc's CHC/PDR-family full verifier.
///
/// Construction and transport do not themselves grant authority. Public
/// admission deliberately rejects both `ChcValidity` and `PdrInvariant`
/// candidates; a private consumer must validate the candidate structure and
/// then independently derive or replay the exact obligation.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ChcPdrProofEvidence {
    pub kind: ChcPdrProofKind,
    pub obligation: MirDerivedChcPdrObligation,
    pub stats: ChcPdrStats,
    pub metadata: FullProofEvidenceMetadata,
    pub invariant_count: usize,
    #[serde(default, deserialize_with = "deserialize_bounded_proof_artifacts")]
    pub artifacts: Vec<FullVerificationArtifact>,
}

impl ChcPdrProofEvidence {
    /// Create CHC/PDR proof evidence without proof-grade artifact metadata.
    #[must_use]
    pub fn new(
        kind: ChcPdrProofKind,
        obligation: MirDerivedChcPdrObligation,
        stats: ChcPdrStats,
    ) -> Self {
        Self {
            kind,
            obligation,
            stats,
            metadata: FullProofEvidenceMetadata::default(),
            invariant_count: 0,
            artifacts: Vec::new(),
        }
    }

    /// Create legacy proof-shaped evidence by hashing and retaining artifact bytes.
    ///
    /// This compatibility constructor does not claim which transcript the
    /// replay/check payloads consumed. Consequently, its result intentionally
    /// remains non-proof-grade under the publication classifier. Producers that
    /// obtained replay/check output from the corresponding operations must use
    /// [`Self::try_chc_validity_candidate_from_linked_bytes`] for `ChcValidity`, or the
    /// reject-only [`Self::try_pdr_invariant_candidate_from_linked_bytes`] for a
    /// `PdrInvariant` candidate.
    #[must_use]
    pub fn proof_grade_from_bytes(
        kind: ChcPdrProofKind,
        obligation: MirDerivedChcPdrObligation,
        stats: ChcPdrStats,
        solver_transcript: (&str, &[u8]),
        replay_log: (&str, &[u8]),
        checked_report: (&str, &[u8]),
    ) -> Self {
        let input_hash = obligation.normalized_input_hash.clone();
        let transcript = FullVerificationArtifact::from_bytes(
            FullVerificationArtifactKind::SolverTranscript,
            solver_transcript.0,
            solver_transcript.1,
        );
        let replay = FullVerificationArtifact::from_bytes(
            FullVerificationArtifactKind::ReplayLog,
            replay_log.0,
            replay_log.1,
        );
        let report = FullVerificationArtifact::from_bytes(
            FullVerificationArtifactKind::CheckedProofReport,
            checked_report.0,
            checked_report.1,
        );
        let metadata = FullProofEvidenceMetadata {
            producer: Some(PRODUCER.to_string()),
            cache_key: None,
            normalized_input_hash: Some(input_hash.clone()),
            transcript_hashes: artifact_digest_vec(&transcript),
            replay_log_hashes: artifact_digest_vec(&replay),
            checked_report_hashes: artifact_digest_vec(&report),
            replay_check_status: Some(ProofReplayCheckStatus {
                replay: ProofReplayStatus::Unknown,
                check: ProofCheckStatus::Unknown,
            }),
        };
        let input = FullVerificationArtifact::from_bytes(
            FullVerificationArtifactKind::NormalizedInput,
            format!("trust_mc://full-verifier/{}/normalized-input", obligation.obligation_id),
            obligation.normalized_input.as_bytes(),
        );

        Self {
            metadata,
            artifacts: vec![input, transcript, replay, report],
            ..Self::new(kind, obligation, stats)
        }
    }

    /// Create a linked `ChcValidity` candidate with exact, bounded artifact
    /// bytes and producer-authored transcript/replay/check relationships.
    ///
    /// The payloads claim that `replay_log` consumed the exact
    /// `solver_transcript` and that `checked_report` consumed that transcript and
    /// replay log. Production callers construct their serialized payloads with
    /// those exact digests embedded; this API records the same relationship in
    /// typed transport metadata.
    /// This is transport validation, not proof authority: arbitrary callers can
    /// supply all three payloads. The resulting candidate therefore remains
    /// non-proof-grade until a private consumer independently derives or replays
    /// the result. `PdrInvariant` is deliberately rejected here because it must
    /// use the invariant-carrying candidate constructor.
    pub fn try_proof_grade_from_linked_bytes(
        kind: ChcPdrProofKind,
        obligation: MirDerivedChcPdrObligation,
        stats: ChcPdrStats,
        solver_transcript: (&str, &[u8]),
        replay_log: (&str, &[u8]),
        checked_report: (&str, &[u8]),
    ) -> Result<Self, FullVerificationArtifactMaterializationError> {
        if kind == ChcPdrProofKind::PdrInvariant {
            return Err(
                FullVerificationArtifactMaterializationError::PdrInvariantCandidateRequired,
            );
        }
        Self::try_chc_validity_candidate_from_linked_bytes(
            obligation,
            stats,
            solver_transcript,
            replay_log,
            checked_report,
        )
    }

    /// Create a linked, reject-only CHC-validity candidate.
    ///
    /// The payload relationships are validated and content-addressed, but this
    /// public constructor cannot attest that a solver or checker actually ran.
    /// Publication therefore requires a separate private authority boundary.
    pub fn try_chc_validity_candidate_from_linked_bytes(
        obligation: MirDerivedChcPdrObligation,
        stats: ChcPdrStats,
        solver_transcript: (&str, &[u8]),
        replay_log: (&str, &[u8]),
        checked_report: (&str, &[u8]),
    ) -> Result<Self, FullVerificationArtifactMaterializationError> {
        Self::try_proof_grade_from_linked_bytes_inner(
            ChcPdrProofKind::ChcValidity,
            obligation,
            stats,
            solver_transcript,
            replay_log,
            checked_report,
            None,
            0,
        )
    }

    /// Create producer-linked PDR evidence carrying the exact invariant-model bytes.
    ///
    /// This binds the model into the content-addressed artifact set, but remains
    /// producer-authored diagnostic evidence. It does not independently replay
    /// the invariant and therefore grants no consumer authority by itself.
    pub fn try_pdr_invariant_candidate_from_linked_bytes(
        obligation: MirDerivedChcPdrObligation,
        stats: ChcPdrStats,
        invariant_count: usize,
        solver_transcript: (&str, &[u8]),
        replay_log: (&str, &[u8]),
        checked_report: (&str, &[u8]),
        invariant_model: (&str, &[u8]),
    ) -> Result<Self, FullVerificationArtifactMaterializationError> {
        Self::try_proof_grade_from_linked_bytes_inner(
            ChcPdrProofKind::PdrInvariant,
            obligation,
            stats,
            solver_transcript,
            replay_log,
            checked_report,
            Some(invariant_model),
            invariant_count,
        )
    }

    fn try_proof_grade_from_linked_bytes_inner(
        kind: ChcPdrProofKind,
        obligation: MirDerivedChcPdrObligation,
        stats: ChcPdrStats,
        solver_transcript: (&str, &[u8]),
        replay_log: (&str, &[u8]),
        checked_report: (&str, &[u8]),
        invariant_model: Option<(&str, &[u8])>,
        invariant_count: usize,
    ) -> Result<Self, FullVerificationArtifactMaterializationError> {
        if obligation.origin != ObligationOrigin::MirDerived {
            return Err(FullVerificationArtifactMaterializationError::NonMirDerivedObligation);
        }
        if obligation.normalized_input.trim().is_empty() {
            return Err(FullVerificationArtifactMaterializationError::EmptyNormalizedInput);
        }
        if stats.relation_count == 0 || stats.clause_count == 0 {
            return Err(FullVerificationArtifactMaterializationError::InvalidProofStatistics);
        }
        if invariant_model.is_some() && invariant_count == 0 {
            return Err(FullVerificationArtifactMaterializationError::InvalidPdrInvariantCount);
        }
        for (artifact_kind, bytes) in [
            (FullVerificationArtifactKind::SolverTranscript, solver_transcript.1),
            (FullVerificationArtifactKind::ReplayLog, replay_log.1),
            (FullVerificationArtifactKind::CheckedProofReport, checked_report.1),
        ] {
            if bytes.is_empty() {
                return Err(FullVerificationArtifactMaterializationError::EmptyProofPayload {
                    kind: artifact_kind,
                });
            }
        }
        if invariant_model.is_some_and(|(_, bytes)| bytes.is_empty()) {
            return Err(FullVerificationArtifactMaterializationError::EmptyProofPayload {
                kind: FullVerificationArtifactKind::PdrInvariantModel,
            });
        }

        let input_hash = EvidenceHash::sha256_bytes(obligation.normalized_input.as_bytes());
        if input_hash != obligation.normalized_input_hash {
            return Err(
                FullVerificationArtifactMaterializationError::NormalizedInputDigestMismatch,
            );
        }
        let transcript = FullVerificationArtifact::try_from_bytes(
            FullVerificationArtifactKind::SolverTranscript,
            solver_transcript.0,
            solver_transcript.1,
        )?;
        let replay = FullVerificationArtifact::try_from_bytes(
            FullVerificationArtifactKind::ReplayLog,
            replay_log.0,
            replay_log.1,
        )?;
        let report = FullVerificationArtifact::try_from_bytes(
            FullVerificationArtifactKind::CheckedProofReport,
            checked_report.0,
            checked_report.1,
        )?;
        let invariant = invariant_model
            .map(|(label, bytes)| {
                FullVerificationArtifact::try_from_bytes(
                    FullVerificationArtifactKind::PdrInvariantModel,
                    label,
                    bytes,
                )
            })
            .transpose()?;
        let input = FullVerificationArtifact::try_from_bytes(
            FullVerificationArtifactKind::NormalizedInput,
            format!("trust_mc://full-verifier/{}/normalized-input", obligation.obligation_id),
            obligation.normalized_input.as_bytes(),
        )?;

        let transcript_hash = required_artifact_digest(&transcript);
        let replay_hash = required_artifact_digest(&replay);
        let report_hash = required_artifact_digest(&report);
        let invariant_hash = invariant.as_ref().map(required_artifact_digest);
        let proof_binding_id = linked_proof_binding_id(
            kind,
            &obligation,
            &transcript_hash,
            &replay_hash,
            &report_hash,
            invariant_hash.as_ref(),
            &stats,
            invariant_count,
        );
        let input = input.with_proof_linkage(proof_binding_id.clone(), Vec::new())?;
        let transcript = transcript.with_proof_linkage(
            proof_binding_id.clone(),
            vec![FullVerificationArtifactReference::new(
                FullVerificationArtifactKind::NormalizedInput,
                input_hash.clone(),
            )],
        )?;
        let invariant = invariant
            .map(|artifact| {
                artifact.with_proof_linkage(
                    proof_binding_id.clone(),
                    vec![FullVerificationArtifactReference::new(
                        FullVerificationArtifactKind::NormalizedInput,
                        input_hash.clone(),
                    )],
                )
            })
            .transpose()?;
        let mut replay_references = vec![FullVerificationArtifactReference::new(
            FullVerificationArtifactKind::SolverTranscript,
            transcript_hash.clone(),
        )];
        if let Some(invariant_hash) = &invariant_hash {
            replay_references.push(FullVerificationArtifactReference::new(
                FullVerificationArtifactKind::PdrInvariantModel,
                invariant_hash.clone(),
            ));
        }
        let replay = replay.with_proof_linkage(proof_binding_id.clone(), replay_references)?;
        let mut report_references = vec![FullVerificationArtifactReference::new(
            FullVerificationArtifactKind::SolverTranscript,
            transcript_hash.clone(),
        )];
        if let Some(invariant_hash) = &invariant_hash {
            report_references.push(FullVerificationArtifactReference::new(
                FullVerificationArtifactKind::PdrInvariantModel,
                invariant_hash.clone(),
            ));
        }
        report_references.push(FullVerificationArtifactReference::new(
            FullVerificationArtifactKind::ReplayLog,
            replay_hash.clone(),
        ));
        let report = report.with_proof_linkage(proof_binding_id, report_references)?;
        let metadata = FullProofEvidenceMetadata {
            producer: Some(PRODUCER.to_string()),
            cache_key: None,
            normalized_input_hash: Some(input_hash),
            transcript_hashes: vec![transcript_hash],
            replay_log_hashes: vec![replay_hash],
            checked_report_hashes: vec![report_hash],
            replay_check_status: Some(ProofReplayCheckStatus {
                replay: ProofReplayStatus::Unknown,
                check: ProofCheckStatus::Unknown,
            }),
        };

        let mut artifacts = vec![input, transcript, replay, report];
        if let Some(invariant) = invariant {
            artifacts.push(invariant);
        }
        Ok(Self { metadata, invariant_count, artifacts, ..Self::new(kind, obligation, stats) })
    }

    /// Attach a proof artifact.
    #[must_use]
    pub fn with_artifact(mut self, artifact: FullVerificationArtifact) -> Self {
        self.artifacts.push(artifact);
        self
    }

    /// Attach proof metadata.
    #[must_use]
    pub fn with_metadata(mut self, metadata: FullProofEvidenceMetadata) -> Self {
        self.metadata = metadata;
        self
    }
}

fn required_artifact_digest(artifact: &FullVerificationArtifact) -> EvidenceHash {
    artifact.digest.clone().expect("try_from_bytes always attaches a digest")
}

fn linked_proof_binding_id(
    kind: ChcPdrProofKind,
    obligation: &MirDerivedChcPdrObligation,
    transcript_hash: &EvidenceHash,
    replay_hash: &EvidenceHash,
    checked_report_hash: &EvidenceHash,
    invariant_model_hash: Option<&EvidenceHash>,
    stats: &ChcPdrStats,
    invariant_count: usize,
) -> ProofArtifactBindingId {
    let mut hasher = Sha256::new();
    let domain = if invariant_model_hash.is_some() {
        b"trust_mc.linked-proof-set/v2".as_slice()
    } else {
        b"trust_mc.linked-proof-set/v1".as_slice()
    };
    push_proof_binding_component(&mut hasher, "domain", domain);
    push_proof_binding_component(
        &mut hasher,
        "proof_kind",
        match kind {
            ChcPdrProofKind::ChcValidity => b"chc-validity",
            ChcPdrProofKind::PdrInvariant => b"pdr-invariant",
        },
    );
    push_proof_binding_component(&mut hasher, "obligation_id", obligation.obligation_id.as_bytes());
    push_proof_binding_hash(&mut hasher, "normalized_input", &obligation.normalized_input_hash);
    push_proof_binding_hash(&mut hasher, "solver_transcript", transcript_hash);
    push_proof_binding_hash(&mut hasher, "replay_log", replay_hash);
    push_proof_binding_hash(&mut hasher, "checked_report", checked_report_hash);
    if let Some(invariant_model_hash) = invariant_model_hash {
        push_proof_binding_hash(&mut hasher, "pdr_invariant_model", invariant_model_hash);
        push_proof_binding_component(
            &mut hasher,
            "stats.relation_count",
            &(stats.relation_count as u64).to_be_bytes(),
        );
        push_proof_binding_component(
            &mut hasher,
            "stats.clause_count",
            &(stats.clause_count as u64).to_be_bytes(),
        );
        push_proof_binding_component(
            &mut hasher,
            "invariant_count",
            &(invariant_count as u64).to_be_bytes(),
        );
    }

    if let Some(metadata) = &obligation.native_metadata {
        push_proof_binding_component(&mut hasher, "native.present", b"1");
        push_proof_binding_component(
            &mut hasher,
            "native.schema_version",
            &metadata.schema_version.to_be_bytes(),
        );
        push_proof_binding_component(&mut hasher, "native.producer", metadata.producer.as_bytes());
        push_proof_binding_component(
            &mut hasher,
            "native.adapter_input",
            metadata.adapter_input.as_bytes(),
        );
        push_proof_binding_component(
            &mut hasher,
            "native.request_id",
            &metadata.native_request_id.to_be_bytes(),
        );
        push_proof_binding_component(
            &mut hasher,
            "native.function_id",
            &metadata.function_id.to_be_bytes(),
        );
        push_proof_binding_component(
            &mut hasher,
            "native.verification_mode",
            metadata.verification_mode.as_bytes(),
        );
        push_proof_binding_native_hash(
            &mut hasher,
            "native.trust_ir_module",
            &metadata.trust_ir_module_digest,
        );
        push_proof_binding_native_hash(
            &mut hasher,
            "native.lineage_manifest",
            &metadata.lineage_manifest_digest,
        );
        if let Some(source_digest) = &metadata.source_digest {
            push_proof_binding_native_hash(&mut hasher, "native.source", source_digest);
        }
        if let Some(compiler_facts_digest) = &metadata.compiler_facts_digest {
            push_proof_binding_native_hash(
                &mut hasher,
                "native.compiler_facts",
                compiler_facts_digest,
            );
        }
        for proof_id in &metadata.proof_obligation_ids {
            push_proof_binding_component(
                &mut hasher,
                "native.proof_obligation_id",
                &proof_id.to_be_bytes(),
            );
        }
        for lineage_root_id in &metadata.lineage_root_ids {
            push_proof_binding_component(
                &mut hasher,
                "native.lineage_root_id",
                &lineage_root_id.to_be_bytes(),
            );
        }
        if let Some(replay_identity) = &metadata.replay_identity {
            push_proof_binding_component(
                &mut hasher,
                "native.replay.engine",
                replay_identity.engine.as_bytes(),
            );
            push_proof_binding_component(
                &mut hasher,
                "native.replay.invocation",
                replay_identity.invocation.as_bytes(),
            );
            push_proof_binding_native_hash(
                &mut hasher,
                "native.replay.transcript",
                &replay_identity.transcript_digest,
            );
        }
    } else {
        push_proof_binding_component(&mut hasher, "native.present", b"0");
    }

    let digest = hasher.finalize();
    ProofArtifactBindingId::from_sha256(EvidenceHash {
        algorithm: "sha256".to_string(),
        value: format!("{digest:x}"),
    })
}

fn push_proof_binding_hash(hasher: &mut Sha256, label: &str, hash: &EvidenceHash) {
    push_proof_binding_component(hasher, &format!("{label}.algorithm"), hash.algorithm.as_bytes());
    push_proof_binding_component(hasher, &format!("{label}.value"), hash.value.as_bytes());
}

fn push_proof_binding_native_hash(hasher: &mut Sha256, label: &str, hash: &NativeArtifactDigest) {
    push_proof_binding_component(hasher, &format!("{label}.algorithm"), hash.algorithm.as_bytes());
    push_proof_binding_component(hasher, &format!("{label}.value"), hash.value.as_bytes());
}

fn push_proof_binding_component(hasher: &mut Sha256, label: &str, value: &[u8]) {
    hasher.update((label.len() as u64).to_be_bytes());
    hasher.update(label.as_bytes());
    hasher.update((value.len() as u64).to_be_bytes());
    hasher.update(value);
}

fn full_verification_cache_key(parts: &FullVerificationCacheKeyParts) -> EvidenceHash {
    let mut payload = String::new();
    push_cache_component(
        &mut payload,
        "schema_version",
        &FullVerificationCacheKey::SCHEMA_VERSION.to_string(),
    );
    push_cache_component(&mut payload, "trust_mc_version", &parts.trust_mc_version);
    push_cache_component(&mut payload, "trust_mc_commit", &parts.trust_mc_commit);
    push_cache_component(
        &mut payload,
        "trust_mc_dirty",
        if parts.trust_mc_dirty { "1" } else { "0" },
    );
    push_artifact_component(&mut payload, "ay_solver", &parts.ay_solver);
    push_optional_artifact_component(
        &mut payload,
        "trust_ir_snapshot",
        parts.trust_ir_snapshot.as_ref(),
    );
    push_cache_component(&mut payload, "proof_mode", &parts.proof_mode);
    push_artifact_component(&mut payload, "options", &parts.options);
    push_artifact_component(&mut payload, "resource_limits", &parts.resource_limits);
    push_cache_component(
        &mut payload,
        "normalized_input_hash.algorithm",
        &parts.normalized_input_hash.algorithm,
    );
    push_cache_component(
        &mut payload,
        "normalized_input_hash.value",
        &parts.normalized_input_hash.value,
    );
    push_cache_component(
        &mut payload,
        "obligation_set_hash.algorithm",
        &parts.obligation_set_hash.algorithm,
    );
    push_cache_component(
        &mut payload,
        "obligation_set_hash.value",
        &parts.obligation_set_hash.value,
    );
    EvidenceHash::sha256_bytes(payload.as_bytes())
}

fn manifest_cache_key(parts: &ContentAddressedEvidenceManifestParts) -> EvidenceHash {
    let mut payload = String::new();
    push_cache_component(
        &mut payload,
        "schema_version",
        &ContentAddressedEvidenceManifest::SCHEMA_VERSION.to_string(),
    );
    push_artifact_component(&mut payload, "input", &parts.input);
    push_artifact_component(&mut payload, "obligation_set", &parts.obligation_set);
    push_optional_artifact_component(&mut payload, "typed_problem", parts.typed_problem.as_ref());
    push_optional_artifact_component(&mut payload, "smt_rendering", parts.smt_rendering.as_ref());
    push_optional_artifact_component(&mut payload, "solver_binary", parts.solver_binary.as_ref());
    push_optional_artifact_component(
        &mut payload,
        "solver_transcript",
        parts.solver_transcript.as_ref(),
    );
    push_optional_artifact_component(&mut payload, "replay_log", parts.replay_log.as_ref());
    push_optional_artifact_component(&mut payload, "checked_report", parts.checked_report.as_ref());
    push_artifact_vec_component(&mut payload, "invariants", &parts.invariants);
    push_artifact_vec_component(&mut payload, "counterexamples", &parts.counterexamples);
    push_artifact_component(&mut payload, "options", &parts.options);
    push_artifact_component(&mut payload, "resource_limits", &parts.resource_limits);
    EvidenceHash::sha256_bytes(payload.as_bytes())
}

fn push_cache_component(payload: &mut String, key: &str, value: &str) {
    payload.push_str(&key.len().to_string());
    payload.push(':');
    payload.push_str(key);
    payload.push('=');
    payload.push_str(&value.len().to_string());
    payload.push(':');
    payload.push_str(value);
    payload.push(';');
}

fn push_artifact_component(payload: &mut String, role: &str, artifact: &FullVerificationArtifact) {
    push_cache_component(payload, role, "present");
    push_cache_component(payload, &format!("{role}.kind"), artifact_kind_cache_name(artifact.kind));
    push_cache_component(payload, &format!("{role}.label"), &artifact.label);
    if let Some(digest) = &artifact.digest {
        push_cache_component(payload, &format!("{role}.digest.algorithm"), &digest.algorithm);
        push_cache_component(payload, &format!("{role}.digest.value"), &digest.value);
    } else {
        push_cache_component(payload, &format!("{role}.digest"), "missing");
    }
    if let Some(byte_len) = artifact.byte_len {
        push_cache_component(payload, &format!("{role}.byte_len"), &byte_len.to_string());
    } else {
        push_cache_component(payload, &format!("{role}.byte_len"), "missing");
    }
}

fn push_optional_artifact_component(
    payload: &mut String,
    role: &str,
    artifact: Option<&FullVerificationArtifact>,
) {
    if let Some(artifact) = artifact {
        push_artifact_component(payload, role, artifact);
    } else {
        push_cache_component(payload, role, "absent");
    }
}

fn push_artifact_vec_component(
    payload: &mut String,
    role: &str,
    artifacts: &[FullVerificationArtifact],
) {
    push_cache_component(payload, &format!("{role}.len"), &artifacts.len().to_string());
    for (idx, artifact) in artifacts.iter().enumerate() {
        push_artifact_component(payload, &format!("{role}.{idx}"), artifact);
    }
}

fn artifact_kind_cache_name(kind: FullVerificationArtifactKind) -> &'static str {
    match kind {
        FullVerificationArtifactKind::CompilerInput => "compiler_input",
        FullVerificationArtifactKind::ObligationSet => "obligation_set",
        FullVerificationArtifactKind::TypedBmcProblem => "typed_bmc_problem",
        FullVerificationArtifactKind::TypedChcProblem => "typed_chc_problem",
        FullVerificationArtifactKind::SmtRendering => "smt_rendering",
        FullVerificationArtifactKind::SolverBinary => "solver_binary",
        FullVerificationArtifactKind::VerificationOptions => "verification_options",
        FullVerificationArtifactKind::ResourceLimits => "resource_limits",
        FullVerificationArtifactKind::NormalizedInput => "normalized_input",
        FullVerificationArtifactKind::SolverTranscript => "solver_transcript",
        FullVerificationArtifactKind::PdrInvariantModel => "pdr_invariant_model",
        FullVerificationArtifactKind::ReplayLog => "replay_log",
        FullVerificationArtifactKind::CheckedProofReport => "checked_proof_report",
        FullVerificationArtifactKind::CounterexampleTrace => "counterexample_trace",
        FullVerificationArtifactKind::DiagnosticTrace => "diagnostic_trace",
        FullVerificationArtifactKind::EvidenceManifest => "evidence_manifest",
    }
}

fn require_artifact_digest(
    role: &str,
    artifact: &FullVerificationArtifact,
    errors: &mut Vec<String>,
) {
    match &artifact.digest {
        Some(digest) if digest.is_canonical_sha256() => {}
        Some(_) => errors.push(format!("{role} digest metadata is not canonical SHA-256")),
        None => errors.push(format!("{role} artifact is missing digest metadata")),
    }
}

fn optional_artifact_digest(
    role: &str,
    artifact: Option<&FullVerificationArtifact>,
    errors: &mut Vec<String>,
) {
    if let Some(artifact) = artifact {
        require_artifact_digest(role, artifact, errors);
    }
}

/// Native full-proof evidence.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum FullProofEvidence {
    ChcPdr(ChcPdrProofEvidence),
}

/// Native full-verification verdict.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[allow(clippy::large_enum_variant)]
pub enum FullVerificationVerdict {
    Proved {
        evidence: FullProofEvidence,
    },
    Failed {
        #[serde(deserialize_with = "deserialize_bounded_manifest_artifacts")]
        counterexample_artifacts: Vec<FullVerificationArtifact>,
    },
    Unknown {
        reason: String,
    },
    DiagnosticOnly {
        evidence: DiagnosticOnlyEvidence,
    },
}

/// Diagnostic-only native evidence that must not be treated as a proof.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DiagnosticOnlyEvidence {
    pub problem_kind: FullVerificationProblemKind,
    pub summary: String,
    #[serde(default, deserialize_with = "deserialize_bounded_manifest_artifacts")]
    pub artifacts: Vec<FullVerificationArtifact>,
}

/// Proof-grade classification for a native verdict.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum ProofGradeVerdict {
    ProofGrade { proof_kind: ChcPdrProofKind, normalized_input_hash: EvidenceHash },
    NotProofGrade { problem_kind: Option<FullVerificationProblemKind>, reasons: Vec<String> },
}

/// Borrowed proof evidence that has passed trust_mc's proof-grade checks.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AcceptedChcPdrProofEvidence<'a> {
    pub proof: &'a ChcPdrProofEvidence,
    pub proof_kind: ChcPdrProofKind,
    pub normalized_input_hash: &'a EvidenceHash,
    pub native_metadata: Option<&'a NativeTypedChcObligationMetadata>,
}

/// Borrowed CHC/PDR candidate whose content-addressed structure is valid.
///
/// This type deliberately carries no proof authority. In particular, it says
/// nothing about whether the caller-provided transcript, replay log, or checked
/// report resulted from a real execution. A private derivation/replay boundary
/// must grant authority separately.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ValidatedChcPdrCandidateEvidence<'a> {
    pub proof: &'a ChcPdrProofEvidence,
    pub proof_kind: ChcPdrProofKind,
    pub normalized_input_hash: &'a EvidenceHash,
    pub native_metadata: Option<&'a NativeTypedChcObligationMetadata>,
}

/// Fail-closed reason returned when proof evidence is not admissible.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProofEvidenceRejection {
    pub problem_kind: Option<FullVerificationProblemKind>,
    pub reasons: Vec<String>,
}

impl ProofEvidenceRejection {
    fn new(problem_kind: Option<FullVerificationProblemKind>, reasons: Vec<String>) -> Self {
        Self { problem_kind, reasons }
    }
}

impl std::fmt::Display for ProofEvidenceRejection {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "proof evidence rejected")?;
        if let Some(problem_kind) = self.problem_kind {
            write!(f, " for {problem_kind:?}")?;
        }
        if !self.reasons.is_empty() {
            write!(f, ": {}", self.reasons.join("; "))?;
        }
        Ok(())
    }
}

impl std::error::Error for ProofEvidenceRejection {}

/// Classify a native verdict for proof-grade publication.
#[must_use]
pub fn classify_proof_grade_verdict(verdict: &FullVerificationVerdict) -> ProofGradeVerdict {
    match verdict {
        FullVerificationVerdict::Proved { evidence: FullProofEvidence::ChcPdr(proof) } => {
            classify_chc_pdr_proof(proof)
        }
        FullVerificationVerdict::Failed { .. } => ProofGradeVerdict::NotProofGrade {
            problem_kind: Some(FullVerificationProblemKind::ChcPdr),
            reasons: vec!["counterexample evidence is not a proof".to_string()],
        },
        FullVerificationVerdict::Unknown { reason } => ProofGradeVerdict::NotProofGrade {
            problem_kind: Some(FullVerificationProblemKind::ChcPdr),
            reasons: vec![format!("solver did not prove the obligation: {reason}")],
        },
        FullVerificationVerdict::DiagnosticOnly { evidence } => {
            let mut reasons = vec!["diagnostic-only evidence is not proof-grade".to_string()];
            if evidence.problem_kind == FullVerificationProblemKind::DiagnosticBmc {
                reasons.push(
                    "diagnostic BMC is bounded evidence and must not claim proof".to_string(),
                );
            }
            ProofGradeVerdict::NotProofGrade { problem_kind: Some(evidence.problem_kind), reasons }
        }
    }
}

/// Return typed CHC/PDR proof evidence only after proof-grade validation.
///
/// This is the stable data-structure API for consumers that need proof
/// artifacts directly instead of parsing driver text or SMT-LIB comments.
pub fn accepted_chc_pdr_proof(
    verdict: &FullVerificationVerdict,
) -> Result<AcceptedChcPdrProofEvidence<'_>, ProofEvidenceRejection> {
    let FullVerificationVerdict::Proved { evidence: FullProofEvidence::ChcPdr(proof) } = verdict
    else {
        return Err(proof_grade_rejection(classify_proof_grade_verdict(verdict)));
    };

    match classify_chc_pdr_proof(proof) {
        ProofGradeVerdict::ProofGrade { proof_kind, normalized_input_hash: _ } => {
            Ok(AcceptedChcPdrProofEvidence {
                proof,
                proof_kind,
                normalized_input_hash: &proof.obligation.normalized_input_hash,
                native_metadata: proof.obligation.native_metadata.as_ref(),
            })
        }
        rejected => Err(proof_grade_rejection(rejected)),
    }
}

/// Return accepted CHC/PDR proof evidence that is bound to native trust_ir metadata.
///
/// This is stricter than [`accepted_chc_pdr_proof`]: tRust-style consumers get
/// `Ok` only when the proof is proof-grade and its typed native bundle metadata
/// is present and matches the accepted obligation id.
pub fn accepted_native_typed_chc_pdr_proof(
    verdict: &FullVerificationVerdict,
) -> Result<AcceptedChcPdrProofEvidence<'_>, ProofEvidenceRejection> {
    let accepted = accepted_chc_pdr_proof(verdict)?;
    let Some(metadata) = accepted.native_metadata else {
        return Err(ProofEvidenceRejection::new(
            Some(FullVerificationProblemKind::ChcPdr),
            vec!["missing native typed CHC obligation metadata".to_string()],
        ));
    };

    metadata.validate_for_obligation_id(&accepted.proof.obligation.obligation_id).map_err(
        |reasons| ProofEvidenceRejection::new(Some(FullVerificationProblemKind::ChcPdr), reasons),
    )?;

    Ok(accepted)
}

/// Validate a serialized CHC/PDR candidate's content-addressed structure.
///
/// Successful validation is not proof-grade admission. This function exists so
/// a private consumer can validate transport structure before independently
/// deriving or replaying the exact obligation.
pub fn validated_chc_pdr_candidate(
    verdict: &FullVerificationVerdict,
) -> Result<ValidatedChcPdrCandidateEvidence<'_>, ProofEvidenceRejection> {
    let FullVerificationVerdict::Proved { evidence: FullProofEvidence::ChcPdr(proof) } = verdict
    else {
        return Err(proof_grade_rejection(classify_proof_grade_verdict(verdict)));
    };

    let mut reasons = missing_chc_pdr_candidate_metadata(proof);
    if !reasons.is_empty() {
        reasons.sort();
        reasons.dedup();
        return Err(ProofEvidenceRejection::new(
            Some(FullVerificationProblemKind::ChcPdr),
            reasons,
        ));
    }

    Ok(ValidatedChcPdrCandidateEvidence {
        proof,
        proof_kind: proof.kind,
        normalized_input_hash: &proof.obligation.normalized_input_hash,
        native_metadata: proof.obligation.native_metadata.as_ref(),
    })
}

/// Validate a serialized CHC/PDR candidate and its native trust_ir identity.
///
/// Like [`validated_chc_pdr_candidate`], this grants no proof authority. It only
/// establishes that the candidate is structurally complete and bound to valid
/// native metadata.
pub fn validated_native_typed_chc_pdr_candidate(
    verdict: &FullVerificationVerdict,
) -> Result<ValidatedChcPdrCandidateEvidence<'_>, ProofEvidenceRejection> {
    let candidate = validated_chc_pdr_candidate(verdict)?;
    let Some(metadata) = candidate.native_metadata else {
        return Err(ProofEvidenceRejection::new(
            Some(FullVerificationProblemKind::ChcPdr),
            vec!["missing native typed CHC obligation metadata".to_string()],
        ));
    };

    metadata.validate_for_obligation_id(&candidate.proof.obligation.obligation_id).map_err(
        |reasons| ProofEvidenceRejection::new(Some(FullVerificationProblemKind::ChcPdr), reasons),
    )?;

    Ok(candidate)
}

fn proof_grade_rejection(verdict: ProofGradeVerdict) -> ProofEvidenceRejection {
    match verdict {
        ProofGradeVerdict::ProofGrade { .. } => ProofEvidenceRejection::new(
            Some(FullVerificationProblemKind::ChcPdr),
            vec!["proof-grade verdict did not contain CHC/PDR proof evidence".to_string()],
        ),
        ProofGradeVerdict::NotProofGrade { problem_kind, reasons } => {
            ProofEvidenceRejection::new(problem_kind, reasons)
        }
    }
}

fn classify_chc_pdr_proof(proof: &ChcPdrProofEvidence) -> ProofGradeVerdict {
    let mut reasons = missing_chc_pdr_proof_grade_metadata(proof);
    if reasons.is_empty() {
        ProofGradeVerdict::ProofGrade {
            proof_kind: proof.kind,
            normalized_input_hash: proof.obligation.normalized_input_hash.clone(),
        }
    } else {
        reasons.sort();
        ProofGradeVerdict::NotProofGrade {
            problem_kind: Some(FullVerificationProblemKind::ChcPdr),
            reasons,
        }
    }
}

fn missing_chc_pdr_proof_grade_metadata(proof: &ChcPdrProofEvidence) -> Vec<String> {
    let mut missing = missing_chc_pdr_candidate_metadata(proof);
    missing.push(match proof.kind {
        ChcPdrProofKind::ChcValidity => CHC_VALIDITY_FRESH_CONSUMER_REPLAY_REQUIRED.to_string(),
        ChcPdrProofKind::PdrInvariant => PDR_INVARIANT_FRESH_CONSUMER_REPLAY_REQUIRED.to_string(),
    });
    missing
}

fn missing_chc_pdr_candidate_metadata(proof: &ChcPdrProofEvidence) -> Vec<String> {
    let mut missing = Vec::new();
    if proof.obligation.origin != ObligationOrigin::MirDerived {
        missing.push("obligation is a router placeholder, not MIR-derived".to_string());
    }
    if proof.obligation.normalized_input.trim().is_empty() {
        missing.push("normalized MIR-derived CHC/PDR input is empty".to_string());
    }
    if proof.stats.relation_count == 0 || proof.stats.clause_count == 0 {
        missing.push(
            "CHC/PDR proof stats must include nonzero relation and clause counts".to_string(),
        );
    }
    if EvidenceHash::sha256_bytes(proof.obligation.normalized_input.as_bytes())
        != proof.obligation.normalized_input_hash
    {
        missing.push("normalized input hash does not match normalized input payload".to_string());
    }
    if proof.metadata.normalized_input_hash.as_ref()
        != Some(&proof.obligation.normalized_input_hash)
    {
        missing
            .push("missing normalized input hash bound to the MIR-derived obligation".to_string());
    }
    if proof.metadata.producer.as_deref().is_none_or(|producer| producer.trim().is_empty()) {
        missing.push("missing proof evidence producer identity".to_string());
    }
    if !has_matching_artifact(
        proof,
        FullVerificationArtifactKind::NormalizedInput,
        std::slice::from_ref(&proof.obligation.normalized_input_hash),
    ) {
        missing.push("missing normalized input artifact matching obligation hash".to_string());
    }
    require_hashes("solver transcript", &proof.metadata.transcript_hashes, &mut missing);
    require_hashes("replay log", &proof.metadata.replay_log_hashes, &mut missing);
    require_hashes("checked proof report", &proof.metadata.checked_report_hashes, &mut missing);
    match proof.metadata.replay_check_status {
        Some(ProofReplayCheckStatus {
            replay: ProofReplayStatus::Unknown,
            check: ProofCheckStatus::Unknown,
        }) => {}
        Some(status) => missing.push(format!(
            "public candidate replay/check status must be Unknown/Unknown, got {:?}/{:?}",
            status.replay, status.check
        )),
        None => missing.push("missing replay/check status metadata".to_string()),
    }
    if !has_matching_artifact(
        proof,
        FullVerificationArtifactKind::SolverTranscript,
        &proof.metadata.transcript_hashes,
    ) {
        missing.push("missing solver transcript artifact matching transcript metadata".to_string());
    }
    if !has_matching_artifact(
        proof,
        FullVerificationArtifactKind::ReplayLog,
        &proof.metadata.replay_log_hashes,
    ) {
        missing.push("missing replay log artifact matching replay metadata".to_string());
    }
    if !has_matching_artifact(
        proof,
        FullVerificationArtifactKind::CheckedProofReport,
        &proof.metadata.checked_report_hashes,
    ) {
        missing.push("missing checked proof report artifact matching report metadata".to_string());
    }
    validate_linked_proof_artifacts(proof, &mut missing);
    if proof.kind == ChcPdrProofKind::PdrInvariant {
        if proof.invariant_count == 0 {
            missing.push("PDR invariant proof declares zero predicate interpretations".to_string());
        }
        if !has_digest_artifact(proof, FullVerificationArtifactKind::PdrInvariantModel) {
            missing.push("PDR invariant proof is missing invariant evidence".to_string());
        }
    } else if proof
        .artifacts
        .iter()
        .any(|artifact| artifact.kind == FullVerificationArtifactKind::PdrInvariantModel)
    {
        missing.push("CHC validity proof must not carry a PDR invariant model".to_string());
    }
    missing
}

fn require_hashes(label: &str, hashes: &[EvidenceHash], missing: &mut Vec<String>) {
    if hashes.is_empty() {
        missing.push(format!("missing {label} digest metadata"));
    } else if hashes.len() != 1 {
        missing.push(format!(
            "{label} digest metadata must identify exactly one artifact, got {}",
            hashes.len()
        ));
    } else if hashes.iter().any(|hash| !hash.is_canonical_sha256()) {
        missing.push(format!("{label} digest metadata is not canonical SHA-256"));
    }
}

fn has_matching_artifact(
    proof: &ChcPdrProofEvidence,
    kind: FullVerificationArtifactKind,
    hashes: &[EvidenceHash],
) -> bool {
    hashes.len() == 1 && matching_artifacts(proof, kind, &hashes[0]).count() == 1
}

fn matching_artifacts<'a>(
    proof: &'a ChcPdrProofEvidence,
    kind: FullVerificationArtifactKind,
    digest: &'a EvidenceHash,
) -> impl Iterator<Item = &'a FullVerificationArtifact> {
    proof
        .artifacts
        .iter()
        .filter(move |artifact| artifact.kind == kind && artifact.digest.as_ref() == Some(digest))
}

fn validate_linked_proof_artifacts(proof: &ChcPdrProofEvidence, missing: &mut Vec<String>) {
    let mut duplicate_required_role = false;
    for (label, kind) in [
        ("normalized input", FullVerificationArtifactKind::NormalizedInput),
        ("solver transcript", FullVerificationArtifactKind::SolverTranscript),
        ("replay log", FullVerificationArtifactKind::ReplayLog),
        ("checked proof report", FullVerificationArtifactKind::CheckedProofReport),
    ] {
        let count = proof.artifacts.iter().filter(|artifact| artifact.kind == kind).count();
        if count != 1 {
            missing
                .push(format!("proof artifact role {label} must occur exactly once, got {count}"));
            duplicate_required_role = true;
        }
    }
    if proof.kind == ChcPdrProofKind::PdrInvariant {
        let count = proof
            .artifacts
            .iter()
            .filter(|artifact| artifact.kind == FullVerificationArtifactKind::PdrInvariantModel)
            .count();
        if count != 1 {
            missing.push(format!(
                "proof artifact role PDR invariant model must occur exactly once, got {count}"
            ));
            duplicate_required_role = true;
        }
    }
    if duplicate_required_role {
        return;
    }

    let Some(input) = exactly_one_materialized_artifact(
        proof,
        FullVerificationArtifactKind::NormalizedInput,
        &proof.obligation.normalized_input_hash,
    ) else {
        missing.push("normalized input artifact lacks unique exact retained bytes".to_string());
        return;
    };
    let [transcript_hash] = proof.metadata.transcript_hashes.as_slice() else {
        return;
    };
    let [replay_hash] = proof.metadata.replay_log_hashes.as_slice() else {
        return;
    };
    let [checked_hash] = proof.metadata.checked_report_hashes.as_slice() else {
        return;
    };
    let Some(transcript) = exactly_one_materialized_artifact(
        proof,
        FullVerificationArtifactKind::SolverTranscript,
        transcript_hash,
    ) else {
        missing.push("solver transcript lacks unique nonempty exact retained bytes".to_string());
        return;
    };
    let Some(replay) = exactly_one_materialized_artifact(
        proof,
        FullVerificationArtifactKind::ReplayLog,
        replay_hash,
    ) else {
        missing.push("replay log lacks unique nonempty exact retained bytes".to_string());
        return;
    };
    let Some(checked) = exactly_one_materialized_artifact(
        proof,
        FullVerificationArtifactKind::CheckedProofReport,
        checked_hash,
    ) else {
        missing.push("checked proof report lacks unique nonempty exact retained bytes".to_string());
        return;
    };
    let invariant = if proof.kind == ChcPdrProofKind::PdrInvariant {
        let Some(artifact) = proof
            .artifacts
            .iter()
            .find(|artifact| artifact.kind == FullVerificationArtifactKind::PdrInvariantModel)
        else {
            return;
        };
        if artifact.materialized_bytes().is_none() || artifact.digest.is_none() {
            missing
                .push("PDR invariant model lacks unique nonempty exact retained bytes".to_string());
            return;
        }
        Some(artifact)
    } else {
        None
    };

    if input.materialized_bytes().is_some_and(<[u8]>::is_empty) {
        missing.push("normalized input artifact materialization is empty".to_string());
    }
    for (label, artifact) in [
        ("solver transcript", transcript),
        ("replay log", replay),
        ("checked proof report", checked),
    ] {
        if artifact.materialized_bytes().is_some_and(<[u8]>::is_empty) {
            missing.push(format!("{label} artifact materialization is empty"));
        }
    }
    if invariant.is_some_and(|artifact| artifact.materialized_bytes().is_some_and(<[u8]>::is_empty))
    {
        missing.push("PDR invariant model artifact materialization is empty".to_string());
    }

    let invariant_hash = invariant.and_then(|artifact| artifact.digest.as_ref());
    let expected_binding = linked_proof_binding_id(
        proof.kind,
        &proof.obligation,
        transcript_hash,
        replay_hash,
        checked_hash,
        invariant_hash,
        &proof.stats,
        proof.invariant_count,
    );
    for (label, artifact) in [
        ("normalized input", input),
        ("solver transcript", transcript),
        ("replay log", replay),
        ("checked proof report", checked),
    ] {
        if artifact.proof_binding_id() != Some(&expected_binding) {
            missing.push(format!(
                "{label} artifact is missing the content-addressed proof-set binding"
            ));
        }
    }
    if let Some(invariant) = invariant {
        if invariant.proof_binding_id() != Some(&expected_binding) {
            missing.push(
                "PDR invariant model artifact is missing the content-addressed proof-set binding"
                    .to_string(),
            );
        }
    }

    require_exact_artifact_references("normalized input", input, &[], missing);
    require_exact_artifact_references(
        "solver transcript",
        transcript,
        &[FullVerificationArtifactReference::new(
            FullVerificationArtifactKind::NormalizedInput,
            proof.obligation.normalized_input_hash.clone(),
        )],
        missing,
    );
    if let Some(invariant) = invariant {
        require_exact_artifact_references(
            "PDR invariant model",
            invariant,
            &[FullVerificationArtifactReference::new(
                FullVerificationArtifactKind::NormalizedInput,
                proof.obligation.normalized_input_hash.clone(),
            )],
            missing,
        );
    }
    let mut replay_references = vec![FullVerificationArtifactReference::new(
        FullVerificationArtifactKind::SolverTranscript,
        transcript_hash.clone(),
    )];
    if let Some(invariant_hash) = invariant_hash {
        replay_references.push(FullVerificationArtifactReference::new(
            FullVerificationArtifactKind::PdrInvariantModel,
            invariant_hash.clone(),
        ));
    }
    require_exact_artifact_references("replay log", replay, &replay_references, missing);
    let mut checked_references = vec![
        FullVerificationArtifactReference::new(
            FullVerificationArtifactKind::SolverTranscript,
            transcript_hash.clone(),
        ),
        FullVerificationArtifactReference::new(
            FullVerificationArtifactKind::ReplayLog,
            replay_hash.clone(),
        ),
    ];
    if let Some(invariant_hash) = invariant_hash {
        checked_references.push(FullVerificationArtifactReference::new(
            FullVerificationArtifactKind::PdrInvariantModel,
            invariant_hash.clone(),
        ));
    }
    require_exact_artifact_references(
        "checked proof report",
        checked,
        &checked_references,
        missing,
    );
}

fn exactly_one_materialized_artifact<'a>(
    proof: &'a ChcPdrProofEvidence,
    kind: FullVerificationArtifactKind,
    digest: &'a EvidenceHash,
) -> Option<&'a FullVerificationArtifact> {
    let mut matches = matching_artifacts(proof, kind, digest)
        .filter(|artifact| artifact.materialized_bytes().is_some());
    let artifact = matches.next()?;
    matches.next().is_none().then_some(artifact)
}

fn require_exact_artifact_references(
    label: &str,
    artifact: &FullVerificationArtifact,
    expected: &[FullVerificationArtifactReference],
    missing: &mut Vec<String>,
) {
    let actual = artifact.referenced_artifacts();
    if actual.len() != expected.len()
        || expected.iter().any(|reference| !actual.contains(reference))
    {
        missing.push(format!(
            "{label} artifact references do not match the exact typed proof relationship"
        ));
    }
}

fn has_digest_artifact(proof: &ChcPdrProofEvidence, kind: FullVerificationArtifactKind) -> bool {
    proof.artifacts.iter().any(|artifact| artifact.kind == kind && artifact.digest.is_some())
}

fn artifact_digest_vec(artifact: &FullVerificationArtifact) -> Vec<EvidenceHash> {
    artifact.digest.iter().cloned().collect()
}

#[cfg(test)]
#[path = "evidence_tests.rs"]
mod tests;
