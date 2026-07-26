// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// trust_mc_core is solver IR, not rustc query state.
#![allow(rustc::default_hash_types, rustc::potential_query_instability)]

//! trust_mc Core - Abstract Verification Condition IR
//!
//! This crate provides solver-independent verification condition (VC) containers
//! that separate "what needs to be proven" from "how it is emitted".
//!
//! ## Overview
//!
//! The IR supports two verification shapes:
//!
//! - **BMC (Bounded Model Checking)**: SAT iff a counterexample exists (bounded/acyclic/unrolled)
//! - **CHC (Constrained Horn Clauses)**: Reachability in CHC system (unbounded/inductive)
//!
//! The MIR front-end produces these containers, and backend emitters serialize them
//! to SMT-LIB2 or directly to solver APIs.
//!
//! ## Architecture
//!
//! ```text
//! ┌─────────────────────────────────────────────────────────────────────┐
//! │                         MIR Front-end                               │
//! └──────────────────────────┬──────────────────────────────────────────┘
//!                            │
//!                            ▼
//! ┌─────────────────────────────────────────────────────────────────────┐
//! │                    trust_mc_core (this crate)                           │
//! │                                                                     │
//! │   BmcVc (Phase 2: env+phi merge)                                    │
//! │   ChcVc (Phase 3: per-block relations)                              │
//! │                                                                     │
//! └──────────────────────────┬──────────────────────────────────────────┘
//!                            │
//!                            ▼
//! ┌─────────────────────────────────────────────────────────────────────┐
//! │                    Backend Emitters                                  │
//! │   • SMT-LIB2 (AY, Z3)                                                │
//! │   • Direct AY API (ay-direct feature)                                │
//! └─────────────────────────────────────────────────────────────────────┘
//! ```
//!
//! ## Design Reference
//!
//! Unified VC IR provides a common intermediate representation for both BMC and CHC backends.

pub mod artifact;
pub mod bmc;
pub mod chc;
pub mod chc_api;
pub mod chc_const_prop;
pub mod chc_optimize;
pub mod constraints;
pub mod decl;
pub mod evidence;
pub mod full_verifier;
pub mod ident;
pub mod violation;

// Re-export main types at crate root
pub use artifact::{
    ArtifactMetadata, CURRENT_VERSION, LoopInvariantHint, PropertyMetadata, UnsoundnessCounters,
    VcArtifact, VerificationMode,
};
pub use bmc::{BmcQuery, BmcVc};
pub use chc::{ChcProperty, ChcQuery, ChcVc, RelationApp, RelationDecl, Rule, RuleBody, VarDecl};
pub use chc_api::{
    ChcPdrCexVerification, ChcPdrEncodingConcreteness, ChcPdrEngine, ChcPdrRefutationWitness,
    ChcPdrSolveOptions, ChcPdrSolveOutcome, ChcPdrSolveRequest, ChcPdrSolveStatus,
    MirChcPdrObligation, MirChcPdrObligationError,
};
pub use constraints::Constraints;
pub use decl::Decl;
pub use evidence::{
    AcceptedChcPdrProofEvidence, CHC_VALIDITY_FRESH_CONSUMER_REPLAY_REQUIRED, ChcPdrProofEvidence,
    ChcPdrProofKind, ChcPdrStats, ContentAddressedEvidenceManifest,
    ContentAddressedEvidenceManifestParts, DiagnosticOnlyEvidence, EvidenceHash, EvidenceHashError,
    FullProofEvidence, FullProofEvidenceMetadata, FullVerificationArtifact,
    FullVerificationArtifactKind, FullVerificationArtifactMaterialization,
    FullVerificationArtifactMaterializationError, FullVerificationArtifactReference,
    FullVerificationCacheKey, FullVerificationCacheKeyParts, FullVerificationProblemKind,
    FullVerificationVerdict, MAX_FULL_VERIFICATION_ARTIFACT_MATERIALIZATION_BYTES,
    MirDerivedChcPdrObligation, MirObligationKind, NativeArtifactDigest, NativeCompilerFactCounts,
    NativeCompilerFactKind, NativeCompilerFactReference, NativeObligationCauseMetadata,
    NativeObligationCompilerFacts, NativeReplayAtomKindMetadata, NativeReplayAtomMetadata,
    NativeReplayContextMetadata, NativeReplayIdentityMetadata, NativeSourceSpanMetadata,
    NativeTypedChcObligationMetadata, NativeUnsupportedModeMetadata, ObligationOrigin,
    PDR_INVARIANT_FRESH_CONSUMER_REPLAY_REQUIRED, ProofArtifactBindingId, ProofCheckStatus,
    ProofEvidenceRejection, ProofGradeVerdict, ProofReplayCheckStatus, ProofReplayStatus,
    ValidatedChcPdrCandidateEvidence, accepted_chc_pdr_proof, accepted_native_typed_chc_pdr_proof,
    classify_proof_grade_verdict, normalize_chc_pdr_input, validated_chc_pdr_candidate,
    validated_native_typed_chc_pdr_candidate,
};
pub use ident::{HarnessId, PropertyId, SourceLocation};
pub use violation::{PropertyKind, Violation};
