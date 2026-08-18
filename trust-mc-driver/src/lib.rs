// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Public library facade for native trust-mc driver integration.
//!
//! The existing command-line driver still owns production solver orchestration.
//! This library target exposes the first fail-closed native solve API shape so
//! callers can compile against typed requests, results, and proof provenance.

// Cargo features are package-wide, so enabling the `cli` feature for the
// trust-mc-driver binary also presents these binary-only dependencies to this
// library target. Mark them intentionally used here until Cargo grows true
// per-binary dependency tables or the CLI moves to its own package.
#[cfg(feature = "cli")]
use anyhow as _;
#[cfg(all(feature = "cli", feature = "ay-memory-limit"))]
use ay_sys as _;
#[cfg(feature = "cli")]
use cargo_metadata as _;
#[cfg(feature = "cli")]
use chrono as _;
#[cfg(feature = "cli")]
use clap as _;
#[cfg(feature = "cli")]
use comfy_table as _;
#[cfg(feature = "cli")]
use console as _;
#[cfg(all(feature = "cli", unix))]
use libc as _;
#[cfg(feature = "cli")]
use once_cell as _;
#[cfg(feature = "cli")]
use pathdiff as _;
#[cfg(feature = "cli")]
use rayon as _;
#[cfg(feature = "cli")]
use regex as _;
#[cfg(feature = "cli")]
use rustc_demangle as _;
#[cfg(feature = "cli")]
use strum as _;
#[cfg(feature = "cli")]
use strum_macros as _;
#[cfg(feature = "cli")]
use tempfile as _;
#[cfg(feature = "cli")]
use time as _;
#[cfg(feature = "cli")]
use to_markdown_table as _;
#[cfg(feature = "cli")]
use toml as _;
#[cfg(feature = "cli")]
use tracing as _;
#[cfg(feature = "cli")]
use tracing_subscriber as _;
#[cfg(feature = "cli")]
use trust_mc_metadata as _;
#[cfg(feature = "cli")]
use trust_mc_trust_vc_ingest as _;
#[cfg(feature = "cli")]
use which as _;

pub mod native;

// CHC auto-invariant candidate extraction — the single implementation behind
// the CLI `--ay-chc-auto-invariants` lane AND the library-only native
// typed-CHC runner (which the compiler drives). See the module doc.
#[cfg(feature = "ay-chc-native")]
pub(crate) mod chc_auto_hints;

#[cfg(feature = "ay-chc-native")]
pub(crate) mod direct_smt_cex;

// Trust: program-space differential soundness oracle — generates trust-ir programs,
// runs the REAL discharge encoding (translate -> lower -> acyclic decision) and an
// independent ground-truth panic oracle (the trust-ir interpreter), and asserts no
// false PROVE across the generated space. Apex Step A (empirical scaffold the clean
// soundness proof replaces). Test-only; needs the trust-ir bundle for the builder +
// interpreter.
#[cfg(all(test, feature = "native-trust-ir-bundle"))]
mod soundness_oracle;

pub use native::{
    AuthorizedNativeTypedChcPdrProof, NativeEncodedArtifact, NativeOperation, NativeProofMode,
    NativeProofProvenance, NativeSolveError, NativeSolveRequest, NativeSolveResult,
    NativeSolveUnsupported, NativeSolvedArtifact, NativeSolverVerdict,
    NativeTypedChcPdrNormalizedInput, NativeTypedChcPdrProofTransport, NativeTypedChcPdrRunner,
    NativeTypedProofArtifactRef, NativeTypedProofStatus, NativeTypedProofStrength, NativeVcKind,
    TypedChcPdrFullVerification, TypedChcPdrRoute, classify_native_full_verification_verdict,
    is_proof_grade_native_full_verification_verdict, normalized_typed_chc_pdr_input, solve_native,
    solve_typed_chc_pdr, solve_typed_chc_pdr_full_verification,
    solve_typed_chc_pdr_native_proof_grade, typed_chc_pdr_semantic_config,
    typed_chc_pdr_semantic_config_sha256,
};

#[cfg(feature = "ay-chc-native")]
pub use native::independently_replay_typed_chc_pdr_refutation_witness;

#[cfg(feature = "native-trust-ir-bundle")]
pub use native::{
    NativeTrustIrChcPdrBundleEvidence, NativeTrustIrChcPdrEvidence, NativeTrustIrChcPdrNotProved,
    NativeTrustIrChcPdrRefuted, NativeTrustIrChcPdrRunner,
};
