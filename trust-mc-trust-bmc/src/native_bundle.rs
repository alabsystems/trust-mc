// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Typed native trust_ir request-bundle consumption for trust_mc.
//!
//! This module is the in-process boundary for tRust-produced
//! `NativeVerificationBundle` values. It selects typed
//! `NativeVerificationRequest::TrustMc` entries directly instead of routing by
//! adapter-name strings or ad hoc JSON payloads.
//!
//! Part of #4337 and alabsystems/tRust#1151.

use thiserror::Error;
use trust_ir::{
    FuncId, NativeAdapterInput, NativeBundleProducer, NativeCompilerFactRef, NativeCompilerFacts,
    NativeObligationCause, NativeReplayAtomKind, NativeReplayContext, NativeRequestId,
    NativeRequestProvenance, NativeUnsupportedModeReason, NativeVerificationBundle,
    NativeVerificationBundleError, NativeVerificationRequest, ObligationKind, ProofDigest, ProofId,
    ProofLineageId, ProofReplayIdentity, SourceSpan, TrustMcVerificationMode,
};
use trust_mc_core::{
    BmcVc, MirChcPdrObligation, MirChcPdrObligationError, MirObligationKind, NativeArtifactDigest,
    NativeCompilerFactCounts, NativeCompilerFactKind, NativeCompilerFactReference,
    NativeObligationCauseMetadata, NativeObligationCompilerFacts, NativeReplayAtomKindMetadata,
    NativeReplayAtomMetadata, NativeReplayContextMetadata, NativeReplayIdentityMetadata,
    NativeSourceSpanMetadata, NativeTypedChcObligationMetadata, NativeUnsupportedModeMetadata,
};

use crate::translate::{TranslateOptions, trust_ir_function_to_bmc_vc};
use crate::translate_chc::{TrustIrChcDiagnostic, trust_ir_function_to_chc_translation_output};

/// BMC VC generated for one typed native trust_mc request.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct NativeTrustMcBmcVc {
    /// Stable request id from the native verification bundle.
    pub request_id: NativeRequestId,
    /// trust_ir function requested by the native trust_mc request.
    pub function: FuncId,
    /// Proof obligations carried by the typed request.
    pub obligations: Vec<ProofId>,
    /// Proof-lineage roots carried by the typed request.
    pub lineage_roots: Vec<ProofLineageId>,
    /// Generated trust_mc BMC verification condition.
    pub vc: BmcVc,
}

/// CHC/PDR obligation generated for one typed native trust_mc request.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct NativeTrustMcChcPdrObligation {
    /// Stable request id from the native verification bundle.
    pub request_id: NativeRequestId,
    /// trust_ir function requested by the native trust_mc request.
    pub function: FuncId,
    /// Proof obligations carried by the typed request.
    pub obligations: Vec<ProofId>,
    /// Proof-lineage roots carried by the typed request.
    pub lineage_roots: Vec<ProofLineageId>,
    /// Generated typed CHC/PDR obligation.
    pub obligation: MirChcPdrObligation,
    /// Typed fail-closed diagnostics emitted while lowering this request.
    pub diagnostics: Vec<TrustIrChcDiagnostic>,
}

/// Errors returned while consuming a native trust_ir request bundle for trust_mc.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
#[non_exhaustive]
pub enum NativeTrustMcBundleError {
    /// Bundle-level validation failed before any trust_mc request was translated.
    #[error("native verification bundle validation failed")]
    InvalidBundle(Vec<NativeVerificationBundleError>),
    /// The bundle was valid, but did not contain a trust_mc request variant.
    #[error("native verification bundle contains no trust_mc requests")]
    NoTrustMcRequests,
    /// The request asks for a trust_mc mode that this BMC translator cannot encode.
    #[error(
        "native trust_mc request {request} mode {mode:?} is not supported by trust_mc-trust-bmc"
    )]
    UnsupportedTrustMcMode { request: NativeRequestId, mode: TrustMcVerificationMode },
    /// Bundle validation should catch this; this variant keeps the direct API
    /// fail-closed if callers bypass validation in future refactors.
    #[error("native trust_mc request {request} references missing function {function}")]
    MissingFunction { request: NativeRequestId, function: FuncId },
    /// The typed trust_ir request translated, but the generated CHC/PDR obligation
    /// failed the proof-shape validation expected by the native solver API.
    #[error("native trust_mc request {request} produced invalid CHC/PDR obligation: {source}")]
    InvalidChcPdrObligation { request: NativeRequestId, source: MirChcPdrObligationError },
}

/// Translate all BMC-capable typed trust_mc requests in a native trust_ir bundle.
///
/// `NativeVerificationBundle::validate` runs first, so requested obligations,
/// lineage roots, and function ids must be structurally bound before trust_mc emits
/// VCs. `TrustMcVerificationMode::Chc` intentionally fails closed here because
/// this crate currently emits `BmcVc`, not a typed `ChcVc`.
pub fn trust_mc_bmc_vcs_from_native_bundle(
    bundle: &NativeVerificationBundle,
    options: &TranslateOptions,
) -> Result<Vec<NativeTrustMcBmcVc>, NativeTrustMcBundleError> {
    bundle.validate().map_err(NativeTrustMcBundleError::InvalidBundle)?;

    let mut saw_trust_mc = false;
    let mut vcs = Vec::new();

    for request in &bundle.requests {
        let NativeVerificationRequest::TrustMc(request) = request else {
            continue;
        };
        saw_trust_mc = true;

        match request.mode {
            TrustMcVerificationMode::BoundedModelCheck => {
                let vc = trust_ir_function_to_bmc_vc(&bundle.module, request.function, options)
                    .ok_or(NativeTrustMcBundleError::MissingFunction {
                        request: request.id,
                        function: request.function,
                    })?;
                vcs.push(NativeTrustMcBmcVc {
                    request_id: request.id,
                    function: request.function,
                    obligations: request.obligations.clone(),
                    lineage_roots: request.lineage_roots.clone(),
                    vc,
                });
            }
            TrustMcVerificationMode::Chc | TrustMcVerificationMode::Pdr => {
                return Err(NativeTrustMcBundleError::UnsupportedTrustMcMode {
                    request: request.id,
                    mode: request.mode,
                });
            }
        }
    }

    if saw_trust_mc { Ok(vcs) } else { Err(NativeTrustMcBundleError::NoTrustMcRequests) }
}

/// Translate all CHC/PDR-capable typed trust_mc requests in a native trust_ir bundle.
///
/// This is the native trust_ir path for `TrustMcVerificationMode::Chc`: it consumes
/// `trust_ir::Module` and `TrustMcNativeRequest` values directly and returns typed
/// `trust_mc_core::MirChcPdrObligation`s for the native CHC/PDR runner.
pub fn trust_mc_chc_pdr_obligations_from_native_bundle(
    bundle: &NativeVerificationBundle,
    options: &TranslateOptions,
) -> Result<Vec<NativeTrustMcChcPdrObligation>, NativeTrustMcBundleError> {
    bundle.validate().map_err(NativeTrustMcBundleError::InvalidBundle)?;

    let mut saw_trust_mc = false;
    let mut obligations = Vec::new();

    for request in &bundle.requests {
        let NativeVerificationRequest::TrustMc(request) = request else {
            continue;
        };
        saw_trust_mc = true;

        match request.mode {
            TrustMcVerificationMode::Chc | TrustMcVerificationMode::Pdr => {
                let function = bundle.module.function_by_id(request.function).ok_or(
                    NativeTrustMcBundleError::MissingFunction {
                        request: request.id,
                        function: request.function,
                    },
                )?;
                let output = trust_ir_function_to_chc_translation_output(
                    &bundle.module,
                    request.function,
                    options,
                )
                .ok_or(NativeTrustMcBundleError::MissingFunction {
                    request: request.id,
                    function: request.function,
                })?;
                let obligation = MirChcPdrObligation::new(
                    native_obligation_id(request.id, &request.obligations),
                    function.name.clone(),
                    native_obligation_kind(&bundle.module, &request.obligations),
                    output.vc,
                )
                .with_native_metadata(
                    native_chc_metadata(
                        bundle,
                        request.id,
                        request.function,
                        request.mode,
                        &request.obligations,
                        &request.lineage_roots,
                        &request.provenance,
                    )
                    // One translator diagnostic is recorded per
                    // `add_unsupported_error` (an unconditionally reachable
                    // error rule from an unmodeled construct). Demote-only:
                    // consumers may use a nonzero count to hold a Refuted
                    // verdict at Unknown, never to mint authority.
                    .with_fail_closed_lowering_site_count(
                        u32::try_from(output.diagnostics.len()).unwrap_or(u32::MAX),
                    )
                    // …and the DISTINCT typed reasons behind that count, so the
                    // demotion message can name the blocking constructs instead
                    // of only counting them. Diagnostic only — the builder
                    // sorts + dedups, and nothing but the message formatter
                    // reads the result.
                    .with_fail_closed_lowering_reasons(
                        output.diagnostics.iter().map(|d| d.reason.label()),
                    ),
                );
                obligation.validate().map_err(|source| {
                    NativeTrustMcBundleError::InvalidChcPdrObligation {
                        request: request.id,
                        source,
                    }
                })?;
                obligations.push(NativeTrustMcChcPdrObligation {
                    request_id: request.id,
                    function: request.function,
                    obligations: request.obligations.clone(),
                    lineage_roots: request.lineage_roots.clone(),
                    obligation,
                    diagnostics: output.diagnostics,
                });
            }
            TrustMcVerificationMode::BoundedModelCheck => {
                return Err(NativeTrustMcBundleError::UnsupportedTrustMcMode {
                    request: request.id,
                    mode: request.mode,
                });
            }
        }
    }

    if saw_trust_mc { Ok(obligations) } else { Err(NativeTrustMcBundleError::NoTrustMcRequests) }
}

fn native_chc_metadata(
    bundle: &NativeVerificationBundle,
    request_id: NativeRequestId,
    function: FuncId,
    mode: TrustMcVerificationMode,
    obligations: &[ProofId],
    lineage_roots: &[ProofLineageId],
    provenance: &NativeRequestProvenance,
) -> NativeTypedChcObligationMetadata {
    let (adapter_input, source_digest) = match bundle.input {
        NativeAdapterInput::RustMir { body_digest } => {
            ("rust-mir", Some(proof_digest_metadata(body_digest)))
        }
        NativeAdapterInput::TrustIrModule => ("trust_ir-module", None),
    };

    let metadata = NativeTypedChcObligationMetadata::new(
        bundle_producer_name(bundle.producer),
        adapter_input,
        source_digest,
        proof_digest_metadata(bundle.trust_ir_module_digest),
        proof_digest_metadata(bundle.lineage.stable_digest()),
        request_id.index(),
        trust_mc_verification_mode_name(mode),
        function.index(),
        obligations.iter().map(|id| id.index()).collect(),
        lineage_roots.iter().map(|id| id.index()).collect(),
    )
    .with_compiler_facts(
        proof_digest_metadata(bundle.compiler_facts.stable_digest()),
        native_compiler_fact_counts(&bundle.compiler_facts),
        native_obligation_compiler_facts(&bundle.compiler_facts, obligations),
    )
    // Diagnostic structural-completeness provenance for the trivially-safe
    // lane. This obligation's CHC is minted below from this same bundle by
    // `translate_chc` (`trust_mc_chc_pdr_obligations_from_native_bundle`), the
    // COMPLETE-BY-CONSTRUCTION native translator: it emits a reachable `error`
    // edge for every panic site (`Inst::Assert`/`Inst::Unreachable`/overflow/
    // div-by-zero/bounds/narrowing-cast), an UNCONDITIONAL `error` edge for
    // every unsupported construct (`add_unsupported_error`), fails closed on
    // indirect calls, and the compiler's `lower.rs` pins every absent/risky
    // call (`unwrap`/`expect`/unmodeled) with an `Assert(false)` may-panic
    // marker. It therefore NEVER drops a panic-site error rule under the full
    // safety profile, so a
    // trivially-safe CHC (no rule derives `error`) minted here is a genuine
    // structural-unreachability proof — not a dropped assertion or a partial
    // translator under-approximation. The serialized marker itself remains
    // forgeable diagnostic metadata and grants no authority; the driver mints
    // authority only at its fresh native-bundle translation boundary after
    // requiring every safety check option (see `native.rs`).
    .with_structural_reachability_complete(true);

    if let Some(replay_identity) = native_replay_identity(provenance.replay_identity()) {
        metadata.with_replay_metadata(
            replay_identity,
            native_replay_context_metadata(provenance.replay_context()),
        )
    } else {
        metadata
    }
}

fn proof_digest_metadata(digest: ProofDigest) -> NativeArtifactDigest {
    NativeArtifactDigest::new(
        digest.algorithm.to_string(),
        digest.bytes.iter().map(|byte| format!("{byte:02x}")).collect::<String>(),
    )
}

fn native_replay_identity(
    replay: Option<&ProofReplayIdentity>,
) -> Option<NativeReplayIdentityMetadata> {
    let replay = replay?;
    Some(NativeReplayIdentityMetadata {
        engine: replay.engine.clone(),
        invocation: replay.invocation.clone(),
        transcript_digest: proof_digest_metadata(replay.transcript_digest?),
    })
}

fn native_replay_context_metadata(context: &NativeReplayContext) -> NativeReplayContextMetadata {
    NativeReplayContextMetadata {
        atoms: context
            .atoms
            .iter()
            .map(|atom| NativeReplayAtomMetadata {
                atom_id: atom.id.index(),
                kind: native_replay_atom_kind(atom.kind),
                formula_schema: atom.formula.schema.clone(),
                payload_digest: proof_digest_metadata(atom.payload_digest),
                proof_obligation_id: atom.obligation.map(ProofId::index),
                assertion_id: atom.assertion_id.map(|id| id.index()),
                span: atom.span.map(native_source_span_metadata),
            })
            .collect(),
        unsupported_modes: context
            .unsupported_modes
            .iter()
            .map(|unsupported| NativeUnsupportedModeMetadata {
                reason: native_unsupported_mode_reason(unsupported.reason).to_string(),
                detail: unsupported.detail.clone(),
            })
            .collect(),
    }
}

fn native_replay_atom_kind(kind: NativeReplayAtomKind) -> NativeReplayAtomKindMetadata {
    match kind {
        NativeReplayAtomKind::Assumption => NativeReplayAtomKindMetadata::Assumption,
        NativeReplayAtomKind::Assertion => NativeReplayAtomKindMetadata::Assertion,
    }
}

fn native_unsupported_mode_reason(reason: NativeUnsupportedModeReason) -> &'static str {
    match reason {
        NativeUnsupportedModeReason::UnsupportedVerifierMode => "unsupported-verifier-mode",
        NativeUnsupportedModeReason::UnsupportedFormulaSchema => "unsupported-formula-schema",
        NativeUnsupportedModeReason::UnsupportedCompilerFact => "unsupported-compiler-fact",
        NativeUnsupportedModeReason::MissingSourceSpan => "missing-source-span",
        NativeUnsupportedModeReason::MissingReplayTranscript => "missing-replay-transcript",
        NativeUnsupportedModeReason::Other => "other",
    }
}

fn bundle_producer_name(producer: NativeBundleProducer) -> &'static str {
    match producer {
        NativeBundleProducer::TRust => "tRust",
        NativeBundleProducer::TSwift => "tSwift",
        NativeBundleProducer::TC => "tC",
        NativeBundleProducer::TrustIr => "trust_ir",
    }
}

fn trust_mc_verification_mode_name(mode: TrustMcVerificationMode) -> &'static str {
    match mode {
        TrustMcVerificationMode::BoundedModelCheck => "bmc",
        TrustMcVerificationMode::Chc => "chc",
        TrustMcVerificationMode::Pdr => "pdr",
    }
}

fn native_compiler_fact_counts(facts: &NativeCompilerFacts) -> NativeCompilerFactCounts {
    NativeCompilerFactCounts {
        adt_layouts: facts.adt_layouts.len(),
        fat_pointers: facts.fat_pointers.len(),
        trait_object_metadata: facts.trait_object_metadata.len(),
        pointer_offsets: facts.pointer_offsets.len(),
        casts: facts.casts.len(),
        monomorphizations: facts.monomorphizations.len(),
        obligation_sources: facts.obligation_sources.len(),
    }
}

fn native_obligation_compiler_facts(
    facts: &NativeCompilerFacts,
    obligations: &[ProofId],
) -> Vec<NativeObligationCompilerFacts> {
    facts
        .obligation_sources
        .iter()
        .filter(|source| obligations.contains(&source.obligation))
        .map(|source| NativeObligationCompilerFacts {
            proof_obligation_id: source.obligation.index(),
            function_id: source.function.map(FuncId::index),
            span: source.span.map(native_source_span_metadata),
            cause: native_obligation_cause_metadata(source.cause),
            monomorphization_id: source.monomorphization.map(|id| id.index()),
            fact_refs: source.facts.iter().map(native_compiler_fact_reference).collect(),
        })
        .collect()
}

fn native_compiler_fact_reference(fact: &NativeCompilerFactRef) -> NativeCompilerFactReference {
    match *fact {
        NativeCompilerFactRef::AdtLayout(id) => {
            NativeCompilerFactReference::new(NativeCompilerFactKind::AdtLayout, id.index())
        }
        NativeCompilerFactRef::FatPointer(id) => {
            NativeCompilerFactReference::new(NativeCompilerFactKind::FatPointer, id.index())
        }
        NativeCompilerFactRef::TraitObjectMetadata(id) => NativeCompilerFactReference::new(
            NativeCompilerFactKind::TraitObjectMetadata,
            id.index(),
        ),
        NativeCompilerFactRef::PointerOffset(id) => {
            NativeCompilerFactReference::new(NativeCompilerFactKind::PointerOffset, id.index())
        }
        NativeCompilerFactRef::Cast(id) => {
            NativeCompilerFactReference::new(NativeCompilerFactKind::Cast, id.index())
        }
        NativeCompilerFactRef::Monomorphization(id) => {
            NativeCompilerFactReference::new(NativeCompilerFactKind::Monomorphization, id.index())
        }
    }
}

fn native_source_span_metadata(span: SourceSpan) -> NativeSourceSpanMetadata {
    NativeSourceSpanMetadata { file: span.file, line: span.line, col: span.col }
}

fn native_obligation_cause_metadata(cause: NativeObligationCause) -> NativeObligationCauseMetadata {
    match cause {
        NativeObligationCause::Precondition => NativeObligationCauseMetadata::Precondition,
        NativeObligationCause::Postcondition => NativeObligationCauseMetadata::Postcondition,
        NativeObligationCause::Assert => NativeObligationCauseMetadata::Assert,
        NativeObligationCause::BoundsCheck => NativeObligationCauseMetadata::BoundsCheck,
        NativeObligationCause::OverflowCheck => NativeObligationCauseMetadata::OverflowCheck,
        NativeObligationCause::LayoutCheck => NativeObligationCauseMetadata::LayoutCheck,
        NativeObligationCause::CastCheck => NativeObligationCauseMetadata::CastCheck,
        NativeObligationCause::PointerOffset => NativeObligationCauseMetadata::PointerOffset,
        NativeObligationCause::BorrowCheck => NativeObligationCauseMetadata::BorrowCheck,
        NativeObligationCause::Translation => NativeObligationCauseMetadata::Translation,
        NativeObligationCause::Panic => NativeObligationCauseMetadata::Panic,
        NativeObligationCause::Temporal => NativeObligationCauseMetadata::Other,
        NativeObligationCause::Other => NativeObligationCauseMetadata::Other,
    }
}

fn native_obligation_id(request: NativeRequestId, obligations: &[ProofId]) -> String {
    // Trust: the canonical typed-obligation id uses the underscore `trust_ir`
    // family prefix (see `NativeTypedChcObligationMetadata::expected_obligation_id`
    // in trust-mc-core and the compiler's `native_trust_ir_expected_trust_mc_obligation_id`).
    // A hyphenated `trust-ir` prefix here makes the translated id fail to match
    // the expected id, so every obligation reports "no translated obligation".
    match obligations {
        [only] => {
            format!("trust_ir-native-trust_mc-request-{}-proof-{}", request.index(), only.index())
        }
        _ => format!("trust_ir-native-trust_mc-request-{}", request.index()),
    }
}

fn native_obligation_kind(module: &trust_ir::Module, obligations: &[ProofId]) -> MirObligationKind {
    obligations
        .first()
        .and_then(|id| module.proof_obligations.iter().find(|obligation| obligation.id == *id))
        .map(|obligation| map_obligation_kind(obligation.kind.clone()))
        .unwrap_or(MirObligationKind::Assertion)
}

fn map_obligation_kind(kind: ObligationKind) -> MirObligationKind {
    match kind {
        ObligationKind::Precondition
        | ObligationKind::Postcondition
        | ObligationKind::TypeInvariant
        | ObligationKind::RefinementType => MirObligationKind::Invariant,
        ObligationKind::LoopInvariant => MirObligationKind::LoopInvariant,
        ObligationKind::TranslationValidation
        | ObligationKind::TemporalSafety
        | ObligationKind::Liveness => MirObligationKind::Protocol,
        // Trust (trust-ir-spine item T1): the new routing-grade panic-class
        // kinds (`ArithmeticSafety`, `BoundsCheck`) are panic-freedom
        // obligations — map them to `Assertion` exactly like `PanicFreedom`.
        ObligationKind::MemorySafety
        | ObligationKind::PanicFreedom
        | ObligationKind::ArithmeticSafety
        | ObligationKind::BoundsCheck => MirObligationKind::Assertion,
        // `ObligationKind` is `#[non_exhaustive]`; treat an unknown future kind
        // conservatively as an assertion.
        _ => MirObligationKind::Assertion,
    }
}
