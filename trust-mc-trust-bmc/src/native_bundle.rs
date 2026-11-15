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

use std::collections::BTreeMap;
use std::collections::btree_map::Entry;
use std::sync::Arc;

use thiserror::Error;
use trust_ir::{
    FuncId, NativeAdapterInput, NativeBundleProducer, NativeCompilerFactRef, NativeCompilerFacts,
    NativeObligationCause, NativeReplayAtomKind, NativeReplayContext, NativeRequestId,
    NativeRequestProvenance, NativeUnsupportedModeReason, NativeVerificationBundle,
    NativeVerificationBundleError, NativeVerificationRequest, ObligationKind, ObligationSite,
    ProofDigest, ProofId, ProofLineageId, ProofObligation, ProofReplayIdentity, SourceSpan,
    TrustMcVerificationMode, proof::SpecObligationRef,
};
use trust_mc_core::{
    BmcVc, ChcVc, MirChcPdrObligation, MirChcPdrObligationError, MirObligationKind,
    NativeArtifactDigest, NativeCompilerFactCounts, NativeCompilerFactKind,
    NativeCompilerFactReference, NativeObligationCauseMetadata, NativeObligationCompilerFacts,
    NativeReplayAtomKindMetadata, NativeReplayAtomMetadata, NativeReplayContextMetadata,
    NativeReplayIdentityMetadata, NativeSourceSpanMetadata, NativeTypedChcObligationMetadata,
    NativeUnsupportedModeMetadata,
};

use crate::input::ModuleInput;
use crate::native_options::{
    EffectiveNativeMcRequestConfig, NativeMcRequestOptionsRefusal, NativeMcTranslationConfig,
};
use crate::signature_abi::first_typed_signature_abi;
use crate::translate::TranslateOptions;
use crate::translate_chc::{ChcTranslationWork, TrustIrChcDiagnostic};

#[cfg(test)]
#[path = "native_bundle_translate_once_tests.rs"]
pub(crate) mod translate_once_tests;

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
    /// Complete original canonical request, including its active BMC bounds.
    pub request_digest: ProofDigest,
    /// Requested obligations `vc` does not answer. A consumer must not attribute
    /// any verdict of `vc` to this request while this is non-empty.
    pub unmodeled_obligations: Vec<NativeUnmodeledObligation>,
}

/// CHC/PDR obligation generated for one typed native trust_mc request.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct NativeTrustMcChcPdrObligation {
    /// Stable request id from the native verification bundle.
    pub request_id: NativeRequestId,
    /// The exact request-selected, supported execution configuration.
    pub request_config: EffectiveNativeMcRequestConfig,
    /// trust_ir function requested by the native trust_mc request.
    pub function: FuncId,
    /// Proof obligations carried by the typed request.
    pub obligations: Vec<ProofId>,
    /// Proof-lineage roots carried by the typed request.
    pub lineage_roots: Vec<ProofLineageId>,
    /// Generated typed CHC/PDR obligation. Its `vc` is the requested
    /// function's CHC, translated once per bundle call and SHARED (`Arc`) by
    /// every row that requests the same function; every other field is this
    /// request's own.
    pub obligation: MirChcPdrObligation,
    /// Typed fail-closed diagnostics emitted while lowering the requested
    /// function; shared like `obligation.vc`.
    pub diagnostics: Arc<[TrustIrChcDiagnostic]>,
    /// Requested obligations `obligation` does not answer. A consumer must not
    /// attribute any verdict of `obligation` to this request while this is
    /// non-empty; the driver's proof-grade runner refuses it before solving.
    pub unmodeled_obligations: Vec<NativeUnmodeledObligation>,
    /// Requested obligations a counterexample of `obligation` does not refute
    /// ([`native_obligations_not_refuted_by_a_counterexample`]). A consumer
    /// must not attribute a refutation to this request while this is non-empty.
    pub not_refuted_by_a_counterexample: Vec<ProofId>,
}

/// A requested proof obligation that the requested function's safety encoding
/// does not answer.
///
/// Both translators lower the REQUESTED FUNCTION into one question: can an error
/// site of that function (a failed `Assert`, a trap, an unmodeled construct) be
/// reached? A proof that none can answers exactly the panic-/memory-safety kinds
/// ([`ObligationKind::PanicFreedom`], `ArithmeticSafety`, `BoundsCheck`,
/// `MemorySafety`) of THAT function: every check the function carries is covered,
/// so a whole-function claim and a claim about any one of its checks both hold.
/// It answers nothing else, and [`NativeUnmodeledReason`] names each way an
/// obligation falls outside it. The request must then be refused by name rather
/// than credited with the function's safety verdict.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct NativeUnmodeledObligation {
    /// The requested obligation.
    pub obligation: ProofId,
    /// Its kind; `None` when the module declares no obligation with this id.
    pub kind: Option<ObligationKind>,
    /// The temporal property it names, if any.
    pub spec: Option<SpecObligationRef>,
    /// Why the safety encoding does not answer it.
    pub reason: NativeUnmodeledReason,
}

/// Why the requested function's safety encoding does not answer an obligation.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum NativeUnmodeledReason {
    /// The module declares no obligation with this id.
    NotDeclared,
    /// It names a temporal property of a spec machine (`ProofObligation::spec`);
    /// no translator here reads one.
    TemporalProperty,
    /// Its kind is not a panic-/memory-safety kind. A temporal, liveness,
    /// termination, give-back, ownership, translation-validation or
    /// producer-namespaced kind asks a different question. A contract kind
    /// (pre/postcondition, type invariant, refinement type, loop invariant)
    /// states its `formula`, which no translator here reads and nothing ties to
    /// an `Assert` of the body, so the body's safety says nothing about it.
    KindNotAnswered,
    /// Neither its `function` scope nor its `site` says which function it is
    /// about. The request's sidecar row does, but the sidecar is a producer
    /// claim about the obligation, not the obligation.
    Unscoped,
    /// Its `function` scope names a function other than the requested one.
    ScopedToAnotherFunction(FuncId),
    /// Its `site` lies in a function other than the requested one.
    SitedInAnotherFunction(FuncId),
    /// Its `site` names no instruction of the requested function.
    SiteUnresolved(ObligationSite),
}

impl std::fmt::Display for NativeUnmodeledReason {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NotDeclared => write!(f, "not declared by the module"),
            Self::TemporalProperty => write!(f, "a temporal property is not a safety question"),
            Self::KindNotAnswered => write!(f, "kind not answered by a safety encoding"),
            Self::Unscoped => write!(f, "neither a function scope nor a site binds it"),
            Self::ScopedToAnotherFunction(function) => {
                write!(f, "scoped to function #{}", function.index())
            }
            Self::SitedInAnotherFunction(function) => {
                write!(f, "sited in function #{}", function.index())
            }
            Self::SiteUnresolved(site) => write!(
                f,
                "site bb{}#{} does not resolve in the requested function",
                site.block.index(),
                site.inst_index
            ),
        }
    }
}

impl std::fmt::Display for NativeUnmodeledObligation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "obligation #{} (", self.obligation.index())?;
        if let Some(kind) = &self.kind {
            write!(f, "{kind:?}, ")?;
        }
        if let Some(spec) = &self.spec {
            write!(f, "temporal property `{}`::`{}`, ", spec.machine, spec.temporal)?;
        }
        write!(f, "{})", self.reason)
    }
}

/// The requested `obligations` that the safety encoding of `function` does not
/// answer (see [`NativeUnmodeledObligation`]), in request order.
#[must_use]
pub fn native_unmodeled_obligations(
    module: &trust_ir::Module,
    function: FuncId,
    obligations: &[ProofId],
) -> Vec<NativeUnmodeledObligation> {
    unmodeled_obligations_indexed(module, &ObligationIndex::new(module), function, obligations)
}

/// The module's declared proof obligations by id. Built once per bundle call so
/// each request's lookups cost `O(log P)` instead of a scan of all `P`
/// declarations — which made a bundle with one request per obligation cost
/// `O(P²)` before any translation started.
struct ObligationIndex<'m> {
    by_id: BTreeMap<ProofId, &'m ProofObligation>,
}

impl<'m> ObligationIndex<'m> {
    fn new(module: &'m trust_ir::Module) -> Self {
        let mut by_id = BTreeMap::new();
        for obligation in &module.proof_obligations {
            // The FIRST declaration of an id, which is what a front-to-back
            // `find` over `proof_obligations` returns.
            by_id.entry(obligation.id).or_insert(obligation);
        }
        Self { by_id }
    }

    fn get(&self, id: ProofId) -> Option<&'m ProofObligation> {
        self.by_id.get(&id).copied()
    }
}

fn unmodeled_obligations_indexed(
    module: &trust_ir::Module,
    index: &ObligationIndex<'_>,
    function: FuncId,
    obligations: &[ProofId],
) -> Vec<NativeUnmodeledObligation> {
    obligations
        .iter()
        .filter_map(|id| {
            let Some(obligation) = index.get(*id) else {
                return Some(NativeUnmodeledObligation {
                    obligation: *id,
                    kind: None,
                    spec: None,
                    reason: NativeUnmodeledReason::NotDeclared,
                });
            };
            unanswered_reason(module, function, obligation).map(|reason| {
                NativeUnmodeledObligation {
                    obligation: *id,
                    kind: Some(obligation.kind.clone()),
                    spec: obligation.spec.clone(),
                    reason,
                }
            })
        })
        .collect()
}

/// Why `function`'s safety encoding does not answer `obligation`, or `None`
/// when it does.
fn unanswered_reason(
    module: &trust_ir::Module,
    function: FuncId,
    obligation: &ProofObligation,
) -> Option<NativeUnmodeledReason> {
    // Every field is named, none is `..`-ed away: a field trust-ir appends to
    // `ProofObligation` must fail to compile HERE and be classified by hand,
    // the way `spec` should have been when it was appended.
    let ProofObligation {
        // Identity; the caller already matched it.
        id: _,
        kind,
        // Producer bookkeeping and labels. None of them changes which question
        // the obligation asks of the body.
        status: _,
        description: _,
        source: _,
        // Read by no translator here. `KindNotAnswered` refuses every kind
        // whose meaning is its formula; the safety kinds mean their checks.
        formula: _,
        function: scope,
        site,
        spec,
    } = obligation;
    if spec.is_some() {
        return Some(NativeUnmodeledReason::TemporalProperty);
    }
    if !safety_encoding_answers(kind) {
        return Some(NativeUnmodeledReason::KindNotAnswered);
    }
    // trust-ir's validator already refuses a site that disagrees with the scope
    // or does not resolve; both are re-checked here so a caller that bypasses
    // it (the BMC translation has no gate in front of it) still fails closed.
    if let Some(scope) = *scope
        && scope != function
    {
        return Some(NativeUnmodeledReason::ScopedToAnotherFunction(scope));
    }
    let Some(site) = *site else {
        return scope.is_none().then_some(NativeUnmodeledReason::Unscoped);
    };
    if site.function != function {
        return Some(NativeUnmodeledReason::SitedInAnotherFunction(site.function));
    }
    let resolves = module
        .function_by_id(function)
        .and_then(|body| body.block(site.block))
        .is_some_and(|block| block.body.get(site.inst_index as usize).is_some());
    (!resolves).then_some(NativeUnmodeledReason::SiteUnresolved(site))
}

/// Whether "no error site of the requested function is reachable" answers an
/// obligation of `kind`.
fn safety_encoding_answers(kind: &ObligationKind) -> bool {
    match kind {
        ObligationKind::PanicFreedom
        | ObligationKind::ArithmeticSafety
        | ObligationKind::BoundsCheck
        | ObligationKind::MemorySafety => true,
        ObligationKind::Precondition
        | ObligationKind::Postcondition
        | ObligationKind::TypeInvariant
        | ObligationKind::RefinementType
        | ObligationKind::LoopInvariant
        | ObligationKind::TranslationValidation
        | ObligationKind::TemporalSafety
        | ObligationKind::Liveness
        | ObligationKind::GiveBackRefinement
        | ObligationKind::Termination
        | ObligationKind::Ownership
        | ObligationKind::Custom { .. } => false,
        // `ObligationKind` is `#[non_exhaustive]`: a kind trust-ir adds later is
        // unmodeled until someone models it here.
        _ => false,
    }
}

/// The requested `obligations` that a counterexample of `function`'s safety
/// encoding does NOT refute, in request order.
///
/// The encoding's error rules are unlabeled, so a counterexample shows only
/// that SOME error site of the function is reachable, not which check failed.
/// That refutes exactly one claim: a whole-function [`ObligationKind::PanicFreedom`]
/// obligation scoped to `function` ("no check of this function fails"). A sited
/// obligation is about one check, which another may have failed before; an
/// `ArithmeticSafety`, `BoundsCheck` or `MemorySafety` obligation is about one
/// class of check, and the failed one may be of another class. Every other
/// obligation is listed, and a consumer must not attribute the refutation to
/// the request while this is non-empty.
#[must_use]
pub fn native_obligations_not_refuted_by_a_counterexample(
    module: &trust_ir::Module,
    function: FuncId,
    obligations: &[ProofId],
) -> Vec<ProofId> {
    not_refuted_by_a_counterexample_indexed(&ObligationIndex::new(module), function, obligations)
}

fn not_refuted_by_a_counterexample_indexed(
    index: &ObligationIndex<'_>,
    function: FuncId,
    obligations: &[ProofId],
) -> Vec<ProofId> {
    obligations
        .iter()
        .copied()
        .filter(|id| {
            !index.get(*id).is_some_and(|o| {
                matches!(o.kind, ObligationKind::PanicFreedom)
                    && o.function == Some(function)
                    && o.site.is_none()
                    && o.spec.is_none()
            })
        })
        .collect()
}

/// Errors returned while consuming a native trust_ir request bundle for trust_mc.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
#[non_exhaustive]
pub enum NativeTrustMcBundleError {
    /// Explicit source reference facts must retain their exact live context.
    #[error(transparent)]
    SourceReferenceFacts(#[from] crate::SourceReferenceFactsError),
    /// The module carries an inline-scope chain with no binary identity carrier.
    /// Refuse before bundle validation reaches the infallible module digest.
    #[error(
        "native verification bundle module has no wire identity: function #{function} scope #{scope} carries an unencodable inlined scope chain"
    )]
    InlinedScopeChainUnencodable { function: u32, scope: u32 },
    /// The module records a typed signature ABI (trust-ir wire v60
    /// `FuncTy::abi`) on the function type at index `func_ty` of its table,
    /// used or not. No trust-mc lowering models that transport, so the bundle
    /// is refused before any request is translated
    /// (`crate::signature_abi`).
    #[error(
        "native verification bundle module records a typed signature ABI on function type #{func_ty}; trust_mc does not model typed ABI transport (caller copies, argument extension, hidden results, source-to-carrier bindings)"
    )]
    TypedSignatureAbiNotModeled { func_ty: usize },
    /// Storage geometry never grants initialized SMT values or array elements.
    #[error(
        "native verification bundle contains addressable storage geometry; trust_mc has no initialized SMT value model for it"
    )]
    AddressableStorageNotModeled,
    /// The module stores trust-ir tensor-region constructs (wire v67-v70:
    /// `Ty::Tensor`, the six `Inst::Tensor*` instructions,
    /// `Constant::TensorBlob`, a non-empty `Module.blobs`), used or not. No
    /// trust-mc lowering models a tensor value, so the bundle is refused
    /// before any request is translated (`crate::tensor_region`).
    #[error(
        "native verification bundle module stores trust-ir tensor-region constructs ({}); trust_mc has no SMT value model for a tensor",
        crate::tensor_region::tensor_construct_names(.constructs)
    )]
    TensorRegionNotModeled { constructs: std::collections::BTreeSet<crate::TensorConstruct> },
    /// Bundle-level validation failed before any trust_mc request was translated.
    #[error("native verification bundle validation failed")]
    InvalidBundle(Vec<NativeVerificationBundleError>),
    /// The transport is bound, but its exact IR module is canonically invalid.
    /// This is a module refusal with no invented function/block ownership.
    #[error("native verification bundle contains an invalid trust_ir module: {0}")]
    InvalidModule(String),
    #[error(transparent)]
    UnsupportedRequestOptions(#[from] NativeMcRequestOptionsRefusal),
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

/// Keep unsupported inline metadata away from the infallible digest used by
/// bundle validation. TrustIR's core helper is available in the ordinary
/// production feature closure; its public binary projection API is enabled
/// only by this crate's dev-dependency, so relying on it here would make tests
/// hide a production feature error. No metadata is stripped and no substitute
/// identity is minted. The bundle validator remains the canonical identity
/// check: unencodable completeness claims are refused, and supported
/// certificate bindings must agree with the module digest.
/// This is a bounded carrier preflight, not a panic-free claim for arbitrary IR.
fn validate_native_bundle(
    bundle: &NativeVerificationBundle,
) -> Result<(), NativeTrustMcBundleError> {
    if let Some((function, scope)) = bundle.module.first_inlined_scope_chain() {
        return Err(NativeTrustMcBundleError::InlinedScopeChainUnencodable { function, scope });
    }
    // Refuse what no lowering models before validation hashes the module.
    if let Some(func_ty) = first_typed_signature_abi(&bundle.module) {
        return Err(NativeTrustMcBundleError::TypedSignatureAbiNotModeled { func_ty });
    }
    if crate::input::storage_sort_refusal(&bundle.module).is_some() {
        return Err(NativeTrustMcBundleError::AddressableStorageNotModeled);
    }
    let constructs = crate::tensor_region::tensor_region_constructs(&bundle.module);
    if !constructs.is_empty() {
        return Err(NativeTrustMcBundleError::TensorRegionNotModeled { constructs });
    }
    bundle.validate().map_err(NativeTrustMcBundleError::InvalidBundle)
}

/// Translate all BMC-capable typed trust_mc requests in a native trust_ir bundle.
///
/// Inline-scope wire admission and the typed-signature-ABI refusal precede
/// `NativeVerificationBundle::validate`, so requested obligations, lineage
/// roots, and function ids must be structurally bound before trust_mc emits
/// VCs. A `Chc`/`Pdr` request fails closed here;
/// those modes are translated by [`trust_mc_chc_pdr_obligations_from_native_bundle`].
pub fn trust_mc_bmc_vcs_from_native_bundle(
    bundle: &NativeVerificationBundle,
    options: &TranslateOptions,
) -> Result<Vec<NativeTrustMcBmcVc>, NativeTrustMcBundleError> {
    validate_native_bundle(bundle)?;

    let mut saw_trust_mc = false;
    let mut vcs = Vec::new();
    // Validate the exact borrowed module only once for this BMC batch.
    // Unsupported non-BMC request modes keep their existing earlier refusal.
    let mut input = None;

    for request in &bundle.requests {
        let NativeVerificationRequest::TrustMc(request) = request else {
            continue;
        };
        saw_trust_mc = true;

        match request.mode {
            TrustMcVerificationMode::BoundedModelCheck => {
                let request_digest = crate::native_options::validate_bmc_options(request)?;
                let vc = input
                    .get_or_insert_with(|| ModuleInput::new(&bundle.module))
                    .function(request.function, options)
                    .ok_or(NativeTrustMcBundleError::MissingFunction {
                        request: request.id,
                        function: request.function,
                    })?;
                vcs.push(NativeTrustMcBmcVc {
                    request_id: request.id,
                    request_digest,
                    function: request.function,
                    obligations: request.obligations.clone(),
                    lineage_roots: request.lineage_roots.clone(),
                    vc,
                    unmodeled_obligations: native_unmodeled_obligations(
                        &bundle.module,
                        request.function,
                        &request.obligations,
                    ),
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
/// `trust_mc_core::MirChcPdrObligation`s for the native CHC/PDR runner. The same
/// inline-scope wire admission, typed-signature-ABI refusal and bundle
/// validation as the BMC path run first.
///
/// One row per request, as before. The translation takes no obligation input,
/// so every request on the same function gets the same whole-function CHC: it
/// is translated ONCE per function per call and shared by those rows (see
/// [`NativeTrustMcChcPdrObligation::obligation`]), while each row keeps its own
/// obligation id, metadata, request id, obligations and lineage roots.
pub fn trust_mc_chc_pdr_obligations_from_native_bundle(
    bundle: &NativeVerificationBundle,
    options: &TranslateOptions,
) -> Result<Vec<NativeTrustMcChcPdrObligation>, NativeTrustMcBundleError> {
    trust_mc_chc_pdr_obligations_from_native_bundle_with_work(bundle, options)
        .map(|(obligations, _)| obligations)
}

/// Deterministic work counters of one [`trust_mc_chc_pdr_obligations_from_native_bundle`]
/// call. Instrumentation only; nothing in the verdict path reads them.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
#[non_exhaustive]
pub struct NativeChcBundleTranslationWork {
    /// CHC/PDR requests turned into rows.
    pub requests: u64,
    /// Functions translated: one per distinct requested function, however many
    /// requests name it.
    pub functions_translated: u64,
    /// The per-function translation counters, summed over the functions
    /// translated.
    pub translation: ChcTranslationWork,
}

/// [`trust_mc_chc_pdr_obligations_from_native_bundle`], also returning its work
/// counters.
pub fn trust_mc_chc_pdr_obligations_from_native_bundle_with_work(
    bundle: &NativeVerificationBundle,
    options: &TranslateOptions,
) -> Result<
    (Vec<NativeTrustMcChcPdrObligation>, NativeChcBundleTranslationWork),
    NativeTrustMcBundleError,
> {
    translate_chc_bundle_with_work(bundle, options, None)
}

/// Translate with explicit live source-reference facts. Public IR annotations
/// and the ordinary diagnostic/replay APIs never enable this context.
pub fn trust_mc_chc_pdr_obligations_from_native_bundle_with_source_reference_facts(
    bundle: &NativeVerificationBundle,
    options: &TranslateOptions,
    facts: &crate::SourceReferenceFacts<'_>,
) -> Result<Vec<NativeTrustMcChcPdrObligation>, NativeTrustMcBundleError> {
    if !facts.belongs_to(bundle) {
        return Err(crate::SourceReferenceFactsError::AuthorityMismatch.into());
    }
    translate_chc_bundle_with_work(bundle, options, Some(facts)).map(|(rows, _)| rows)
}

/// Supported translations and explicit request-local option refusals.
/// Unsupported settings never receive a substitute verification condition.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct NativeMcConfiguredChcTranslation {
    pub obligations: Vec<NativeTrustMcChcPdrObligation>,
    pub refused_requests: Vec<NativeMcRequestOptionsRefusal>,
    pub work: NativeChcBundleTranslationWork,
}

pub fn trust_mc_configured_chc_pdr_obligations_from_native_bundle(
    bundle: &NativeVerificationBundle,
    options: &TranslateOptions,
) -> Result<NativeMcConfiguredChcTranslation, NativeTrustMcBundleError> {
    translate_configured_chc_bundle(bundle, options, None)
}

pub fn trust_mc_configured_chc_pdr_obligations_from_native_bundle_with_source_reference_facts(
    bundle: &NativeVerificationBundle,
    options: &TranslateOptions,
    facts: &crate::SourceReferenceFacts<'_>,
) -> Result<NativeMcConfiguredChcTranslation, NativeTrustMcBundleError> {
    if !facts.belongs_to(bundle) {
        return Err(crate::SourceReferenceFactsError::AuthorityMismatch.into());
    }
    translate_configured_chc_bundle(bundle, options, Some(facts))
}

fn translate_chc_bundle_with_work(
    bundle: &NativeVerificationBundle,
    options: &TranslateOptions,
    source_references: Option<&crate::SourceReferenceFacts<'_>>,
) -> Result<
    (Vec<NativeTrustMcChcPdrObligation>, NativeChcBundleTranslationWork),
    NativeTrustMcBundleError,
> {
    let batch = translate_configured_chc_bundle(bundle, options, source_references)?;
    if let Some(refusal) = batch.refused_requests.into_iter().next() {
        return Err(refusal.into());
    }
    Ok((batch.obligations, batch.work))
}

fn translate_configured_chc_bundle(
    bundle: &NativeVerificationBundle,
    options: &TranslateOptions,
    source_references: Option<&crate::SourceReferenceFacts<'_>>,
) -> Result<NativeMcConfiguredChcTranslation, NativeTrustMcBundleError> {
    validate_native_bundle(bundle)?;

    // One complete check of this exact immutable module, before per-function
    // indexing, source-value analysis or request translation. The cached
    // context is shared by every requested function, not reconstructed per row.
    let input = ModuleInput::new(&bundle.module);
    if let Some(reason) = input.refusal_reason() {
        return Err(NativeTrustMcBundleError::InvalidModule(reason.to_owned()));
    }

    let mut saw_trust_mc = false;
    let mut obligations = Vec::new();
    let mut refused_requests = Vec::new();
    let mut work = NativeChcBundleTranslationWork::default();
    let index = ObligationIndex::new(&bundle.module);
    let metadata_context = NativeChcMetadataContext::new(bundle);
    let mut translations: BTreeMap<(FuncId, NativeMcTranslationConfig), SharedChcTranslation> =
        BTreeMap::new();

    for request in &bundle.requests {
        let NativeVerificationRequest::TrustMc(request) = request else {
            continue;
        };
        saw_trust_mc = true;

        match request.mode {
            TrustMcVerificationMode::Chc | TrustMcVerificationMode::Pdr => {
                let request_config = match EffectiveNativeMcRequestConfig::from_request(request) {
                    Ok(config) => config,
                    Err(refusal) => {
                        refused_requests.push(refusal);
                        continue;
                    }
                };
                let function = bundle.module.function_by_id(request.function).ok_or(
                    NativeTrustMcBundleError::MissingFunction {
                        request: request.id,
                        function: request.function,
                    },
                )?;
                let translation = match translations
                    .entry((request.function, request_config.translation_config()))
                {
                    Entry::Occupied(entry) => entry.into_mut(),
                    Entry::Vacant(entry) => {
                        let output = match source_references {
                            Some(facts) => input.chc_function_with_source_references(
                                request.function,
                                options,
                                facts,
                            ),
                            None => input.chc_function(request.function, options),
                        }
                        .ok_or(
                            NativeTrustMcBundleError::MissingFunction {
                                request: request.id,
                                function: request.function,
                            },
                        )?;
                        work.functions_translated += 1;
                        work.translation.accumulate(&output.work);
                        entry.insert(SharedChcTranslation::new(
                            output.vc,
                            output.diagnostics,
                            output.inductive_hypothesis_sites.len(),
                        ))
                    }
                };
                work.requests += 1;
                let obligation = MirChcPdrObligation::new(
                    native_obligation_id(request.id, &request.obligations),
                    function.name.clone(),
                    native_obligation_kind(&index, &request.obligations),
                    Arc::clone(&translation.vc),
                )
                .with_native_metadata(
                    metadata_context
                        .request_metadata(
                            request.id,
                            request.function,
                            request.mode,
                            &request.obligations,
                            &request.lineage_roots,
                            &request.provenance,
                        )
                        .with_request_config(request_config.binding().clone())
                        // One translator diagnostic is recorded per
                        // `add_unsupported_error` (an unconditionally reachable
                        // error rule from an unmodeled construct). Demote-only:
                        // consumers may use a nonzero count to hold a Refuted
                        // verdict at Unknown, never to mint authority.
                        .with_fail_closed_lowering_site_count(
                            u32::try_from(translation.diagnostics.len()).unwrap_or(u32::MAX),
                        )
                        // …and the DISTINCT typed reasons behind that count, so the
                        // demotion message can name the blocking constructs instead
                        // of only counting them. Diagnostic only — the builder
                        // sorts + dedups, and nothing but the message formatter
                        // reads the result. Deduplicated once per function, so a
                        // row costs the number of distinct reasons, not of sites.
                        .with_fail_closed_lowering_reasons(
                            translation.distinct_reason_labels.iter().cloned(),
                        )
                        // Direct self-call sites modeled by the inductive hypothesis
                        // (no error rule). Demote-only, like the count above: a
                        // refutation through a havoc'd self-call result is held at
                        // Unknown; a proof stands.
                        .with_inductive_hypothesis_site_count(
                            u32::try_from(translation.inductive_hypothesis_site_count)
                                .unwrap_or(u32::MAX),
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
                    request_config,
                    function: request.function,
                    obligations: request.obligations.clone(),
                    lineage_roots: request.lineage_roots.clone(),
                    obligation,
                    diagnostics: Arc::clone(&translation.diagnostics),
                    unmodeled_obligations: unmodeled_obligations_indexed(
                        &bundle.module,
                        &index,
                        request.function,
                        &request.obligations,
                    ),
                    not_refuted_by_a_counterexample: not_refuted_by_a_counterexample_indexed(
                        &index,
                        request.function,
                        &request.obligations,
                    ),
                });
            }
            TrustMcVerificationMode::BoundedModelCheck => {
                refused_requests.push(crate::native_options::unsupported_chc_mode(request));
            }
        }
    }

    if saw_trust_mc {
        Ok(NativeMcConfiguredChcTranslation { obligations, refused_requests, work })
    } else {
        Err(NativeTrustMcBundleError::NoTrustMcRequests)
    }
}

/// One function's CHC translation, shared by every row that requests it.
struct SharedChcTranslation {
    vc: Arc<ChcVc>,
    diagnostics: Arc<[TrustIrChcDiagnostic]>,
    /// `diagnostics`' reason labels, sorted and deduplicated — exactly what
    /// `with_fail_closed_lowering_reasons` makes of the full list.
    distinct_reason_labels: Vec<String>,
    inductive_hypothesis_site_count: usize,
}

impl SharedChcTranslation {
    fn new(
        vc: ChcVc,
        diagnostics: Vec<TrustIrChcDiagnostic>,
        inductive_hypothesis_site_count: usize,
    ) -> Self {
        let mut distinct_reason_labels: Vec<String> =
            diagnostics.iter().map(|d| d.reason.label()).collect();
        distinct_reason_labels.sort_unstable();
        distinct_reason_labels.dedup();
        Self {
            vc: Arc::new(vc),
            diagnostics: diagnostics.into(),
            distinct_reason_labels,
            inductive_hypothesis_site_count,
        }
    }
}

/// The bundle-level half of every row's native metadata, computed once per call:
/// the module, lineage and compiler-fact digests and counts are properties of
/// the bundle, and recomputing the digests per request made metadata cost
/// `O(requests × bundle)`. The per-request half is `request_metadata`'s.
struct NativeChcMetadataContext<'b> {
    producer: &'static str,
    adapter_input: &'static str,
    source_digest: Option<NativeArtifactDigest>,
    module_digest: NativeArtifactDigest,
    lineage_digest: NativeArtifactDigest,
    compiler_facts_digest: NativeArtifactDigest,
    compiler_fact_counts: NativeCompilerFactCounts,
    compiler_facts: &'b NativeCompilerFacts,
    /// Positions in `compiler_facts.obligation_sources`, by the obligation each
    /// source row names, in source order.
    sources_by_obligation: BTreeMap<ProofId, Vec<usize>>,
}

impl<'b> NativeChcMetadataContext<'b> {
    fn new(bundle: &'b NativeVerificationBundle) -> Self {
        let (adapter_input, source_digest) = match bundle.input {
            NativeAdapterInput::RustMir { body_digest } => {
                ("rust-mir", Some(proof_digest_metadata(body_digest)))
            }
            NativeAdapterInput::TrustIrModule => ("trust_ir-module", None),
        };
        let mut sources_by_obligation: BTreeMap<ProofId, Vec<usize>> = BTreeMap::new();
        for (position, source) in bundle.compiler_facts.obligation_sources.iter().enumerate() {
            sources_by_obligation.entry(source.obligation).or_default().push(position);
        }
        Self {
            producer: bundle_producer_name(bundle.producer),
            adapter_input,
            source_digest,
            module_digest: proof_digest_metadata(bundle.trust_ir_module_digest),
            lineage_digest: proof_digest_metadata(bundle.lineage.stable_digest()),
            compiler_facts_digest: proof_digest_metadata(bundle.compiler_facts.stable_digest()),
            compiler_fact_counts: native_compiler_fact_counts(&bundle.compiler_facts),
            compiler_facts: &bundle.compiler_facts,
            sources_by_obligation,
        }
    }

    /// The compiler-fact source rows naming any of `obligations`, in source
    /// order — the rows a front-to-back filter of every source keeps.
    fn obligation_compiler_facts(
        &self,
        obligations: &[ProofId],
    ) -> Vec<NativeObligationCompilerFacts> {
        let mut positions: Vec<usize> = obligations
            .iter()
            .filter_map(|id| self.sources_by_obligation.get(id))
            .flatten()
            .copied()
            .collect();
        positions.sort_unstable();
        positions.dedup();
        positions
            .into_iter()
            .map(|position| {
                native_obligation_compiler_facts_row(
                    &self.compiler_facts.obligation_sources[position],
                )
            })
            .collect()
    }

    fn request_metadata(
        &self,
        request_id: NativeRequestId,
        function: FuncId,
        mode: TrustMcVerificationMode,
        obligations: &[ProofId],
        lineage_roots: &[ProofLineageId],
        provenance: &NativeRequestProvenance,
    ) -> NativeTypedChcObligationMetadata {
        let metadata = NativeTypedChcObligationMetadata::new(
            self.producer,
            self.adapter_input,
            self.source_digest.clone(),
            self.module_digest.clone(),
            self.lineage_digest.clone(),
            request_id.index(),
            trust_mc_verification_mode_name(mode),
            function.index(),
            obligations.iter().map(|id| id.index()).collect(),
            lineage_roots.iter().map(|id| id.index()).collect(),
        )
        .with_compiler_facts(
            self.compiler_facts_digest.clone(),
            self.compiler_fact_counts,
            self.obligation_compiler_facts(obligations),
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
}

pub(crate) fn proof_digest_metadata(digest: ProofDigest) -> NativeArtifactDigest {
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
        NativeBundleProducer::Clean => "Clean",
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

fn native_obligation_compiler_facts_row(
    source: &trust_ir::NativeObligationSource,
) -> NativeObligationCompilerFacts {
    NativeObligationCompilerFacts {
        proof_obligation_id: source.obligation.index(),
        function_id: source.function.map(FuncId::index),
        span: source.span.map(native_source_span_metadata),
        cause: native_obligation_cause_metadata(source.cause),
        monomorphization_id: source.monomorphization.map(|id| id.index()),
        fact_refs: source.facts.iter().map(native_compiler_fact_reference).collect(),
    }
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

pub(crate) fn native_obligation_id(request: NativeRequestId, obligations: &[ProofId]) -> String {
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

/// Metadata class of a request: the class every requested obligation shares.
/// A request whose obligations are not all declared and of one class is never
/// filed under the L0 safety class (`Assertion`), which admits the request to
/// the bounded-unroll refutation lane; reading only the first obligation filed
/// `[PanicFreedom, Postcondition]` there.
fn native_obligation_kind(
    index: &ObligationIndex<'_>,
    obligations: &[ProofId],
) -> MirObligationKind {
    let mut classes = obligations
        .iter()
        .map(|id| index.get(*id).map(|obligation| map_obligation_kind(obligation.kind.clone())));
    match classes.next() {
        Some(Some(first)) if classes.all(|class| class == Some(first)) => first,
        _ => MirObligationKind::Protocol,
    }
}

/// Metadata class of an obligation kind. `Assertion` is the L0 safety class
/// that downstream lanes (the bounded-unroll refutation lane among them) treat
/// as a panic-reachability question, so only the panic-/memory-safety kinds may
/// map to it; whether the encoding answers a kind at all is
/// [`native_unmodeled_obligations`]'s decision, not this one's.
fn map_obligation_kind(kind: ObligationKind) -> MirObligationKind {
    match kind {
        ObligationKind::Precondition
        | ObligationKind::Postcondition
        | ObligationKind::TypeInvariant
        | ObligationKind::RefinementType => MirObligationKind::Invariant,
        ObligationKind::LoopInvariant => MirObligationKind::LoopInvariant,
        ObligationKind::Termination => MirObligationKind::Termination,
        ObligationKind::TranslationValidation
        | ObligationKind::TemporalSafety
        | ObligationKind::Liveness
        | ObligationKind::GiveBackRefinement
        | ObligationKind::Ownership
        | ObligationKind::Custom { .. } => MirObligationKind::Protocol,
        // Trust (trust-ir-spine item T1): the routing-grade panic-class kinds
        // (`ArithmeticSafety`, `BoundsCheck`) are panic-freedom obligations —
        // map them to `Assertion` exactly like `PanicFreedom`.
        ObligationKind::MemorySafety
        | ObligationKind::PanicFreedom
        | ObligationKind::ArithmeticSafety
        | ObligationKind::BoundsCheck => MirObligationKind::Assertion,
        // `ObligationKind` is `#[non_exhaustive]`: a kind added later is never
        // filed under the L0 safety class by default.
        _ => MirObligationKind::Protocol,
    }
}
