// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! trust_ir Module consumption for trust_mc verification.
//!
//! This crate translates a `trust_ir::Module` into trust_mc's solver-independent VC IR
//! (`BmcVc`), enabling verification of programs from any t* frontend (tRust,
//! tSwift, tC).
//!
//! ## Architecture
//!
//! ```text
//! tRust/tSwift/tC  ──►  trust_ir::Module  ──►  trust_mc-trust-bmc  ──►  BmcVc/ChcVc  ──►  ay
//! ```
//!
//! ## Supported Checks
//!
//! - **Arithmetic overflow**: Add, Sub, Mul on integer types
//! - **Division by zero**: SDiv, UDiv, SRem, URem
//! - **Memory bounds**: Load/Store/GEP with array-based symbolic memory model
//! - **Assertions**: `Assert` instructions become direct VCs
//! - **Control flow**: acyclic multi-block CFGs (br/condbr/scalar switch with
//!   block-parameter joins) use a guarded-path BMC encoding; loops
//!   (back-edges) fail closed pending bounded unrolling. (The CHC lane
//!   encodes loops relationally; trust-mc-driver's `bounded_unroll` module
//!   additionally derives a k-bounded acyclic under-approximation from that
//!   encoding for REFUTATION-only counterexample search.)
//! - **Postconditions**: Return instructions generate VCs from function proof annotations
//! - **Interprocedural**: Bounded acyclic direct calls get typed CHC summaries;
//!   unknown and recursive calls fail closed
//! - **Atomics**: AtomicLoad/AtomicStore/AtomicRMW/CmpXchg for sequential BMC
//!
//! ## Memory Model
//!
//! Each `Alloca` creates a symbolic memory region backed by an SMT `Array(BV64, T)`.
//! `Store` updates the array, `Load` selects from it, and `GEP` computes offsets.
//! Bounds checks are emitted when enabled. Unknown raw pointers and unsupported
//! semantics fail closed by adding typed VCs rather than silently trusting
//! annotations.
//!
//! ## Proof Annotations
//!
//! The BMC lane treats bare safety claims as metadata. The CHC diagnostic lane
//! additionally interprets `Wrapping` as modular arithmetic and `ValidBorrow`
//! as a borrow-checker claim, so those annotations can suppress diagnostic
//! overflow/memory error edges. They are not proof authority: the ordinary
//! `trust-mc-driver` proof-grade native-bundle entry point rejects both. Its
//! live-source entry point admits source access claims only when a non-serializable
//! source-generation authority still belongs to that exact valid bundle. Initialized
//! scalar reference loads additionally require explicit [`SourceReferenceFacts`]
//! and checked actual pointees; a `ValidBorrow` stamp is not that evidence.
//! Callers using this crate directly receive diagnostic VCs only.
//!
//! Function-level annotations:
//! - `BoundedOutput` → generates postcondition VCs on Return
//!
//! Part of #4256.

mod bulk_count;
mod coverage;
mod input;
mod native_bundle;
mod native_options;
mod source_reference;

pub use source_reference::{
    SourceInitializedParameterFact, SourceInitializedValueFact, SourceReferenceFacts,
    SourceReferenceFactsError, SourceReferenceLoadFact, SourceReferenceParameterFact,
    SourceReferenceValueFact,
};
mod signature_abi;
mod translate;
mod translate_chc;

pub use coverage::{
    SEMANTICS_COVERAGE, SemanticsCoverage, SemanticsFamily, SemanticsStatus, coverage_for_family,
    family_for_inst,
};
pub use native_bundle::{
    NativeChcBundleTranslationWork, NativeMcConfiguredChcTranslation, NativeTrustMcBmcVc,
    NativeTrustMcBundleError, NativeTrustMcChcPdrObligation, NativeUnmodeledObligation,
    NativeUnmodeledReason, native_obligations_not_refuted_by_a_counterexample,
    native_unmodeled_obligations, trust_mc_bmc_vcs_from_native_bundle,
    trust_mc_chc_pdr_obligations_from_native_bundle,
    trust_mc_chc_pdr_obligations_from_native_bundle_with_source_reference_facts,
    trust_mc_chc_pdr_obligations_from_native_bundle_with_work,
    trust_mc_configured_chc_pdr_obligations_from_native_bundle,
    trust_mc_configured_chc_pdr_obligations_from_native_bundle_with_source_reference_facts,
};
pub use native_options::{
    EffectiveNativeMcRequestConfig, NativeMcRequestOptionsRefusal, NativeMcTranslationConfig,
};
pub use signature_abi::first_typed_signature_abi;
mod tensor_region;
pub use tensor_region::{
    TensorConstruct, constant_carries_tensor_blob, inst_carries_tensor_blob,
    inst_spells_tensor_type, tensor_construct_names, tensor_region_constructs,
};
pub use translate::{TranslateOptions, trust_ir_function_to_bmc_vc, trust_ir_to_bmc_vc};
#[cfg(any(test, feature = "legacy-liveness-oracle"))]
#[doc(hidden)]
pub use translate_chc::trust_ir_function_to_chc_translation_output_with_legacy_liveness;
pub use translate_chc::{
    BlockLocalAllocaReject, CallSummaryAttempt, CallSummaryDeclineSite, CallSummaryOutcome,
    ChcTranslationOutput, ChcTranslationWork, ElementReadingFunctions, ExtractElementReject,
    LargeBlockEdge, LargeBlockErrorSite, LargeBlockMap, LargeBlockPath, PromotedAllocaReject,
    PromotionBlocker, ProofGradeElementReads, SingleCellAllocaRejection, StackCellAdmission,
    TrustIrChcDiagnostic, TrustIrChcUnsupportedReason, classify_aggregate_stack_cell,
    initialized_local_borrow_is_admissible, proof_grade_cast_is_admissible,
    single_cell_alloca_is_admissible, single_cell_alloca_rejection,
    stack_alloca_cell_accesses_match_type, stack_alloca_pointer_is_non_escaping,
    stack_cell_is_translator_opaque, trust_ir_function_to_chc_translation_output,
    trust_ir_function_to_chc_translation_output_per_block, trust_ir_function_to_chc_vc,
    trust_ir_to_chc_translation_outputs, trust_ir_to_chc_translation_outputs_per_block,
    trust_ir_to_chc_vc,
};

#[cfg(test)]
mod tests;
