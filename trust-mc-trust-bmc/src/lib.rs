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
//! separate live-source entry point admits `Wrapping` only when a non-serializable
//! source-generation authority still belongs to that exact valid bundle;
//! `ValidBorrow` remains rejected. Callers using this crate directly receive
//! diagnostic VCs only.
//!
//! Function-level annotations:
//! - `BoundedOutput` → generates postcondition VCs on Return
//!
//! Part of #4256.

mod coverage;
mod native_bundle;
mod translate;
mod translate_chc;

pub use coverage::{
    SEMANTICS_COVERAGE, SemanticsCoverage, SemanticsFamily, SemanticsStatus, coverage_for_family,
    family_for_inst,
};
pub use native_bundle::{
    NativeTrustMcBmcVc, NativeTrustMcBundleError, NativeTrustMcChcPdrObligation,
    trust_mc_bmc_vcs_from_native_bundle, trust_mc_chc_pdr_obligations_from_native_bundle,
};
pub use translate::{TranslateOptions, trust_ir_function_to_bmc_vc, trust_ir_to_bmc_vc};
pub use translate_chc::{
    BlockLocalAllocaReject, CallSummaryAttempt, CallSummaryDeclineSite, CallSummaryOutcome,
    ChcTranslationOutput, PromotedAllocaReject, PromotionBlocker,
    SingleCellAllocaRejection, StackCellAdmission, TrustIrChcDiagnostic,
    TrustIrChcUnsupportedReason, classify_aggregate_stack_cell, proof_grade_cast_is_admissible,
    single_cell_alloca_is_admissible, single_cell_alloca_rejection,
    stack_alloca_cell_accesses_match_type, stack_alloca_pointer_is_non_escaping,
    stack_cell_is_translator_opaque,
    trust_ir_function_to_chc_translation_output, trust_ir_function_to_chc_vc,
    trust_ir_to_chc_translation_outputs, trust_ir_to_chc_vc,
};

#[cfg(test)]
mod tests;
