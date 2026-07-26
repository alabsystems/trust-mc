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
//!   (back-edges) fail closed pending bounded unrolling
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
//! overflow/memory error edges. They are not proof authority: the
//! `trust-mc-driver` proof-grade native-bundle entry point rejects public
//! `Wrapping`/`ValidBorrow` occurrences before minting its private exact-bundle
//! capability. Callers using this crate directly receive diagnostic VCs only.
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
    ChcTranslationOutput, TrustIrChcDiagnostic, TrustIrChcUnsupportedReason,
    trust_ir_function_to_chc_translation_output, trust_ir_function_to_chc_vc,
    trust_ir_to_chc_translation_outputs, trust_ir_to_chc_vc,
};

#[cfg(test)]
mod tests;
