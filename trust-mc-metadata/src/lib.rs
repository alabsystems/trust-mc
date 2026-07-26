// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

extern crate clap;

use serde::{Deserialize, Serialize};
use std::{collections::HashSet, path::PathBuf};

pub use artifact::ArtifactType;
pub use autoharness::{AutoHarnessMetadata, AutoHarnessSkipReason};
pub use chc::{ChcStepMode, ChcTrackLevel};
pub use diagnostics::{
    AbstractedFallbackInfo, AggregateEncodingGapInfo, AssertUntranslatableInfo,
    AssumeDroppedTransitionInfo, BigIntUnsoundnessInfo, BmcStoreCoercionFallbackInfo,
    ChcCoerceEqDropInfo, ChcFallbackInfo, ChcTranslationDropInfo, ConstantZeroFallbackInfo,
    DiagnosticCounters, DivergingCallDropInfo, ErrorBlockedFmtInfo, FpBitvectorEncodingInfo,
    HeapCheckUnknownLayoutInfo, HeapCheckUntranslatableInfo, InferablePredicateInfo,
    InternalWorkaroundInfo, IntoOptionDropInfo, IteratorUnsoundnessInfo, KaniMemOverapproxInfo,
    KnownStdlibUnconstrainedInfo, OffsetProvenanceUnresolvedInfo, PointeeSynthesisFallbackInfo,
    PtrMetadataUnconstrainedInfo, RoundingAssertionBypassInfo, SignednessFallbackInfo,
    SortHarmonizeFreshVarInfo, StaticInitIncompleteInfo, StoreDroppedTransitionInfo,
    StubApproximationInfo, TypeSortFallbackInfo, UNSOUNDNESS_CATEGORY_COUNT,
    UnconstrainedAssignmentInfo, UnhandledCallInfo, UnsoundnessCategory, UnsoundnessClass,
    UnsoundnessRecord, UnsupportedConstructFallbackInfo, VecFieldFallbackInfo,
};
pub use harness::{
    AssignsContract, HarnessAttributes, HarnessKind, HarnessMetadata, Stub, find_proof_harnesses,
};
pub use solver_option::SolverOption;
pub use unstable::{EnabledUnstableFeatures, UnstableFeature};
pub use vtable::{
    CallSite, InternedString, PossibleMethodEntry, TraitDefinedMethod, VtableCtxResults,
};

pub mod artifact;
mod autoharness;
mod chc;
mod diagnostics;
mod harness;
mod solver_option;
pub mod unstable;
mod vtable;

/// The structure of `.kani-metadata.json` files, which are emitted for each crate
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct KaniMetadata {
    /// The crate name from which this metadata was extracted.
    pub crate_name: String,
    /// The proof harnesses (`#[kani::proof]`) found in this crate.
    pub proof_harnesses: Vec<HarnessMetadata>,
    /// The features found in this crate that trust_mc does not support.
    /// (These general translate to `assert(false)` so we can still attempt verification.)
    pub unsupported_features: Vec<UnsupportedFeature>,
    /// If crates are built in test-mode, then test harnesses will be recorded here.
    pub test_harnesses: Vec<HarnessMetadata>,
    /// The functions with contracts in this crate
    pub contracted_functions: Vec<ContractedFunction>,
    /// Metadata for the `autoharness` subcommand
    pub autoharness_md: Option<AutoHarnessMetadata>,
    /// Iterator unsoundness information from codegen (#1929).
    /// When present and non-zero, indicates iterator verification was skipped due to sort mismatches.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub iterator_unsoundness: Option<IteratorUnsoundnessInfo>,
    /// BigInt/BigRational unsoundness information from codegen (#1989).
    /// When present and non-zero, indicates BigInt verification was skipped due to sort mismatches.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub bigint_unsoundness: Option<BigIntUnsoundnessInfo>,
    /// CHC type/size fallback information from codegen (#2234).
    /// When present and non-zero, indicates hard-coded fallback defaults were used.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub chc_fallbacks: Option<ChcFallbackInfo>,
    /// CHC translation drops from immutable/static helper paths (#2770).
    /// When present and non-zero, indicates place/constant/projection translation
    /// returned `None` and was tracked via dedicated drop counters.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub chc_translation_drops: Option<ChcTranslationDropInfo>,
    /// CHC coerce-eq dropped constraint information from codegen (#2235).
    /// When present, indicates call-result equality constraints were dropped
    /// due to sort mismatches, leaving destination locals unconstrained.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub chc_coerce_eq_drops: Option<ChcCoerceEqDropInfo>,
    /// CHC dropped `kani::assume` semantics from codegen (#2584).
    /// When present and non-zero, indicates one or more `kani::assume` guards
    /// were not enforced (missing target relation or fail-open fallback).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub assume_dropped_transitions: Option<AssumeDroppedTransitionInfo>,
    /// CHC dropped store transitions from codegen (#2424).
    /// When present and non-zero, indicates memory writes were dropped because
    /// projections could not be translated. Reads return stale/symbolic values.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub store_dropped_transitions: Option<StoreDroppedTransitionInfo>,
    /// Constant zero-value fallback information from statement codegen (#2463).
    /// When present and non-zero, indicates MIR constants were replaced with zero
    /// because their actual values could not be extracted — potentially unsound.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub constant_zero_fallbacks: Option<ConstantZeroFallbackInfo>,
    /// Unhandled call information from CHC call dispatch (#2573).
    /// When present and non-zero, indicates function calls fell through all dispatch
    /// stages and destination locals were left unconstrained (over-approximation).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub unhandled_calls: Option<UnhandledCallInfo>,
    /// Formatting/panic calls error-blocked in CHC dispatch (#3379).
    /// Dead-ended paths (not over-approximation).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub error_blocked_fmt: Option<ErrorBlockedFmtInfo>,
    /// Known stdlib calls left unconstrained in CHC dispatch (#3379).
    /// Recognized over-approximation, distinct from true unhandled calls.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub known_stdlib_unconstrained: Option<KnownStdlibUnconstrainedInfo>,
    /// Calls encoded with solver-inferable function summaries (#3395).
    /// Replacement-quality PROOFs hard-gate on this counter because the result
    /// depends on an inferred summary rather than the original call semantics.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub inferable_predicates: Option<InferablePredicateInfo>,
    /// Diverging calls (target=None) silently dropped without emitting CHC rules (#3164).
    /// When present and non-zero, indicates call dispatch claimed calls but emitted no
    /// rule, silently pruning paths from verification. Replacement-quality PROOFs
    /// hard-gate on this counter because reachable drops would hide behaviors.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub diverging_call_drops: Option<DivergingCallDropInfo>,
    /// Pointer-offset / deref allocation-bound checks skipped on unresolved
    /// provenance (symbolic obj_id lane). Fail-open, so a non-zero count means an
    /// OOB offset+deref could be falsely proven Safe — demotes the harness.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub offset_provenance_unresolved: Option<OffsetProvenanceUnresolvedInfo>,
    /// CHC assertions that could not be translated and were conservatively fail-closed.
    /// When present and non-zero, indicates assertion operands were untranslatable.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub assert_untranslatable: Option<AssertUntranslatableInfo>,
    /// CHC heap safety checks that could not be translated and were conservatively fail-closed.
    /// When present and non-zero, indicates unsupported heap-check predicates.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub heap_check_untranslatable: Option<HeapCheckUntranslatableInfo>,
    /// CHC heap checks that encountered unknown-layout types and were handled conservatively.
    /// When present and non-zero, indicates unknown-layout heap checks were emitted.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub heap_check_unknown_layout: Option<HeapCheckUnknownLayoutInfo>,
    /// CHC type-sort resolution fallback information (#2705).
    /// When present and non-zero, indicates type resolution fell back to hardcoded sorts
    /// (typically bv32), making the verification model potentially narrower than actual types.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub type_sort_fallbacks: Option<TypeSortFallbackInfo>,
    /// Signedness fallback information (#2749).
    /// When present and non-zero, indicates operand signedness could not be determined
    /// from MIR types and an operation-specific default was used.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub signedness_fallbacks: Option<SignednessFallbackInfo>,
    /// Statement `IntoOption<Result<..>>` dropped-error information (#2597).
    /// When present and non-zero, indicates statement codegen converted one or more
    /// `Result::Err` values to `None`, short-circuiting translation paths.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub into_option_drops: Option<IntoOptionDropInfo>,
    /// Pre-inlined collection internal workaround count (#1662).
    /// When present and non-zero, indicates statement codegen used symbolic approximations
    /// for rustc pre-inlined collection internals (BTree, RawVec, etc.).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub internal_workarounds: Option<InternalWorkaroundInfo>,
    /// Abstracted stdlib fallback count (#1691).
    /// When present and non-zero, indicates statement codegen used symbolic approximations
    /// for pre-inlined UTF8/Cow/String internals not intercepted at reachability level.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub abstracted_fallbacks: Option<AbstractedFallbackInfo>,
    /// Vec field fallback information (#2733).
    /// When present and non-zero, indicates `vec_field_select` encountered a Vec with
    /// non-datatype sort and returned a symbolic fallback instead of a real field access.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub vec_field_fallbacks: Option<VecFieldFallbackInfo>,
    /// Pointee synthesis fallback information (#3013).
    /// When present and non-zero, indicates `synthesize_pointee_expr` created unconstrained
    /// symbolic variables for pointer dereferences with incomplete tracking.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub pointee_synthesis_fallbacks: Option<PointeeSynthesisFallbackInfo>,
    /// Unsupported construct fallback information (#3017).
    /// When present and non-zero, indicates `ctx.unsupported()` was called at code paths
    /// that proceed with incorrect/fallback data rather than bailing early.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub unsupported_construct_fallbacks: Option<UnsupportedConstructFallbackInfo>,
    /// Unconstrained assignment information (#3192).
    /// When present and non-zero, indicates BMC `codegen_assign` received `None` from
    /// `codegen_rvalue`, leaving LHS SSA variables declared but unconstrained.
    /// Distinct from `unsupported_construct_fallback` which tracks fallback-data paths.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub unconstrained_assignments: Option<UnconstrainedAssignmentInfo>,
    /// BMC store coercion fallback information (#3064).
    /// When present and non-zero, indicates BMC store operations substituted fresh
    /// unconstrained symbolics because value sorts could not be coerced to match
    /// array element sorts.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub bmc_store_coercion_fallbacks: Option<BmcStoreCoercionFallbackInfo>,
    /// kani::mem over-approximation information (#3165).
    /// When present and non-zero, indicates kani::mem memory safety predicates
    /// (is_ptr_aligned, same_allocation, in_bounds) were over-approximated as true.
    /// Replacement-quality PROOFs hard-gate on this counter because the harness has
    /// no memory safety assurance from these checks.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub kani_mem_overapprox: Option<KaniMemOverapproxInfo>,
    /// Sort harmonize fresh-variable fallback information (#3263).
    /// When present and non-zero, indicates sort harmonization created fresh
    /// unconstrained symbolic variables at phi merge points, destroying concrete
    /// value information. Sound over-approximation — PROOF remains valid.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub sort_harmonize_fresh_var_fallbacks: Option<SortHarmonizeFreshVarInfo>,
    /// PtrMetadata unconstrained symbolic fallback (#3447).
    /// When present and non-zero, indicates PtrMetadata codegen used fresh symbolic
    /// variables because metadata could not be resolved from tracked state.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub ptr_metadata_unconstrained: Option<PtrMetadataUnconstrainedInfo>,
    /// Static initializer incomplete encoding (#3447).
    /// When present and non-zero, indicates static initializers could not be
    /// fully encoded, leaving statics unconstrained.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub static_init_incomplete: Option<StaticInitIncompleteInfo>,
    /// Floating-point bitvector encoding (#3447).
    /// When present and non-zero, indicates float types were mapped to BV sorts
    /// instead of SMT FP sorts, so IEEE 754 behavior is not modeled precisely.
    /// Replacement-quality PROOFs hard-gate on this counter.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub fp_bitvector_encoding: Option<FpBitvectorEncodingInfo>,
    /// Aggregate encoding gap (#3447).
    /// When present and non-zero, indicates ADT/enum aggregate or discriminant
    /// encoding fell back to fresh unconstrained symbolics.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub aggregate_encoding_gap: Option<AggregateEncodingGapInfo>,
    /// Stub approximation (#3447).
    /// When present and non-zero, indicates CHC stubs returned unconstrained
    /// symbolic values instead of precisely-encoded results.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub stub_approximation: Option<StubApproximationInfo>,
    /// Float rounding assertion bypass (#3779).
    /// When present and non-zero, indicates rounding assertions were weakened
    /// to finiteness tautologies by the assertion-pattern recognizer.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub rounding_assertion_bypass: Option<RoundingAssertionBypassInfo>,
}

impl KaniMetadata {
    /// Extract an unsoundness record for one category (#3715).
    ///
    /// Returns `None` if the category's diagnostic field is absent.
    #[allow(clippy::enum_glob_use)]
    pub fn unsoundness(&self, cat: UnsoundnessCategory) -> Option<UnsoundnessRecord<'_>> {
        use UnsoundnessCategory::*;
        // Compact arm macros: most categories use `i.count` + `Some(&i.per_harness)`.
        macro_rules! ph {
            ($field:expr) => {{
                let i = $field.as_ref()?;
                (i.count, Some(&i.per_harness))
            }};
        }
        macro_rules! no_ph {
            ($field:expr) => {{
                let i = $field.as_ref()?;
                (i.count, None)
            }};
        }
        let (total_count, per_harness) = match cat {
            ConstantZeroFallback => ph!(self.constant_zero_fallbacks),
            InternalWorkaround => ph!(self.internal_workarounds),
            ChcFallback => {
                let i = self.chc_fallbacks.as_ref()?;
                (i.total_count, Some(&i.per_harness))
            }
            TypeSortFallback => ph!(self.type_sort_fallbacks),
            SignednessFallback => ph!(self.signedness_fallbacks),
            UnsupportedConstructFallback => ph!(self.unsupported_construct_fallbacks),
            UnconstrainedAssignment => ph!(self.unconstrained_assignments),
            AssertUntranslatable => no_ph!(self.assert_untranslatable),
            HeapCheckUntranslatable => no_ph!(self.heap_check_untranslatable),
            HeapCheckUnknownLayout => no_ph!(self.heap_check_unknown_layout),
            IteratorUnsoundness => {
                let i = self.iterator_unsoundness.as_ref()?;
                (i.total_skip_count(), Some(&i.per_harness))
            }
            BigIntUnsoundness => {
                let i = self.bigint_unsoundness.as_ref()?;
                (i.chc_skip_count, Some(&i.per_harness))
            }
            BmcStoreCoercionFallback => ph!(self.bmc_store_coercion_fallbacks),
            AssumeDroppedTransition => ph!(self.assume_dropped_transitions),
            ChcCoerceEqDrop => {
                let i = self.chc_coerce_eq_drops.as_ref()?;
                (i.total_count, Some(&i.per_harness))
            }
            ChcTranslationDrop => {
                let i = self.chc_translation_drops.as_ref()?;
                (i.total_count(), Some(&i.per_harness))
            }
            ChcSoundHavocDrop => {
                let i = self.chc_translation_drops.as_ref()?;
                (i.sound_havoc_count, Some(&i.sound_havoc_per_harness))
            }
            StoreDroppedTransition => ph!(self.store_dropped_transitions),
            IntoOptionDrop => ph!(self.into_option_drops),
            AbstractedFallback => ph!(self.abstracted_fallbacks),
            VecFieldFallback => ph!(self.vec_field_fallbacks),
            PointeeSynthesisFallback => ph!(self.pointee_synthesis_fallbacks),
            UnhandledCalls => ph!(self.unhandled_calls),
            DivergingCallDrop => ph!(self.diverging_call_drops),
            OffsetProvenanceUnresolved => ph!(self.offset_provenance_unresolved),
            KaniMemOverapprox => ph!(self.kani_mem_overapprox),
            SortHarmonizeFreshVar => ph!(self.sort_harmonize_fresh_var_fallbacks),
            InferablePredicate => ph!(self.inferable_predicates),
            PtrMetadataUnconstrained => ph!(self.ptr_metadata_unconstrained),
            StaticInitIncomplete => ph!(self.static_init_incomplete),
            FpBitvectorEncoding => ph!(self.fp_bitvector_encoding),
            AggregateEncodingGap => ph!(self.aggregate_encoding_gap),
            StubApproximation => ph!(self.stub_approximation),
            RoundingAssertionBypass => ph!(self.rounding_assertion_bypass),
        };
        (total_count > 0).then(|| UnsoundnessRecord {
            category: cat,
            class: cat.class(),
            json_key: cat.json_key(),
            total_count,
            per_harness,
        })
    }

    /// Iterate over all unsoundness categories that have nonzero counts (#3715).
    pub fn unsoundness_diagnostics(&self) -> impl Iterator<Item = UnsoundnessRecord<'_>> {
        use strum::IntoEnumIterator;
        UnsoundnessCategory::iter().filter_map(|cat| self.unsoundness(cat))
    }
}

#[derive(Debug, Clone, Serialize, Deserialize, Eq, PartialEq, PartialOrd, Ord)]
pub struct ContractedFunction {
    /// The fully qualified name the user gave to the function (i.e. includes the module path).
    pub function: String,
    /// The (currently full-) path to the file this function was declared within.
    pub file: String,
    /// The pretty names of the proof harnesses (`#[kani::proof_for_contract]`) for this function
    pub harnesses: Vec<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct UnsupportedFeature {
    // We could replace this with an enum: https://github.com/model-checking/kani/issues/1765
    /// A string identifying the feature.
    pub feature: String,
    /// A list of locations (file, line) where this unsupported feature can be found.
    pub locations: HashSet<Location>,
}

/// The location in a file
#[derive(Clone, Debug, Deserialize, Eq, Hash, PartialEq, Serialize)]
pub struct Location {
    pub filename: String,
    pub start_line: u64,
}

/// We stub artifacts with the path to a trust_mcMetadata file.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CompilerArtifactStub {
    pub metadata_path: PathBuf,
}
