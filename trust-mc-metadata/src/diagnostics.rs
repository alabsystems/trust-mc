// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use strum_macros::{EnumCount, EnumIter, IntoStaticStr};

/// Total number of unsoundness categories tracked in `KaniMetadata` (#2973).
///
/// Derived from `UnsoundnessCategory` enum count. Adding a new variant to the
/// enum automatically updates this constant. The compile-time assertion in
/// `trust_mc-driver/src/unsoundness_counts.rs` verifies that every category is
/// accounted for in either `DEMOTED_CATEGORIES`, `FAIL_CLOSED_CATEGORIES`, or
/// `SOUND_APPROXIMATION_CATEGORIES`.
pub const UNSOUNDNESS_CATEGORY_COUNT: usize = <UnsoundnessCategory as strum::EnumCount>::COUNT;

/// Authoritative registry of counted unsoundness categories (#3715).
///
/// Each variant corresponds to one optional diagnostic field on `KaniMetadata`.
/// The `class()` and `json_key()` methods provide the category's classification
/// and stable JSON field name, eliminating string-table duplication in the driver.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, EnumIter, EnumCount, IntoStaticStr)]
pub enum UnsoundnessCategory {
    // ── Demoted (17): require driver demotion to prevent false proofs ──
    // (VecFieldFallback + PointeeSynthesisFallback are listed lower for layout
    //  but classify as Demoted — see class(); they are unsound symbolic subs.)
    ConstantZeroFallback,
    InternalWorkaround,
    ChcFallback,
    TypeSortFallback,
    SignednessFallback,
    UnsupportedConstructFallback,
    UnconstrainedAssignment,
    BmcStoreCoercionFallback,
    StoreDroppedTransition,
    DivergingCallDrop,
    KaniMemOverapprox,
    OffsetProvenanceUnresolved,
    InferablePredicate,
    FpBitvectorEncoding,
    RoundingAssertionBypass,
    // ── FailClosed (5): inject false constraints, no demotion needed ──
    AssertUntranslatable,
    HeapCheckUntranslatable,
    HeapCheckUnknownLayout,
    IteratorUnsoundness,
    BigIntUnsoundness,
    // ── SoundApproximation (12): tracked as proof/counterexample qualifications ──
    //    (VecFieldFallback and PointeeSynthesisFallback appear in this block for
    //     layout only; class() puts them in Demoted — see the note above.)
    AssumeDroppedTransition,
    ChcCoerceEqDrop,
    ChcTranslationDrop,
    ChcSoundHavocDrop,
    IntoOptionDrop,
    AbstractedFallback,
    VecFieldFallback,
    PointeeSynthesisFallback,
    UnhandledCalls,
    SortHarmonizeFreshVar,
    PtrMetadataUnconstrained,
    StaticInitIncomplete,
    AggregateEncodingGap,
    StubApproximation,
}

/// Classification of an unsoundness category (#3715).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnsoundnessClass {
    /// Requires driver demotion to prevent false proofs.
    Demoted,
    /// Injects `false` constraints or error rules — cannot produce false proofs.
    FailClosed,
    /// Fresh unconstrained symbolics — PROOF remains valid (universally quantified).
    SoundApproximation,
}

/// Borrowed view of one unsoundness category's metadata for a given crate (#3715).
pub struct UnsoundnessRecord<'a> {
    pub category: UnsoundnessCategory,
    pub class: UnsoundnessClass,
    pub json_key: &'static str,
    pub total_count: usize,
    pub per_harness: Option<&'a BTreeMap<String, usize>>,
}

impl UnsoundnessCategory {
    /// Returns the unsoundness class for this category.
    #[allow(clippy::enum_glob_use)]
    pub const fn class(self) -> UnsoundnessClass {
        use UnsoundnessCategory::*;
        use UnsoundnessClass::*;
        match self {
            ConstantZeroFallback
            | InternalWorkaround
            | ChcFallback
            | TypeSortFallback
            | SignednessFallback
            | UnsupportedConstructFallback
            | UnconstrainedAssignment
            | BmcStoreCoercionFallback
            | StoreDroppedTransition
            | DivergingCallDrop
            | KaniMemOverapprox
            | OffsetProvenanceUnresolved
            | InferablePredicate
            | FpBitvectorEncoding
            | RoundingAssertionBypass
            // VecFieldFallback / PointeeSynthesisFallback substitute a FRESH,
            // solver-controlled symbolic for a value the program actually
            // produced (a Vec field load; a pointee load). As their own docs
            // state, that is UNSOUND — the solver can pick a value that makes a
            // failing assertion pass (a false PROVED), unlike a universally-
            // quantified input havoc. They must demote, not be a silent NOTE.
            | VecFieldFallback
            | PointeeSynthesisFallback => Demoted,
            AssertUntranslatable
            | HeapCheckUntranslatable
            | HeapCheckUnknownLayout
            | IteratorUnsoundness
            | BigIntUnsoundness => FailClosed,
            AssumeDroppedTransition
            | ChcCoerceEqDrop
            | ChcTranslationDrop
            | ChcSoundHavocDrop
            | IntoOptionDrop
            | AbstractedFallback
            | UnhandledCalls
            | SortHarmonizeFreshVar
            | PtrMetadataUnconstrained
            | StaticInitIncomplete
            | AggregateEncodingGap
            | StubApproximation => SoundApproximation,
        }
    }

    /// Returns the stable JSON field name used in driver classification tables.
    #[allow(clippy::enum_glob_use)]
    pub const fn json_key(self) -> &'static str {
        use UnsoundnessCategory::*;
        match self {
            ConstantZeroFallback => "constant_zero_fallback",
            InternalWorkaround => "internal_workaround",
            ChcFallback => "chc_fallback",
            TypeSortFallback => "type_sort_fallback",
            SignednessFallback => "signedness_fallback",
            UnsupportedConstructFallback => "unsupported_construct_fallback",
            UnconstrainedAssignment => "unconstrained_assignment",
            AssertUntranslatable => "assert_untranslatable",
            HeapCheckUntranslatable => "heap_check_untranslatable",
            HeapCheckUnknownLayout => "heap_check_unknown_layout",
            IteratorUnsoundness => "iterator_unsoundness",
            BigIntUnsoundness => "bigint_unsoundness",
            BmcStoreCoercionFallback => "bmc_store_coercion_fallback",
            AssumeDroppedTransition => "assume_dropped_transition",
            ChcCoerceEqDrop => "chc_coerce_eq_drop",
            ChcTranslationDrop => "chc_translation_drop",
            ChcSoundHavocDrop => "chc_sound_havoc_drop",
            StoreDroppedTransition => "store_dropped_transition",
            IntoOptionDrop => "into_option_drop",
            AbstractedFallback => "abstracted_fallback",
            VecFieldFallback => "vec_field_fallback",
            PointeeSynthesisFallback => "pointee_synthesis_fallback",
            UnhandledCalls => "unhandled_calls",
            DivergingCallDrop => "diverging_call_drop",
            KaniMemOverapprox => "kani_mem_overapprox",
            OffsetProvenanceUnresolved => "offset_provenance_unresolved",
            SortHarmonizeFreshVar => "sort_harmonize_fresh_var",
            InferablePredicate => "inferable_predicate",
            PtrMetadataUnconstrained => "ptr_metadata_unconstrained",
            StaticInitIncomplete => "static_init_incomplete",
            FpBitvectorEncoding => "fp_bitvector_encoding",
            AggregateEncodingGap => "aggregate_encoding_gap",
            StubApproximation => "stub_approximation",
            RoundingAssertionBypass => "rounding_assertion_bypass",
        }
    }
}

/// Common counter surface for diagnostics metadata structs.
///
/// This unifies "is anything recorded?" checks and total-count queries across
/// the multiple `*Info` types used in `.kani-metadata.json`.
pub trait DiagnosticCounters {
    /// Total number of diagnostic events represented by this struct.
    fn total_count(&self) -> usize;

    /// Whether this diagnostic struct records zero events.
    fn is_empty(&self) -> bool {
        self.total_count() == 0
    }
}
/// Information about iterator verification that was skipped due to sort mismatches (#1929).
/// Non-zero counts indicate UNSOUND verification - iterator constraints were lost.
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct IteratorUnsoundnessInfo {
    /// Count of CHC iterator stubs that skipped verification due to non-datatype iterator sorts.
    pub chc_skip_count: usize,
    /// Count of BMC iterator stubs that skipped verification due to sort mismatches.
    pub bmc_skip_count: usize,
    /// Part of #3080: per-harness demotion granularity.
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub per_harness: BTreeMap<String, usize>,
}

impl IteratorUnsoundnessInfo {
    /// Returns true if any unsoundness was detected.
    pub fn has_unsoundness(&self) -> bool {
        !self.is_empty()
    }

    /// Returns the total count of skipped iterator verifications.
    pub fn total_skip_count(&self) -> usize {
        self.total_count()
    }
}

impl DiagnosticCounters for IteratorUnsoundnessInfo {
    fn total_count(&self) -> usize {
        self.chc_skip_count + self.bmc_skip_count
    }
}

impl DiagnosticCounters for ChcTranslationDropInfo {
    fn total_count(&self) -> usize {
        self.place_count + self.constant_count + self.field_projection_count
    }
}

/// Information about BigInt/BigRational verification that was skipped due to sort mismatches (#1989).
/// Non-zero counts indicate UNSOUND verification - BigInt constraints were lost.
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct BigIntUnsoundnessInfo {
    /// Count of CHC BigInt stubs that skipped verification due to sort mismatches.
    pub chc_skip_count: usize,
    /// Part of #3080: per-harness demotion granularity.
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub per_harness: BTreeMap<String, usize>,
}

impl BigIntUnsoundnessInfo {
    /// Returns true if any unsoundness was detected.
    pub fn has_unsoundness(&self) -> bool {
        !self.is_empty()
    }
}

/// Information about CHC type/size fallback defaults used during encoding (#2234).
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct ChcFallbackInfo {
    /// Total fallback trigger count across all translated functions in this crate.
    pub total_count: usize,
    /// Per-function fallback counts (function/harness name -> count).
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub per_harness: BTreeMap<String, usize>,
}

impl ChcFallbackInfo {
    /// Returns true if any fallback defaults were used.
    pub fn has_fallbacks(&self) -> bool {
        !self.is_empty()
    }
}

/// Information about CHC call-result equality constraints dropped due to sort mismatch (#2235).
/// Non-zero counts indicate destination locals were left unconstrained after call returns.
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct ChcCoerceEqDropInfo {
    /// Total dropped-constraint count across all translated functions in this crate.
    pub total_count: usize,
    /// Per-function dropped-constraint counts (function/harness name -> count).
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub per_harness: BTreeMap<String, usize>,
}

impl ChcCoerceEqDropInfo {
    /// Returns true if any constraints were dropped.
    pub fn has_drops(&self) -> bool {
        !self.is_empty()
    }
}

/// Information about dropped `kani::assume` semantics in CHC codegen (#2584).
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct AssumeDroppedTransitionInfo {
    /// Total count of dropped assume semantics across all functions in this crate.
    pub count: usize,
    /// Part of #3080: per-harness demotion granularity.
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub per_harness: BTreeMap<String, usize>,
}

impl AssumeDroppedTransitionInfo {
    /// Returns true if any assume semantics were dropped.
    pub fn has_drops(&self) -> bool {
        !self.is_empty()
    }
}

/// Information about dropped store transitions in CHC codegen (#2424).
/// Non-zero count indicates memory-store operations could not be faithfully
/// translated and were dropped. Subsequent reads return stale/symbolic values,
/// making verification results unsound (false proofs or false counterexamples).
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct StoreDroppedTransitionInfo {
    /// Total count of dropped store transitions across all functions in this crate.
    pub count: usize,
    /// Part of #2966: per-harness demotion granularity.
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub per_harness: BTreeMap<String, usize>,
}

impl StoreDroppedTransitionInfo {
    /// Returns true if any store transitions were dropped.
    pub fn has_drops(&self) -> bool {
        !self.is_empty()
    }
}

/// Information about CHC translation drops from immutable/static paths (#2770).
/// Non-zero counts indicate expression translation returned `None` for unsupported
/// flattened-place reads, scalar constants, or non-field projections.
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct ChcTranslationDropInfo {
    /// Count of dropped flattened-place translations.
    pub place_count: usize,
    /// Count of dropped scalar-constant translations.
    pub constant_count: usize,
    /// Count of dropped unsupported projection translations.
    pub field_projection_count: usize,
    /// Part of #2966: per-harness demotion granularity (combined total).
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub per_harness: BTreeMap<String, usize>,
    /// Part of #3791: per-harness drop fallback reasons.
    /// Outer key: fn_name, inner key: reason string, value: count.
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub per_harness_reasons: BTreeMap<String, BTreeMap<String, usize>>,
    /// Part of #3794: per-harness translation-drop site reasons.
    /// Outer key: fn_name, inner key: site reason code, value: count.
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub per_harness_translation_sites: BTreeMap<String, BTreeMap<String, usize>>,
    /// Recognized-clean SoundHavoc drops (the `ChcSoundHavocDrop` category).
    /// These are the subset of sound-fallback sites whose per-reason audit
    /// classifies them as a certified fresh unconstrained havoc (universally
    /// quantified), so a PROOF under them is valid for all concrete values.
    /// Tracked SEPARATELY from `place_count` (which now holds only the
    /// non-recognized-clean / fail-close translation drops) and DELIBERATELY
    /// excluded from `total_count()`, so a proof whose only fallbacks are
    /// SoundHavoc reports a clean (non-qualified) success. The driver still
    /// surfaces it as a SOUND_APPROXIMATION category so a spurious
    /// counterexample from a genuine over-approximation is tagged
    /// `OverApproximation` (Unknown), never a false positive.
    #[serde(default)]
    pub sound_havoc_count: usize,
    /// Per-harness SoundHavoc drop counts (crate-relative fn names).
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub sound_havoc_per_harness: BTreeMap<String, usize>,
}

impl ChcTranslationDropInfo {
    /// Returns true if any CHC translation drops were recorded.
    pub fn has_drops(&self) -> bool {
        !self.is_empty()
    }
}

/// Information about constant zero-value fallbacks in statement codegen (#2463).
/// Non-zero count indicates MIR constants whose values could not be extracted were
/// silently replaced with zero. This is unsound when the actual value is non-zero.
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct ConstantZeroFallbackInfo {
    /// Total count of constants replaced with zero across all functions in this crate.
    pub count: usize,
    /// Part of #3080: per-harness demotion granularity.
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub per_harness: BTreeMap<String, usize>,
}

impl ConstantZeroFallbackInfo {
    /// Returns true if any zero-value fallbacks were used.
    pub fn has_fallbacks(&self) -> bool {
        !self.is_empty()
    }
}

/// Information about unhandled function calls in CHC call dispatch (#2573).
/// Non-zero count indicates function calls fell through all dispatch stages,
/// leaving destination locals unconstrained. This is an over-approximation:
/// the solver treats the return value as unconstrained, which can mask real bugs
/// or produce false proofs when composed with other unconstrained values.
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct UnhandledCallInfo {
    /// Total count of function calls that fell through to the catch-all dispatch path.
    pub count: usize,
    /// Part of #2966: per-harness demotion granularity.
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub per_harness: BTreeMap<String, usize>,
}

impl UnhandledCallInfo {
    /// Returns true if any unhandled calls were encountered.
    pub fn has_unhandled_calls(&self) -> bool {
        !self.is_empty()
    }
}

/// Information about diverging calls (target=None) silently dropped without
/// emitting CHC rules (#3164). Non-zero count indicates call dispatch claimed
/// the call but emitted no rule, silently pruning the path from verification.
/// Most drops are on genuinely unreachable panic paths, but without propagation
/// to metadata there is no way to distinguish safe drops from unsound ones.
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct DivergingCallDropInfo {
    /// Total count of diverging calls dropped without emitting rules.
    pub count: usize,
    /// Per-harness demotion granularity.
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub per_harness: BTreeMap<String, usize>,
}

impl DivergingCallDropInfo {
    /// Returns true if any diverging call drops were recorded.
    pub fn has_drops(&self) -> bool {
        !self.is_empty()
    }
}

/// Information about pointer-offset / deref allocation-bound safety checks that
/// were silently SKIPPED because the base pointer's obj_id lane did not
/// const-fold (unresolved provenance — e.g. a pointer from `<[T]>::as_ptr()`
/// whose stdlib MIR is unavailable). The bound check is fail-open, so a non-zero
/// count means an out-of-bounds offset+deref could be falsely proven Safe. This
/// category demotes the harness so a safety verdict is never claimed without a
/// verified bound.
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct OffsetProvenanceUnresolvedInfo {
    /// Total count of offset/deref bound checks skipped on unresolved provenance.
    pub count: usize,
    /// Per-harness demotion granularity.
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub per_harness: BTreeMap<String, usize>,
}

/// Formatting/panic calls error-blocked in CHC dispatch (#3379).
/// These are dead-ended (not over-approximation) — the path is terminated.
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct ErrorBlockedFmtInfo {
    pub count: usize,
}

/// Known stdlib calls left unconstrained in CHC dispatch (#3379).
/// Recognized over-approximation — distinct from true unhandled calls.
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct KnownStdlibUnconstrainedInfo {
    pub count: usize,
}

/// Calls encoded with solver-inferable function summaries (#3395).
/// Instead of leaving the destination unconstrained, the return value is constrained
/// to equal an uninterpreted function of the call arguments. PDR synthesizes a
/// consistent function summary. This is not replacement-quality proof evidence
/// until summary inference is independently validated.
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct InferablePredicateInfo {
    pub count: usize,
    /// Part of #3493: per-harness inferable predicate counts for CTREX classification.
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub per_harness: BTreeMap<String, usize>,
    /// Part of #4031: per-harness inferable summary names for provenance.
    /// Outer key: fn_name, inner key: P_inf_<callee> name, value: count.
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub per_harness_summaries: BTreeMap<String, BTreeMap<String, usize>>,
}

/// Count of assertion operands that CHC could not translate and handled fail-closed.
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct AssertUntranslatableInfo {
    /// Number of untranslatable assertion operands.
    pub count: usize,
}

impl AssertUntranslatableInfo {
    /// Returns true if any untranslatable assertions were observed.
    pub fn has_untranslatable(&self) -> bool {
        !self.is_empty()
    }
}

/// Count of heap-check predicates that CHC could not translate and handled fail-closed.
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct HeapCheckUntranslatableInfo {
    /// Number of untranslatable heap-check predicates.
    pub count: usize,
}

impl HeapCheckUntranslatableInfo {
    /// Returns true if any untranslatable heap checks were observed.
    pub fn has_untranslatable(&self) -> bool {
        !self.is_empty()
    }
}

/// Count of unknown-layout heap checks encountered by CHC.
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct HeapCheckUnknownLayoutInfo {
    /// Number of heap checks on unknown-layout types.
    pub count: usize,
}

impl HeapCheckUnknownLayoutInfo {
    /// Returns true if any unknown-layout heap checks were observed.
    pub fn has_unknown_layout(&self) -> bool {
        !self.is_empty()
    }
}

/// Information about type-sort resolution fallbacks in CHC codegen (#2705).
/// Non-zero count indicates type resolution fell back to a hardcoded sort
/// (typically bv32), making the verification model narrower than the actual
/// Rust types. Properties proved under the fallback sort may not hold for
/// the real type widths.
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct TypeSortFallbackInfo {
    /// Total count of type-sort fallbacks across all functions in this crate.
    pub count: usize,
    /// Per-function type-sort fallback counts (function/harness name -> count).
    /// Part of #2959: per-harness demotion granularity.
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub per_harness: BTreeMap<String, usize>,
}

impl TypeSortFallbackInfo {
    /// Returns true if any type-sort fallbacks were used.
    pub fn has_fallbacks(&self) -> bool {
        !self.is_empty()
    }
}

/// Information about signedness fallbacks in CHC/BMC codegen (#2749).
/// Non-zero count indicates signedness could not be determined from MIR types,
/// and an operation-specific default was used. For div/rem and cast/coerce,
/// this means the verification model may use incorrect signedness semantics
/// (e.g., bvudiv instead of bvsdiv for signed values, or vice versa).
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct SignednessFallbackInfo {
    /// Total count of signedness fallback events across all functions.
    pub count: usize,
    /// Per-function signedness fallback counts (function/harness name -> count).
    /// Part of #2959: per-harness demotion granularity.
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub per_harness: BTreeMap<String, usize>,
}

impl SignednessFallbackInfo {
    /// Returns true if any signedness fallbacks were used.
    pub fn has_fallbacks(&self) -> bool {
        !self.is_empty()
    }
}

/// Information about statement `IntoOption` Result→None drops (#2597).
/// Non-zero count indicates codegen skipped one or more translation paths
/// after converting a `Result::Err` to `None`.
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct IntoOptionDropInfo {
    /// Total count of dropped `Result::Err` values converted by `IntoOption`.
    pub count: usize,
    /// Part of #3080: per-harness demotion granularity.
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub per_harness: BTreeMap<String, usize>,
}

impl IntoOptionDropInfo {
    /// Returns true if any `IntoOption` Result drops were observed.
    pub fn has_drops(&self) -> bool {
        !self.is_empty()
    }
}

/// Pre-inlined collection internal workaround information (#1662).
/// Non-zero count indicates statement codegen used symbolic approximations
/// for rustc pre-inlined BTree, RawVec, or other collection internals.
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct InternalWorkaroundInfo {
    /// Total count of internal workaround hits.
    pub count: usize,
    /// Part of #3080: per-harness demotion granularity.
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub per_harness: BTreeMap<String, usize>,
}

impl InternalWorkaroundInfo {
    /// Returns true if any internal workarounds were used.
    pub fn has_workarounds(&self) -> bool {
        !self.is_empty()
    }
}

/// Abstracted stdlib fallback information (#1691).
/// Non-zero count indicates statement codegen used symbolic approximations
/// for pre-inlined UTF8/Cow/String internals not intercepted at reachability.
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct AbstractedFallbackInfo {
    /// Total count of abstracted fallback hits.
    pub count: usize,
    /// Part of #3080: per-harness demotion granularity.
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub per_harness: BTreeMap<String, usize>,
}

impl AbstractedFallbackInfo {
    /// Returns true if any abstracted fallbacks were used.
    pub fn has_fallbacks(&self) -> bool {
        !self.is_empty()
    }
}

/// Vec field fallback information (#2733).
/// Non-zero count indicates `vec_field_select` encountered a Vec expression with
/// non-datatype sort and returned a fresh symbolic variable instead of a real
/// field access. This is unsound because the actual field value is lost.
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct VecFieldFallbackInfo {
    /// Total count of Vec field fallback hits.
    pub count: usize,
    /// Part of #3080: per-harness demotion granularity.
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub per_harness: BTreeMap<String, usize>,
}

impl VecFieldFallbackInfo {
    /// Returns true if any Vec field fallbacks were used.
    pub fn has_fallbacks(&self) -> bool {
        !self.is_empty()
    }
}

/// Pointee synthesis fallback information (#3013).
/// Non-zero count indicates `synthesize_pointee_expr` created fresh unconstrained
/// symbolic variables for pointer dereferences when tracking was incomplete.
/// This is unsound because the solver can choose any value for the symbolic,
/// potentially proving assertions that would fail at runtime.
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct PointeeSynthesisFallbackInfo {
    /// Total count of pointee synthesis fallback hits.
    pub count: usize,
    /// Part of #3080: per-harness demotion granularity.
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub per_harness: BTreeMap<String, usize>,
}

impl PointeeSynthesisFallbackInfo {
    /// Returns true if any pointee synthesis fallbacks were used.
    pub fn has_fallbacks(&self) -> bool {
        !self.is_empty()
    }
}

/// Unsupported construct fallback information (#3017).
/// Non-zero count indicates `ctx.unsupported()` was called at a code path that
/// proceeds with incorrect or fallback data rather than bailing early. This is
/// unsound because the solver operates on a model that doesn't match the actual
/// Rust semantics (e.g., defaulting to variant 0 for multi-variant enums,
/// using positional discriminant values for #[repr] enums).
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct UnsupportedConstructFallbackInfo {
    /// Total count of unsupported construct fallback hits.
    pub count: usize,
    /// Part of #3080: per-harness demotion granularity.
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub per_harness: BTreeMap<String, usize>,
}

impl UnsupportedConstructFallbackInfo {
    /// Returns true if any unsupported construct fallbacks were used.
    pub fn has_fallbacks(&self) -> bool {
        !self.is_empty()
    }
}

/// Unconstrained assignment information (#3192).
/// Non-zero count indicates BMC `codegen_assign` received a `None` from
/// `codegen_rvalue`, leaving the LHS SSA variable declared but unconstrained.
/// The solver can pick any value for these variables, creating a potential
/// false-proof vector (solver might satisfy downstream assertions with a
/// value the real program would never produce). Distinct from
/// `unsupported_construct_fallback` which tracks paths that proceed with
/// incorrect fallback data rather than bailing.
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct UnconstrainedAssignmentInfo {
    /// Total count of unconstrained assignment hits.
    pub count: usize,
    /// Part of #3192: per-harness demotion granularity.
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub per_harness: BTreeMap<String, usize>,
}

/// BMC store coercion fallback information (#3064).
/// Non-zero count indicates BMC store operations could not coerce value sorts
/// to match array element sorts, and fresh unconstrained symbolic variables
/// were substituted. The solver can pick any value for these symbolics,
/// potentially producing false proofs.
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct BmcStoreCoercionFallbackInfo {
    /// Total count of BMC store coercion fallback hits.
    pub count: usize,
    /// Part of #3064: per-harness demotion granularity.
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub per_harness: BTreeMap<String, usize>,
}

impl BmcStoreCoercionFallbackInfo {
    /// Returns true if any BMC store coercion fallbacks were used.
    pub fn has_fallbacks(&self) -> bool {
        !self.is_empty()
    }
}

/// kani::mem over-approximation information (#3165).
/// Non-zero count indicates kani::mem memory safety predicates (is_ptr_aligned,
/// same_allocation, in_bounds, etc.) were over-approximated as `true`.
/// Replacement-quality PROOFs hard-gate on this counter because the harness has
/// no memory safety assurance from these checks.
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct KaniMemOverapproxInfo {
    /// Total count of kani::mem predicates over-approximated as true.
    pub count: usize,
    /// Part of #3165: per-harness granularity.
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub per_harness: BTreeMap<String, usize>,
}

/// Sort harmonize fresh-variable fallback information (#3263).
/// Non-zero count indicates sort harmonization created fresh unconstrained
/// symbolic variables when Datatype<->BitVec flatten/unflatten failed or
/// sorts were otherwise incompatible at phi merge points. This is a sound
/// over-approximation (universally quantified), but destroys all concrete
/// value information flowing through the affected merge point.
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct SortHarmonizeFreshVarInfo {
    /// Total count of fresh-variable fallbacks across all functions in this crate.
    pub count: usize,
    /// Per-harness granularity for demotion decisions.
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub per_harness: BTreeMap<String, usize>,
}

impl SortHarmonizeFreshVarInfo {
    /// Returns true if any sort harmonize fresh-variable fallbacks were used.
    pub fn has_fallbacks(&self) -> bool {
        !self.is_empty()
    }
}

/// PtrMetadata unconstrained symbolic fallback (#3447).
/// Non-zero count indicates `PtrMetadata` codegen created fresh unconstrained
/// symbolic variables because the metadata (length or vtable pointer) could not
/// be resolved from tracked state. Sound over-approximation — universally
/// quantified over all possible metadata values.
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct PtrMetadataUnconstrainedInfo {
    pub count: usize,
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub per_harness: BTreeMap<String, usize>,
}

/// Static initializer incomplete encoding (#3447).
/// Non-zero count indicates `register_statics` had an allocation for a static
/// but `static_init_from_alloc` returned `None` (composite type encoding gap).
/// The static is left unconstrained — sound over-approximation.
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct StaticInitIncompleteInfo {
    pub count: usize,
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub per_harness: BTreeMap<String, usize>,
}

/// Floating-point bitvector encoding (#3447).
/// Non-zero count indicates float types (f32/f64) were mapped to bitvectors
/// instead of SMT floating-point sorts. All FP arithmetic uses BV operations
/// which cannot model IEEE 754 semantics (rounding, NaN, etc.).
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct FpBitvectorEncodingInfo {
    pub count: usize,
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub per_harness: BTreeMap<String, usize>,
}

/// Aggregate encoding gap (#3447).
/// Non-zero count indicates ADT/enum aggregate construction or discriminant
/// translation fell back to fresh unconstrained symbolic variables due to
/// sort mismatches, unresolvable deref chains, or non-Datatype sorts.
/// Sound over-approximation — universally quantified over all possible values.
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct AggregateEncodingGapInfo {
    pub count: usize,
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub per_harness: BTreeMap<String, usize>,
    /// Per-harness gap REASONS, which for the nested-call lane carry the
    /// callee: `inline_nested_call_fallback_symbolic@<callee_path>`.
    ///
    /// The walker records these at the point of decision
    /// (`terminator_exec.rs`, `ctx.record_aggregate_gap`) and until now nothing
    /// drained them outside unit tests, so the count was reportable and the
    /// CAUSE was not. That matters more here than for most counters: a
    /// 2026-08-23 corpus run had `nested_call_overapprox` on 62 non-parity
    /// rows — 42 of them `oracle=success, observed=fail`, i.e. spurious
    /// counterexamples built on an invented return value — and naming the
    /// responsible callees is the whole difference between "over-approximated
    /// somewhere" and a ranked fix list.
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub per_harness_reasons: BTreeMap<String, BTreeMap<String, usize>>,
}

/// Stub approximation (#3447).
/// Non-zero count indicates a CHC stub (closure combinator, numeric argument,
/// or store value coercion) returned a fresh unconstrained symbolic variable
/// instead of a precisely-encoded value. Sound over-approximation.
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct StubApproximationInfo {
    pub count: usize,
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub per_harness: BTreeMap<String, usize>,
}

/// Float rounding assertion bypass (#3779).
/// Non-zero count indicates float rounding assertions (e.g. `|x - ceil(x)| <= 1.0`)
/// were weakened to a finiteness tautology by the assertion-pattern recognizer.
/// Replacement-quality PROOFs hard-gate on this counter because the explicit
/// assertion is not checked as written.
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct RoundingAssertionBypassInfo {
    pub count: usize,
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub per_harness: BTreeMap<String, usize>,
}

macro_rules! impl_diagnostic_counters_from_field {
    ($($ty:ty => $field:ident),+ $(,)?) => {
        $(
            impl DiagnosticCounters for $ty {
                fn total_count(&self) -> usize {
                    self.$field
                }
            }
        )+
    };
}

impl_diagnostic_counters_from_field!(
    BigIntUnsoundnessInfo => chc_skip_count,
    ChcFallbackInfo => total_count,
    ChcCoerceEqDropInfo => total_count,
    AssumeDroppedTransitionInfo => count,
    StoreDroppedTransitionInfo => count,
    ConstantZeroFallbackInfo => count,
    UnhandledCallInfo => count,
    ErrorBlockedFmtInfo => count,
    KnownStdlibUnconstrainedInfo => count,
    InferablePredicateInfo => count,
    DivergingCallDropInfo => count,
    AssertUntranslatableInfo => count,
    HeapCheckUntranslatableInfo => count,
    HeapCheckUnknownLayoutInfo => count,
    TypeSortFallbackInfo => count,
    SignednessFallbackInfo => count,
    IntoOptionDropInfo => count,
    InternalWorkaroundInfo => count,
    AbstractedFallbackInfo => count,
    VecFieldFallbackInfo => count,
    PointeeSynthesisFallbackInfo => count,
    UnsupportedConstructFallbackInfo => count,
    UnconstrainedAssignmentInfo => count,
    BmcStoreCoercionFallbackInfo => count,
    KaniMemOverapproxInfo => count,
    OffsetProvenanceUnresolvedInfo => count,
    SortHarmonizeFreshVarInfo => count,
    PtrMetadataUnconstrainedInfo => count,
    StaticInitIncompleteInfo => count,
    FpBitvectorEncodingInfo => count,
    AggregateEncodingGapInfo => count,
    StubApproximationInfo => count,
    RoundingAssertionBypassInfo => count,
);
#[cfg(test)]
mod tests {
    use super::*;
    use crate::KaniMetadata;

    #[test]
    fn test_iterator_unsoundness_info_has_unsoundness() {
        let zero_info =
            IteratorUnsoundnessInfo { chc_skip_count: 0, bmc_skip_count: 0, ..Default::default() };
        assert!(!zero_info.has_unsoundness());

        let chc_only =
            IteratorUnsoundnessInfo { chc_skip_count: 1, bmc_skip_count: 0, ..Default::default() };
        assert!(chc_only.has_unsoundness());

        let bmc_only =
            IteratorUnsoundnessInfo { chc_skip_count: 0, bmc_skip_count: 2, ..Default::default() };
        assert!(bmc_only.has_unsoundness());

        let both =
            IteratorUnsoundnessInfo { chc_skip_count: 3, bmc_skip_count: 4, ..Default::default() };
        assert!(both.has_unsoundness());
        assert_eq!(both.total_skip_count(), 7);
    }

    #[test]
    fn test_diagnostic_counters_trait_totals_and_empty() {
        fn assert_counter<T: DiagnosticCounters>(value: &T, total: usize, is_empty: bool) {
            assert_eq!(value.total_count(), total);
            assert_eq!(value.is_empty(), is_empty);
        }

        assert_counter(
            &IteratorUnsoundnessInfo { chc_skip_count: 2, bmc_skip_count: 3, ..Default::default() },
            5,
            false,
        );
        assert_counter(&BigIntUnsoundnessInfo { chc_skip_count: 0, ..Default::default() }, 0, true);
        assert_counter(&ChcFallbackInfo { total_count: 4, per_harness: BTreeMap::new() }, 4, false);
        assert_counter(
            &StoreDroppedTransitionInfo { count: 0, per_harness: Default::default() },
            0,
            true,
        );
        assert_counter(&InternalWorkaroundInfo { count: 6, ..Default::default() }, 6, false);
        assert_counter(&AbstractedFallbackInfo { count: 1, ..Default::default() }, 1, false);
        assert_counter(&VecFieldFallbackInfo { count: 9, ..Default::default() }, 9, false);
    }

    #[test]
    fn test_replacement_quality_hard_gate_categories_are_demoted() {
        use UnsoundnessCategory as UC;

        let hard_gates = [
            UC::BmcStoreCoercionFallback,
            UC::StoreDroppedTransition,
            UC::DivergingCallDrop,
            UC::KaniMemOverapprox,
            UC::FpBitvectorEncoding,
            UC::RoundingAssertionBypass,
            UC::InferablePredicate,
        ];

        for category in hard_gates {
            assert_eq!(
                category.class(),
                UnsoundnessClass::Demoted,
                "{} must hard-gate replacement-quality PROOFs",
                category.json_key()
            );
        }
    }

    #[test]
    fn test_iterator_unsoundness_serialization() {
        // Metadata without iterator_unsoundness should serialize without the field
        let metadata_none = KaniMetadata {
            crate_name: "test".to_string(),
            proof_harnesses: vec![],
            unsupported_features: vec![],
            test_harnesses: vec![],
            contracted_functions: vec![],
            autoharness_md: None,
            iterator_unsoundness: None,
            bigint_unsoundness: None,
            chc_fallbacks: None,
            chc_translation_drops: None,
            chc_coerce_eq_drops: None,
            assume_dropped_transitions: None,
            store_dropped_transitions: None,
            constant_zero_fallbacks: None,
            unhandled_calls: None,
            diverging_call_drops: None,
            assert_untranslatable: None,
            heap_check_untranslatable: None,
            heap_check_unknown_layout: None,
            type_sort_fallbacks: None,
            signedness_fallbacks: None,
            into_option_drops: None,
            internal_workarounds: None,
            abstracted_fallbacks: None,
            vec_field_fallbacks: None,
            pointee_synthesis_fallbacks: None,
            unsupported_construct_fallbacks: None,
            unconstrained_assignments: None,
            bmc_store_coercion_fallbacks: None,
            kani_mem_overapprox: None,
            offset_provenance_unresolved: None,
            sort_harmonize_fresh_var_fallbacks: None,
            error_blocked_fmt: None,
            known_stdlib_unconstrained: None,
            inferable_predicates: None,
            ptr_metadata_unconstrained: None,
            static_init_incomplete: None,
            fp_bitvector_encoding: None,
            aggregate_encoding_gap: None,
            stub_approximation: None,
            rounding_assertion_bypass: None,
        };
        let json = serde_json::to_string(&metadata_none).expect("serialize metadata_none");
        assert!(!json.contains("iterator_unsoundness"));
        assert!(!json.contains("bigint_unsoundness"));
        assert!(!json.contains("chc_fallbacks"));
        assert!(!json.contains("constant_zero_fallbacks"));

        // Metadata with iterator_unsoundness should include it
        let metadata_with = KaniMetadata {
            crate_name: "test".to_string(),
            proof_harnesses: vec![],
            unsupported_features: vec![],
            test_harnesses: vec![],
            contracted_functions: vec![],
            autoharness_md: None,
            iterator_unsoundness: Some(IteratorUnsoundnessInfo {
                chc_skip_count: 5,
                bmc_skip_count: 3,
                ..Default::default()
            }),
            bigint_unsoundness: None,
            chc_fallbacks: None,
            chc_translation_drops: None,
            chc_coerce_eq_drops: None,
            assume_dropped_transitions: None,
            store_dropped_transitions: None,
            constant_zero_fallbacks: None,
            unhandled_calls: None,
            diverging_call_drops: None,
            assert_untranslatable: None,
            heap_check_untranslatable: None,
            heap_check_unknown_layout: None,
            type_sort_fallbacks: None,
            signedness_fallbacks: None,
            into_option_drops: None,
            internal_workarounds: None,
            abstracted_fallbacks: None,
            vec_field_fallbacks: None,
            pointee_synthesis_fallbacks: None,
            unsupported_construct_fallbacks: None,
            unconstrained_assignments: None,
            bmc_store_coercion_fallbacks: None,
            kani_mem_overapprox: None,
            offset_provenance_unresolved: None,
            sort_harmonize_fresh_var_fallbacks: None,
            error_blocked_fmt: None,
            known_stdlib_unconstrained: None,
            inferable_predicates: None,
            ptr_metadata_unconstrained: None,
            static_init_incomplete: None,
            fp_bitvector_encoding: None,
            aggregate_encoding_gap: None,
            stub_approximation: None,
            rounding_assertion_bypass: None,
        };
        let json = serde_json::to_string(&metadata_with).expect("serialize metadata_with");
        assert!(json.contains("iterator_unsoundness"));
        assert!(json.contains("chc_skip_count"));
        assert!(json.contains("bmc_skip_count"));

        // Verify round-trip
        let deserialized: KaniMetadata =
            serde_json::from_str(&json).expect("deserialize round-trip");
        let info = deserialized.iterator_unsoundness.expect("iterator_unsoundness present");
        assert_eq!(info.chc_skip_count, 5);
        assert_eq!(info.bmc_skip_count, 3);
    }

    #[test]
    fn test_iterator_unsoundness_deserialization_missing_field() {
        // Old metadata without iterator_unsoundness field should deserialize with None
        let json = r#"{
            "crate_name": "test",
            "proof_harnesses": [],
            "unsupported_features": [],
            "test_harnesses": [],
            "contracted_functions": [],
            "autoharness_md": null
        }"#;
        let metadata: KaniMetadata = serde_json::from_str(json).expect("deserialize missing field");
        assert!(metadata.iterator_unsoundness.is_none());
        assert!(metadata.bigint_unsoundness.is_none());
        assert!(metadata.chc_fallbacks.is_none());
    }

    #[test]
    fn test_bigint_unsoundness_deserialization_missing_field() {
        // Old metadata without bigint_unsoundness field should deserialize with None
        // This ensures backward compatibility with metadata created before #1989
        let json = r#"{
            "crate_name": "test",
            "proof_harnesses": [],
            "unsupported_features": [],
            "test_harnesses": [],
            "contracted_functions": [],
            "autoharness_md": null,
            "iterator_unsoundness": {"chc_skip_count": 1, "bmc_skip_count": 0}
        }"#;
        let metadata: KaniMetadata =
            serde_json::from_str(json).expect("deserialize bigint missing");
        assert!(metadata.iterator_unsoundness.is_some());
        assert!(metadata.bigint_unsoundness.is_none());
        assert!(metadata.chc_fallbacks.is_none());
    }

    #[test]
    fn test_bigint_unsoundness_info_has_unsoundness() {
        let zero_info = BigIntUnsoundnessInfo { chc_skip_count: 0, ..Default::default() };
        assert!(!zero_info.has_unsoundness());

        let with_count = BigIntUnsoundnessInfo { chc_skip_count: 5, ..Default::default() };
        assert!(with_count.has_unsoundness());
    }

    #[test]
    fn test_bigint_unsoundness_serialization() {
        // Metadata without bigint_unsoundness should serialize without the field
        let metadata_none = KaniMetadata {
            crate_name: "test".to_string(),
            proof_harnesses: vec![],
            unsupported_features: vec![],
            test_harnesses: vec![],
            contracted_functions: vec![],
            autoharness_md: None,
            iterator_unsoundness: None,
            bigint_unsoundness: None,
            chc_fallbacks: None,
            chc_translation_drops: None,
            chc_coerce_eq_drops: None,
            assume_dropped_transitions: None,
            store_dropped_transitions: None,
            constant_zero_fallbacks: None,
            unhandled_calls: None,
            diverging_call_drops: None,
            assert_untranslatable: None,
            heap_check_untranslatable: None,
            heap_check_unknown_layout: None,
            type_sort_fallbacks: None,
            signedness_fallbacks: None,
            into_option_drops: None,
            internal_workarounds: None,
            abstracted_fallbacks: None,
            vec_field_fallbacks: None,
            pointee_synthesis_fallbacks: None,
            unsupported_construct_fallbacks: None,
            unconstrained_assignments: None,
            bmc_store_coercion_fallbacks: None,
            kani_mem_overapprox: None,
            offset_provenance_unresolved: None,
            sort_harmonize_fresh_var_fallbacks: None,
            error_blocked_fmt: None,
            known_stdlib_unconstrained: None,
            inferable_predicates: None,
            ptr_metadata_unconstrained: None,
            static_init_incomplete: None,
            fp_bitvector_encoding: None,
            aggregate_encoding_gap: None,
            stub_approximation: None,
            rounding_assertion_bypass: None,
        };
        let json = serde_json::to_string(&metadata_none).expect("serialize bigint metadata_none");
        assert!(!json.contains("bigint_unsoundness"));

        // Metadata with bigint_unsoundness should include it
        let metadata_with = KaniMetadata {
            crate_name: "test".to_string(),
            proof_harnesses: vec![],
            unsupported_features: vec![],
            test_harnesses: vec![],
            contracted_functions: vec![],
            autoharness_md: None,
            iterator_unsoundness: None,
            bigint_unsoundness: Some(BigIntUnsoundnessInfo {
                chc_skip_count: 3,
                ..Default::default()
            }),
            chc_fallbacks: None,
            chc_translation_drops: None,
            chc_coerce_eq_drops: None,
            assume_dropped_transitions: None,
            store_dropped_transitions: None,
            constant_zero_fallbacks: None,
            unhandled_calls: None,
            diverging_call_drops: None,
            assert_untranslatable: None,
            heap_check_untranslatable: None,
            heap_check_unknown_layout: None,
            type_sort_fallbacks: None,
            signedness_fallbacks: None,
            into_option_drops: None,
            internal_workarounds: None,
            abstracted_fallbacks: None,
            vec_field_fallbacks: None,
            pointee_synthesis_fallbacks: None,
            unsupported_construct_fallbacks: None,
            unconstrained_assignments: None,
            bmc_store_coercion_fallbacks: None,
            kani_mem_overapprox: None,
            offset_provenance_unresolved: None,
            sort_harmonize_fresh_var_fallbacks: None,
            error_blocked_fmt: None,
            known_stdlib_unconstrained: None,
            inferable_predicates: None,
            ptr_metadata_unconstrained: None,
            static_init_incomplete: None,
            fp_bitvector_encoding: None,
            aggregate_encoding_gap: None,
            stub_approximation: None,
            rounding_assertion_bypass: None,
        };
        let json = serde_json::to_string(&metadata_with).expect("serialize bigint metadata_with");
        assert!(json.contains("bigint_unsoundness"));
        assert!(json.contains("chc_skip_count"));

        // Verify round-trip
        let deserialized: KaniMetadata =
            serde_json::from_str(&json).expect("deserialize bigint round-trip");
        let info = deserialized.bigint_unsoundness.expect("bigint_unsoundness present");
        assert_eq!(info.chc_skip_count, 3);
    }

    #[test]
    fn test_deserialization_no_optional_unsoundness_fields() {
        // Old metadata without optional diagnostics fields should deserialize with None
        let json = r#"{
            "crate_name": "test",
            "proof_harnesses": [],
            "unsupported_features": [],
            "test_harnesses": [],
            "contracted_functions": [],
            "autoharness_md": null
        }"#;
        let metadata: KaniMetadata =
            serde_json::from_str(json).expect("deserialize no optional fields");
        assert!(metadata.bigint_unsoundness.is_none());
        assert!(metadata.iterator_unsoundness.is_none());
        assert!(metadata.chc_fallbacks.is_none());
    }

    #[test]
    fn test_chc_fallback_info_has_fallbacks() {
        let empty = ChcFallbackInfo { total_count: 0, per_harness: BTreeMap::new() };
        assert!(!empty.has_fallbacks());

        let mut per_harness = BTreeMap::new();
        per_harness.insert("probe".to_string(), 2);
        let with_count = ChcFallbackInfo { total_count: 2, per_harness };
        assert!(with_count.has_fallbacks());
    }

    #[test]
    fn test_chc_fallback_serialization() {
        let mut per_harness = BTreeMap::new();
        per_harness.insert("foo::harness".to_string(), 3);
        let metadata_with = KaniMetadata {
            crate_name: "test".to_string(),
            proof_harnesses: vec![],
            unsupported_features: vec![],
            test_harnesses: vec![],
            contracted_functions: vec![],
            autoharness_md: None,
            iterator_unsoundness: None,
            bigint_unsoundness: None,
            chc_fallbacks: Some(ChcFallbackInfo { total_count: 3, per_harness }),
            chc_translation_drops: None,
            chc_coerce_eq_drops: None,
            assume_dropped_transitions: None,
            store_dropped_transitions: None,
            constant_zero_fallbacks: None,
            unhandled_calls: None,
            diverging_call_drops: None,
            assert_untranslatable: None,
            heap_check_untranslatable: None,
            heap_check_unknown_layout: None,
            type_sort_fallbacks: None,
            signedness_fallbacks: None,
            into_option_drops: None,
            internal_workarounds: None,
            abstracted_fallbacks: None,
            vec_field_fallbacks: None,
            pointee_synthesis_fallbacks: None,
            unsupported_construct_fallbacks: None,
            unconstrained_assignments: None,
            bmc_store_coercion_fallbacks: None,
            kani_mem_overapprox: None,
            offset_provenance_unresolved: None,
            sort_harmonize_fresh_var_fallbacks: None,
            error_blocked_fmt: None,
            known_stdlib_unconstrained: None,
            inferable_predicates: None,
            ptr_metadata_unconstrained: None,
            static_init_incomplete: None,
            fp_bitvector_encoding: None,
            aggregate_encoding_gap: None,
            stub_approximation: None,
            rounding_assertion_bypass: None,
        };

        let json = serde_json::to_string(&metadata_with).expect("serialize fallback metadata");
        assert!(json.contains("chc_fallbacks"));
        assert!(json.contains("foo::harness"));
        assert!(json.contains("total_count"));

        let deserialized: KaniMetadata =
            serde_json::from_str(&json).expect("deserialize fallback round-trip");
        let info = deserialized.chc_fallbacks.expect("expected chc_fallbacks");
        assert_eq!(info.total_count, 3);
        assert_eq!(info.per_harness.get("foo::harness").copied(), Some(3));
    }

    #[test]
    fn test_chc_translation_drop_info_has_drops() {
        let empty = ChcTranslationDropInfo {
            place_count: 0,
            constant_count: 0,
            field_projection_count: 0,
            ..Default::default()
        };
        assert!(!empty.has_drops());

        let with_count = ChcTranslationDropInfo {
            place_count: 1,
            constant_count: 2,
            field_projection_count: 0,
            ..Default::default()
        };
        assert!(with_count.has_drops());
        assert_eq!(with_count.total_count(), 3);
    }

    #[test]
    fn test_chc_translation_drop_serialization() {
        let metadata_with = KaniMetadata {
            crate_name: "test".to_string(),
            proof_harnesses: vec![],
            unsupported_features: vec![],
            test_harnesses: vec![],
            contracted_functions: vec![],
            autoharness_md: None,
            iterator_unsoundness: None,
            bigint_unsoundness: None,
            chc_fallbacks: None,
            chc_translation_drops: Some(ChcTranslationDropInfo {
                place_count: 2,
                constant_count: 3,
                field_projection_count: 1,
                ..Default::default()
            }),
            chc_coerce_eq_drops: None,
            assume_dropped_transitions: None,
            store_dropped_transitions: None,
            constant_zero_fallbacks: None,
            unhandled_calls: None,
            diverging_call_drops: None,
            assert_untranslatable: None,
            heap_check_untranslatable: None,
            heap_check_unknown_layout: None,
            type_sort_fallbacks: None,
            signedness_fallbacks: None,
            into_option_drops: None,
            internal_workarounds: None,
            abstracted_fallbacks: None,
            vec_field_fallbacks: None,
            pointee_synthesis_fallbacks: None,
            unsupported_construct_fallbacks: None,
            unconstrained_assignments: None,
            bmc_store_coercion_fallbacks: None,
            kani_mem_overapprox: None,
            offset_provenance_unresolved: None,
            sort_harmonize_fresh_var_fallbacks: None,
            error_blocked_fmt: None,
            known_stdlib_unconstrained: None,
            inferable_predicates: None,
            ptr_metadata_unconstrained: None,
            static_init_incomplete: None,
            fp_bitvector_encoding: None,
            aggregate_encoding_gap: None,
            stub_approximation: None,
            rounding_assertion_bypass: None,
        };

        let json = serde_json::to_string(&metadata_with).expect("serialize chc_translation_drops");
        assert!(json.contains("chc_translation_drops"));
        assert!(json.contains("place_count"));
        assert!(json.contains("constant_count"));
        assert!(json.contains("field_projection_count"));

        let deserialized: KaniMetadata =
            serde_json::from_str(&json).expect("deserialize chc_translation_drops");
        let info = deserialized.chc_translation_drops.expect("expected chc_translation_drops");
        assert_eq!(info.place_count, 2);
        assert_eq!(info.constant_count, 3);
        assert_eq!(info.field_projection_count, 1);
    }

    #[test]
    fn test_chc_coerce_eq_drop_info_has_drops() {
        let empty = ChcCoerceEqDropInfo { total_count: 0, per_harness: BTreeMap::new() };
        assert!(!empty.has_drops());

        let mut per_harness = BTreeMap::new();
        per_harness.insert("probe".to_string(), 2);
        let with_count = ChcCoerceEqDropInfo { total_count: 2, per_harness };
        assert!(with_count.has_drops());
    }

    #[test]
    fn test_chc_coerce_eq_drop_serialization() {
        let mut per_harness = BTreeMap::new();
        per_harness.insert("bar::harness".to_string(), 5);
        let metadata_with = KaniMetadata {
            crate_name: "test".to_string(),
            proof_harnesses: vec![],
            unsupported_features: vec![],
            test_harnesses: vec![],
            contracted_functions: vec![],
            autoharness_md: None,
            iterator_unsoundness: None,
            bigint_unsoundness: None,
            chc_fallbacks: None,
            chc_translation_drops: None,
            chc_coerce_eq_drops: Some(ChcCoerceEqDropInfo { total_count: 5, per_harness }),
            assume_dropped_transitions: None,
            store_dropped_transitions: None,
            constant_zero_fallbacks: None,
            unhandled_calls: None,
            diverging_call_drops: None,
            assert_untranslatable: None,
            heap_check_untranslatable: None,
            heap_check_unknown_layout: None,
            type_sort_fallbacks: None,
            signedness_fallbacks: None,
            into_option_drops: None,
            internal_workarounds: None,
            abstracted_fallbacks: None,
            vec_field_fallbacks: None,
            pointee_synthesis_fallbacks: None,
            unsupported_construct_fallbacks: None,
            unconstrained_assignments: None,
            bmc_store_coercion_fallbacks: None,
            kani_mem_overapprox: None,
            offset_provenance_unresolved: None,
            sort_harmonize_fresh_var_fallbacks: None,
            error_blocked_fmt: None,
            known_stdlib_unconstrained: None,
            inferable_predicates: None,
            ptr_metadata_unconstrained: None,
            static_init_incomplete: None,
            fp_bitvector_encoding: None,
            aggregate_encoding_gap: None,
            stub_approximation: None,
            rounding_assertion_bypass: None,
        };

        let json = serde_json::to_string(&metadata_with).expect("serialize coerce_eq metadata");
        assert!(json.contains("chc_coerce_eq_drops"));
        assert!(json.contains("bar::harness"));
        assert!(json.contains("total_count"));

        let deserialized: KaniMetadata =
            serde_json::from_str(&json).expect("deserialize coerce_eq round-trip");
        let info = deserialized.chc_coerce_eq_drops.expect("expected chc_coerce_eq_drops");
        assert_eq!(info.total_count, 5);
        assert_eq!(info.per_harness.get("bar::harness").copied(), Some(5));
    }

    #[test]
    fn test_chc_coerce_eq_drop_deserialization_missing_field() {
        // Old metadata without chc_coerce_eq_drops field should deserialize with None
        let json = r#"{
            "crate_name": "test",
            "proof_harnesses": [],
            "unsupported_features": [],
            "test_harnesses": [],
            "contracted_functions": [],
            "autoharness_md": null,
            "chc_fallbacks": {"total_count": 1, "per_harness": {"fn1": 1}}
        }"#;
        let metadata: KaniMetadata =
            serde_json::from_str(json).expect("deserialize coerce_eq missing field");
        assert!(metadata.chc_coerce_eq_drops.is_none());
        assert!(metadata.chc_fallbacks.is_some());
        assert!(metadata.constant_zero_fallbacks.is_none());
    }

    #[test]
    fn test_assume_dropped_transition_info_has_drops() {
        let zero = AssumeDroppedTransitionInfo { count: 0, ..Default::default() };
        assert!(!zero.has_drops());

        let with_count = AssumeDroppedTransitionInfo { count: 2, ..Default::default() };
        assert!(with_count.has_drops());
    }

    #[test]
    fn test_assume_dropped_transition_serialization() {
        let metadata_with = KaniMetadata {
            crate_name: "test".to_string(),
            proof_harnesses: vec![],
            unsupported_features: vec![],
            test_harnesses: vec![],
            contracted_functions: vec![],
            autoharness_md: None,
            iterator_unsoundness: None,
            bigint_unsoundness: None,
            chc_fallbacks: None,
            chc_translation_drops: None,
            chc_coerce_eq_drops: None,
            assume_dropped_transitions: Some(AssumeDroppedTransitionInfo {
                count: 3,
                ..Default::default()
            }),
            store_dropped_transitions: None,
            constant_zero_fallbacks: None,
            unhandled_calls: None,
            diverging_call_drops: None,
            assert_untranslatable: None,
            heap_check_untranslatable: None,
            heap_check_unknown_layout: None,
            type_sort_fallbacks: None,
            signedness_fallbacks: None,
            into_option_drops: None,
            internal_workarounds: None,
            abstracted_fallbacks: None,
            vec_field_fallbacks: None,
            pointee_synthesis_fallbacks: None,
            unsupported_construct_fallbacks: None,
            unconstrained_assignments: None,
            bmc_store_coercion_fallbacks: None,
            kani_mem_overapprox: None,
            offset_provenance_unresolved: None,
            sort_harmonize_fresh_var_fallbacks: None,
            error_blocked_fmt: None,
            known_stdlib_unconstrained: None,
            inferable_predicates: None,
            ptr_metadata_unconstrained: None,
            static_init_incomplete: None,
            fp_bitvector_encoding: None,
            aggregate_encoding_gap: None,
            stub_approximation: None,
            rounding_assertion_bypass: None,
        };

        let json =
            serde_json::to_string(&metadata_with).expect("serialize assume_dropped metadata");
        assert!(json.contains("assume_dropped_transitions"));
        assert!(json.contains("\"count\":3"));

        let deserialized: KaniMetadata =
            serde_json::from_str(&json).expect("deserialize assume_dropped round-trip");
        let info =
            deserialized.assume_dropped_transitions.expect("expected assume_dropped_transitions");
        assert_eq!(info.count, 3);
    }

    #[test]
    fn test_store_dropped_transition_info_has_drops() {
        let zero = StoreDroppedTransitionInfo { count: 0, per_harness: Default::default() };
        assert!(!zero.has_drops());

        let with_count = StoreDroppedTransitionInfo { count: 4, per_harness: Default::default() };
        assert!(with_count.has_drops());
    }

    #[test]
    fn test_store_dropped_transition_serialization() {
        let metadata_with = KaniMetadata {
            crate_name: "test".to_string(),
            proof_harnesses: vec![],
            unsupported_features: vec![],
            test_harnesses: vec![],
            contracted_functions: vec![],
            autoharness_md: None,
            iterator_unsoundness: None,
            bigint_unsoundness: None,
            chc_fallbacks: None,
            chc_translation_drops: None,
            chc_coerce_eq_drops: None,
            assume_dropped_transitions: None,
            store_dropped_transitions: Some(StoreDroppedTransitionInfo {
                count: 6,
                per_harness: Default::default(),
            }),
            constant_zero_fallbacks: None,
            unhandled_calls: None,
            diverging_call_drops: None,
            assert_untranslatable: None,
            heap_check_untranslatable: None,
            heap_check_unknown_layout: None,
            type_sort_fallbacks: None,
            signedness_fallbacks: None,
            into_option_drops: None,
            internal_workarounds: None,
            abstracted_fallbacks: None,
            vec_field_fallbacks: None,
            pointee_synthesis_fallbacks: None,
            unsupported_construct_fallbacks: None,
            unconstrained_assignments: None,
            bmc_store_coercion_fallbacks: None,
            kani_mem_overapprox: None,
            offset_provenance_unresolved: None,
            sort_harmonize_fresh_var_fallbacks: None,
            error_blocked_fmt: None,
            known_stdlib_unconstrained: None,
            inferable_predicates: None,
            ptr_metadata_unconstrained: None,
            static_init_incomplete: None,
            fp_bitvector_encoding: None,
            aggregate_encoding_gap: None,
            stub_approximation: None,
            rounding_assertion_bypass: None,
        };

        let json = serde_json::to_string(&metadata_with).expect("serialize store_dropped metadata");
        assert!(json.contains("store_dropped_transitions"));
        assert!(json.contains("\"count\":6"));

        let deserialized: KaniMetadata =
            serde_json::from_str(&json).expect("deserialize store_dropped round-trip");
        let info =
            deserialized.store_dropped_transitions.expect("expected store_dropped_transitions");
        assert_eq!(info.count, 6);
    }

    #[test]
    fn test_constant_zero_fallback_info_has_fallbacks() {
        let zero = ConstantZeroFallbackInfo { count: 0, ..Default::default() };
        assert!(!zero.has_fallbacks());

        let with_count = ConstantZeroFallbackInfo { count: 3, ..Default::default() };
        assert!(with_count.has_fallbacks());
    }

    #[test]
    fn test_constant_zero_fallback_serialization() {
        let metadata_with = KaniMetadata {
            crate_name: "test".to_string(),
            proof_harnesses: vec![],
            unsupported_features: vec![],
            test_harnesses: vec![],
            contracted_functions: vec![],
            autoharness_md: None,
            iterator_unsoundness: None,
            bigint_unsoundness: None,
            chc_fallbacks: None,
            chc_translation_drops: None,
            chc_coerce_eq_drops: None,
            assume_dropped_transitions: None,
            store_dropped_transitions: None,
            constant_zero_fallbacks: Some(ConstantZeroFallbackInfo {
                count: 5,
                ..Default::default()
            }),
            unhandled_calls: None,
            diverging_call_drops: None,
            assert_untranslatable: None,
            heap_check_untranslatable: None,
            heap_check_unknown_layout: None,
            type_sort_fallbacks: None,
            signedness_fallbacks: None,
            into_option_drops: None,
            internal_workarounds: None,
            abstracted_fallbacks: None,
            vec_field_fallbacks: None,
            pointee_synthesis_fallbacks: None,
            unsupported_construct_fallbacks: None,
            unconstrained_assignments: None,
            bmc_store_coercion_fallbacks: None,
            kani_mem_overapprox: None,
            offset_provenance_unresolved: None,
            sort_harmonize_fresh_var_fallbacks: None,
            error_blocked_fmt: None,
            known_stdlib_unconstrained: None,
            inferable_predicates: None,
            ptr_metadata_unconstrained: None,
            static_init_incomplete: None,
            fp_bitvector_encoding: None,
            aggregate_encoding_gap: None,
            stub_approximation: None,
            rounding_assertion_bypass: None,
        };

        let json = serde_json::to_string(&metadata_with).expect("serialize constant_zero metadata");
        assert!(json.contains("constant_zero_fallbacks"));
        assert!(json.contains("\"count\":5"));

        let deserialized: KaniMetadata =
            serde_json::from_str(&json).expect("deserialize constant_zero round-trip");
        let info = deserialized.constant_zero_fallbacks.expect("expected constant_zero_fallbacks");
        assert_eq!(info.count, 5);
    }

    #[test]
    fn test_assert_untranslatable_info_has_untranslatable() {
        let zero = AssertUntranslatableInfo { count: 0 };
        assert!(!zero.has_untranslatable());

        let with_count = AssertUntranslatableInfo { count: 2 };
        assert!(with_count.has_untranslatable());
    }

    #[test]
    fn test_heap_check_untranslatable_info_has_untranslatable() {
        let zero = HeapCheckUntranslatableInfo { count: 0 };
        assert!(!zero.has_untranslatable());

        let with_count = HeapCheckUntranslatableInfo { count: 3 };
        assert!(with_count.has_untranslatable());
    }

    #[test]
    fn test_heap_check_unknown_layout_info_has_unknown_layout() {
        let zero = HeapCheckUnknownLayoutInfo { count: 0 };
        assert!(!zero.has_unknown_layout());

        let with_count = HeapCheckUnknownLayoutInfo { count: 4 };
        assert!(with_count.has_unknown_layout());
    }

    #[test]
    fn test_signedness_fallback_info_has_fallbacks() {
        let zero = SignednessFallbackInfo { count: 0, ..Default::default() };
        assert!(!zero.has_fallbacks());

        let with_count = SignednessFallbackInfo { count: 5, ..Default::default() };
        assert!(with_count.has_fallbacks());
    }

    #[test]
    fn test_signedness_fallback_serialization() {
        let metadata_with = KaniMetadata {
            crate_name: "test".to_string(),
            proof_harnesses: vec![],
            unsupported_features: vec![],
            test_harnesses: vec![],
            contracted_functions: vec![],
            autoharness_md: None,
            iterator_unsoundness: None,
            bigint_unsoundness: None,
            chc_fallbacks: None,
            chc_translation_drops: None,
            chc_coerce_eq_drops: None,
            assume_dropped_transitions: None,
            store_dropped_transitions: None,
            constant_zero_fallbacks: None,
            unhandled_calls: None,
            diverging_call_drops: None,
            assert_untranslatable: None,
            heap_check_untranslatable: None,
            heap_check_unknown_layout: None,
            type_sort_fallbacks: None,
            signedness_fallbacks: Some(SignednessFallbackInfo { count: 4, ..Default::default() }),
            into_option_drops: None,
            internal_workarounds: None,
            abstracted_fallbacks: None,
            vec_field_fallbacks: None,
            pointee_synthesis_fallbacks: None,
            unsupported_construct_fallbacks: None,
            unconstrained_assignments: None,
            bmc_store_coercion_fallbacks: None,
            kani_mem_overapprox: None,
            offset_provenance_unresolved: None,
            sort_harmonize_fresh_var_fallbacks: None,
            error_blocked_fmt: None,
            known_stdlib_unconstrained: None,
            inferable_predicates: None,
            ptr_metadata_unconstrained: None,
            static_init_incomplete: None,
            fp_bitvector_encoding: None,
            aggregate_encoding_gap: None,
            stub_approximation: None,
            rounding_assertion_bypass: None,
        };

        let json =
            serde_json::to_string(&metadata_with).expect("serialize signedness_fallback metadata");
        assert!(json.contains("signedness_fallbacks"));
        assert!(json.contains("\"count\":4"));

        let deserialized: KaniMetadata =
            serde_json::from_str(&json).expect("deserialize signedness_fallback round-trip");
        let info = deserialized.signedness_fallbacks.expect("expected signedness_fallbacks");
        assert_eq!(info.count, 4);
    }

    #[test]
    fn test_fail_closed_counter_serialization() {
        let metadata_with = KaniMetadata {
            crate_name: "test".to_string(),
            proof_harnesses: vec![],
            unsupported_features: vec![],
            test_harnesses: vec![],
            contracted_functions: vec![],
            autoharness_md: None,
            iterator_unsoundness: None,
            bigint_unsoundness: None,
            chc_fallbacks: None,
            chc_translation_drops: None,
            chc_coerce_eq_drops: None,
            assume_dropped_transitions: None,
            store_dropped_transitions: None,
            constant_zero_fallbacks: None,
            unhandled_calls: None,
            diverging_call_drops: None,
            assert_untranslatable: Some(AssertUntranslatableInfo { count: 7 }),
            heap_check_untranslatable: Some(HeapCheckUntranslatableInfo { count: 8 }),
            heap_check_unknown_layout: Some(HeapCheckUnknownLayoutInfo { count: 9 }),
            type_sort_fallbacks: None,
            signedness_fallbacks: None,
            into_option_drops: None,
            internal_workarounds: None,
            abstracted_fallbacks: None,
            vec_field_fallbacks: None,
            pointee_synthesis_fallbacks: None,
            unsupported_construct_fallbacks: None,
            unconstrained_assignments: None,
            bmc_store_coercion_fallbacks: None,
            kani_mem_overapprox: None,
            offset_provenance_unresolved: None,
            sort_harmonize_fresh_var_fallbacks: None,
            error_blocked_fmt: None,
            known_stdlib_unconstrained: None,
            inferable_predicates: None,
            ptr_metadata_unconstrained: None,
            static_init_incomplete: None,
            fp_bitvector_encoding: None,
            aggregate_encoding_gap: None,
            stub_approximation: None,
            rounding_assertion_bypass: None,
        };

        let json = serde_json::to_string(&metadata_with).expect("serialize fail-closed counters");
        assert!(json.contains("assert_untranslatable"));
        assert!(json.contains("heap_check_untranslatable"));
        assert!(json.contains("heap_check_unknown_layout"));

        let deserialized: KaniMetadata =
            serde_json::from_str(&json).expect("deserialize fail-closed counters");
        assert_eq!(deserialized.assert_untranslatable.expect("assert_untranslatable").count, 7);
        assert_eq!(
            deserialized.heap_check_untranslatable.expect("heap_check_untranslatable").count,
            8
        );
        assert_eq!(
            deserialized.heap_check_unknown_layout.expect("heap_check_unknown_layout").count,
            9
        );
    }
}
