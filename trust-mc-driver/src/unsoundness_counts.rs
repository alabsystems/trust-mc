// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Unsoundness counting and classification types for verification result demotion.
//!
//! Extracts unsoundness metadata from project compilation artifacts and provides
//! per-crate and per-harness unsoundness counts used by [`crate::demotion`] to
//! gate PROOF verdicts.
//!
//! Extraction functions are in [`crate::unsoundness_extract`].
//! Shared test helpers are in [`crate::test_support`] (cfg(test) only).

use std::collections::{BTreeMap, BTreeSet};

use trust_mc_metadata::{KaniMetadata, UnsoundnessCategory};

use crate::project::Project;
use crate::unsoundness_extract;
use crate::unsoundness_extract_fail_closed;

/// Unsoundness categories that demote PROOF to FAILURE when nonzero (#2973, #3715).
///
/// Enum-backed: adding a new `UnsoundnessCategory` variant with `class() == Demoted`
/// requires adding it here. The compile-time assertion below enforces coverage.
pub(crate) const DEMOTED_CATEGORIES: [UnsoundnessCategory; 17] = [
    UnsoundnessCategory::ConstantZeroFallback,
    UnsoundnessCategory::InternalWorkaround,
    UnsoundnessCategory::ChcFallback,
    UnsoundnessCategory::TypeSortFallback,
    UnsoundnessCategory::SignednessFallback,
    UnsoundnessCategory::UnsupportedConstructFallback,
    UnsoundnessCategory::UnconstrainedAssignment,
    UnsoundnessCategory::BmcStoreCoercionFallback,
    UnsoundnessCategory::StoreDroppedTransition,
    UnsoundnessCategory::DivergingCallDrop,
    UnsoundnessCategory::KaniMemOverapprox,
    UnsoundnessCategory::OffsetProvenanceUnresolved,
    UnsoundnessCategory::InferablePredicate,
    UnsoundnessCategory::FpBitvectorEncoding,
    UnsoundnessCategory::RoundingAssertionBypass,
    // Reclassified from SoundApproximation (#unsound-symbolic-sub): these mint a
    // fresh solver-controlled symbolic for a program-produced value, which can
    // mask a real violation (false PROVED). Their own diagnostics docs say so.
    UnsoundnessCategory::VecFieldFallback,
    UnsoundnessCategory::PointeeSynthesisFallback,
];

/// Unsoundness categories handled conservatively at codegen time (#2973, #3715).
///
/// These produce error rules or inject `false` constraints that force the
/// solver to report failure, so no demotion is needed.
pub(crate) const FAIL_CLOSED_CATEGORIES: [UnsoundnessCategory; 5] = [
    UnsoundnessCategory::AssertUntranslatable,
    UnsoundnessCategory::HeapCheckUntranslatable,
    UnsoundnessCategory::HeapCheckUnknownLayout,
    UnsoundnessCategory::IteratorUnsoundness,
    UnsoundnessCategory::BigIntUnsoundness,
];

/// Unsoundness categories that use sound over-approximation (#3099, #3715).
///
/// These create fresh unconstrained symbolic values or drop constraints,
/// making the encoding strictly STRONGER (universally quantified).
/// A PROOF under this model is always valid. Tracked for diagnostics but not demotion.
pub(crate) const SOUND_APPROXIMATION_CATEGORIES: [UnsoundnessCategory; 12] = [
    UnsoundnessCategory::AssumeDroppedTransition,
    UnsoundnessCategory::ChcCoerceEqDrop,
    UnsoundnessCategory::ChcTranslationDrop,
    // Recognized-clean subset of translation drops (certified fresh havoc).
    // Kept as a SoundApproximation category so a spurious counterexample is
    // still tagged OverApproximation (Unknown), but the driver excludes it from
    // the sound-fallback proof qualifier so an all-SoundHavoc proof is clean.
    UnsoundnessCategory::ChcSoundHavocDrop,
    UnsoundnessCategory::IntoOptionDrop,
    UnsoundnessCategory::AbstractedFallback,
    UnsoundnessCategory::UnhandledCalls,
    UnsoundnessCategory::SortHarmonizeFreshVar,
    UnsoundnessCategory::PtrMetadataUnconstrained,
    UnsoundnessCategory::StaticInitIncomplete,
    UnsoundnessCategory::AggregateEncodingGap,
    UnsoundnessCategory::StubApproximation,
];

// Compile-time assertion: all KaniMetadata unsoundness categories accounted for (#2973, #3715).
const _: () = assert!(
    DEMOTED_CATEGORIES.len() + FAIL_CLOSED_CATEGORIES.len() + SOUND_APPROXIMATION_CATEGORIES.len()
        == trust_mc_metadata::UNSOUNDNESS_CATEGORY_COUNT
);

/// Per-crate, per-harness aggregated sound-approximation map type.
/// crate_name -> (harness_name -> [(category_name, count)])
pub(crate) type SoundApproxPerHarnessMap<'a> =
    BTreeMap<&'a str, BTreeMap<String, Vec<(String, usize)>>>;

fn sum_sound_approx_categories(
    sound_approx_per_harness: &BTreeMap<String, Vec<(String, usize)>>,
) -> Vec<(String, usize)> {
    let mut totals: BTreeMap<String, usize> = BTreeMap::new();
    for categories in sound_approx_per_harness.values() {
        for (category, count) in categories {
            *totals.entry(category.clone()).or_default() += count;
        }
    }
    totals.into_iter().collect()
}

fn diagnostic_count_by_crate(
    project: &Project,
    category: UnsoundnessCategory,
) -> BTreeMap<&str, usize> {
    project
        .metadata
        .iter()
        .filter_map(|metadata| {
            let record = metadata.unsoundness(category)?;
            (record.total_count > 0).then_some((metadata.crate_name.as_str(), record.total_count))
        })
        .collect()
}

fn diagnostic_per_harness_by_crate(
    project: &Project,
    category: UnsoundnessCategory,
) -> BTreeMap<&str, &BTreeMap<String, usize>> {
    project
        .metadata
        .iter()
        .filter_map(|metadata| {
            let per_harness = diagnostic_per_harness(metadata, category)?;
            (!per_harness.is_empty()).then_some((metadata.crate_name.as_str(), per_harness))
        })
        .collect()
}

#[allow(clippy::enum_glob_use)]
fn diagnostic_per_harness(
    metadata: &KaniMetadata,
    category: UnsoundnessCategory,
) -> Option<&BTreeMap<String, usize>> {
    use UnsoundnessCategory::*;
    Some(match category {
        ConstantZeroFallback => &metadata.constant_zero_fallbacks.as_ref()?.per_harness,
        InternalWorkaround => &metadata.internal_workarounds.as_ref()?.per_harness,
        ChcFallback => &metadata.chc_fallbacks.as_ref()?.per_harness,
        TypeSortFallback => &metadata.type_sort_fallbacks.as_ref()?.per_harness,
        SignednessFallback => &metadata.signedness_fallbacks.as_ref()?.per_harness,
        UnsupportedConstructFallback => {
            &metadata.unsupported_construct_fallbacks.as_ref()?.per_harness
        }
        UnconstrainedAssignment => &metadata.unconstrained_assignments.as_ref()?.per_harness,
        BmcStoreCoercionFallback => &metadata.bmc_store_coercion_fallbacks.as_ref()?.per_harness,
        StoreDroppedTransition => &metadata.store_dropped_transitions.as_ref()?.per_harness,
        DivergingCallDrop => &metadata.diverging_call_drops.as_ref()?.per_harness,
        OffsetProvenanceUnresolved => &metadata.offset_provenance_unresolved.as_ref()?.per_harness,
        KaniMemOverapprox => &metadata.kani_mem_overapprox.as_ref()?.per_harness,
        InferablePredicate => &metadata.inferable_predicates.as_ref()?.per_harness,
        FpBitvectorEncoding => &metadata.fp_bitvector_encoding.as_ref()?.per_harness,
        RoundingAssertionBypass => &metadata.rounding_assertion_bypass.as_ref()?.per_harness,
        AssertUntranslatable | HeapCheckUntranslatable | HeapCheckUnknownLayout => return None,
        IteratorUnsoundness => &metadata.iterator_unsoundness.as_ref()?.per_harness,
        BigIntUnsoundness => &metadata.bigint_unsoundness.as_ref()?.per_harness,
        AssumeDroppedTransition => &metadata.assume_dropped_transitions.as_ref()?.per_harness,
        ChcCoerceEqDrop => &metadata.chc_coerce_eq_drops.as_ref()?.per_harness,
        ChcTranslationDrop => &metadata.chc_translation_drops.as_ref()?.per_harness,
        ChcSoundHavocDrop => &metadata.chc_translation_drops.as_ref()?.sound_havoc_per_harness,
        IntoOptionDrop => &metadata.into_option_drops.as_ref()?.per_harness,
        AbstractedFallback => &metadata.abstracted_fallbacks.as_ref()?.per_harness,
        VecFieldFallback => &metadata.vec_field_fallbacks.as_ref()?.per_harness,
        PointeeSynthesisFallback => &metadata.pointee_synthesis_fallbacks.as_ref()?.per_harness,
        UnhandledCalls => &metadata.unhandled_calls.as_ref()?.per_harness,
        SortHarmonizeFreshVar => &metadata.sort_harmonize_fresh_var_fallbacks.as_ref()?.per_harness,
        PtrMetadataUnconstrained => &metadata.ptr_metadata_unconstrained.as_ref()?.per_harness,
        StaticInitIncomplete => &metadata.static_init_incomplete.as_ref()?.per_harness,
        AggregateEncodingGap => &metadata.aggregate_encoding_gap.as_ref()?.per_harness,
        StubApproximation => &metadata.stub_approximation.as_ref()?.per_harness,
    })
}

/// Consolidated per-crate unsoundness counts used for result demotion (#2659).
///
/// Replaces the previous pattern of passing individual counts through `check_harness`.
/// Each field is a `BTreeMap<&str, usize>` mapping crate name to count.
pub(crate) struct UnsoundnessCounts<'a> {
    constant_zero_fallback: BTreeMap<&'a str, usize>,
    internal_workaround: BTreeMap<&'a str, usize>,
    chc_fallback: BTreeMap<&'a str, usize>,
    type_sort_fallback: BTreeMap<&'a str, usize>,
    signedness_fallback: BTreeMap<&'a str, usize>,
    unsupported_construct_fallback: BTreeMap<&'a str, usize>,
    unconstrained_assignment: BTreeMap<&'a str, usize>,
    bmc_store_coercion_fallback: BTreeMap<&'a str, usize>,
    store_dropped_transition: BTreeMap<&'a str, usize>,
    diverging_call_drop: BTreeMap<&'a str, usize>,
    offset_provenance_unresolved: BTreeMap<&'a str, usize>,
    kani_mem_overapprox: BTreeMap<&'a str, usize>,
    inferable_predicate: BTreeMap<&'a str, usize>,
    fp_bitvector_encoding: BTreeMap<&'a str, usize>,
    rounding_assertion_bypass: BTreeMap<&'a str, usize>,
    /// Per-harness CHC fallback counts by crate (#2959).
    chc_fallback_per_harness: BTreeMap<&'a str, &'a BTreeMap<String, usize>>,
    /// Per-harness signedness fallback counts by crate (#2959 Phase 2).
    signedness_fallback_per_harness: BTreeMap<&'a str, &'a BTreeMap<String, usize>>,
    /// Per-harness type-sort fallback counts by crate (#2959 Phase 2).
    type_sort_fallback_per_harness: BTreeMap<&'a str, &'a BTreeMap<String, usize>>,
    constant_zero_per_harness: BTreeMap<&'a str, &'a BTreeMap<String, usize>>,
    internal_workaround_per_harness: BTreeMap<&'a str, &'a BTreeMap<String, usize>>,
    unsupported_construct_per_harness: BTreeMap<&'a str, &'a BTreeMap<String, usize>>,
    unconstrained_assignment_per_harness: BTreeMap<&'a str, &'a BTreeMap<String, usize>>,
    bmc_store_coercion_per_harness: BTreeMap<&'a str, &'a BTreeMap<String, usize>>,
    store_dropped_transition_per_harness: BTreeMap<&'a str, &'a BTreeMap<String, usize>>,
    diverging_call_drop_per_harness: BTreeMap<&'a str, &'a BTreeMap<String, usize>>,
    offset_provenance_unresolved_per_harness: BTreeMap<&'a str, &'a BTreeMap<String, usize>>,
    kani_mem_overapprox_per_harness: BTreeMap<&'a str, &'a BTreeMap<String, usize>>,
    inferable_predicate_per_harness: BTreeMap<&'a str, &'a BTreeMap<String, usize>>,
    fp_bitvector_encoding_per_harness: BTreeMap<&'a str, &'a BTreeMap<String, usize>>,
    rounding_assertion_bypass_per_harness: BTreeMap<&'a str, &'a BTreeMap<String, usize>>,
    /// Reclassified-to-demoting (unsound symbolic substitution): demote PROOF.
    vec_field_fallback: BTreeMap<&'a str, usize>,
    pointee_synthesis_fallback: BTreeMap<&'a str, usize>,
    vec_field_fallback_per_harness: BTreeMap<&'a str, &'a BTreeMap<String, usize>>,
    pointee_synthesis_fallback_per_harness: BTreeMap<&'a str, &'a BTreeMap<String, usize>>,
    /// Aggregated per-harness sound-approximation counts across all SOUND_APPROXIMATION
    /// categories (#3303). Used for CTREX OverApproximation classification.
    sound_approx_per_harness: SoundApproxPerHarnessMap<'a>,
    /// Fail-closed counters (Part of #3447): injected failure for untranslatable constructs.
    assert_untranslatable: BTreeMap<&'a str, usize>,
    heap_check_untranslatable: BTreeMap<&'a str, usize>,
    heap_check_unknown_layout: BTreeMap<&'a str, usize>,
    iterator_unsoundness: BTreeMap<&'a str, usize>,
    bigint_unsoundness: BTreeMap<&'a str, usize>,
    iterator_unsoundness_per_harness: BTreeMap<&'a str, &'a BTreeMap<String, usize>>,
    bigint_unsoundness_per_harness: BTreeMap<&'a str, &'a BTreeMap<String, usize>>,
    /// Proof-harness pretty names per crate. Used by `classify_ctrex` to
    /// distinguish sound-approximation counts attributed to a DIFFERENT
    /// harness (which cannot taint this harness's counterexample) from
    /// residual counts attributed to non-harness functions (which stay
    /// fail-closed and demote every harness in the crate).
    harness_names_by_crate: BTreeMap<&'a str, BTreeSet<String>>,
}

impl<'a> UnsoundnessCounts<'a> {
    pub(crate) fn from_project(project: &'a Project) -> Self {
        use UnsoundnessCategory as UC;

        let dc = diagnostic_count_by_crate;
        let dph = diagnostic_per_harness_by_crate;

        Self {
            constant_zero_fallback: unsoundness_extract::constant_zero_fallback_count_by_crate(
                project,
            ),
            internal_workaround: unsoundness_extract::internal_workaround_count_by_crate(project),
            chc_fallback: unsoundness_extract::chc_fallback_count_by_crate(project),
            type_sort_fallback: unsoundness_extract::type_sort_fallback_count_by_crate(project),
            signedness_fallback: unsoundness_extract::signedness_fallback_count_by_crate(project),
            unsupported_construct_fallback:
                unsoundness_extract::unsupported_construct_fallback_count_by_crate(project),
            unconstrained_assignment: unsoundness_extract::unconstrained_assignment_count_by_crate(
                project,
            ),
            bmc_store_coercion_fallback: dc(project, UC::BmcStoreCoercionFallback),
            store_dropped_transition: dc(project, UC::StoreDroppedTransition),
            diverging_call_drop: dc(project, UC::DivergingCallDrop),
            offset_provenance_unresolved: dc(project, UC::OffsetProvenanceUnresolved),
            kani_mem_overapprox: dc(project, UC::KaniMemOverapprox),
            inferable_predicate: dc(project, UC::InferablePredicate),
            fp_bitvector_encoding: dc(project, UC::FpBitvectorEncoding),
            rounding_assertion_bypass: dc(project, UC::RoundingAssertionBypass),
            chc_fallback_per_harness: unsoundness_extract::chc_fallback_per_harness_by_crate(
                project,
            ),
            signedness_fallback_per_harness:
                unsoundness_extract::signedness_fallback_per_harness_by_crate(project),
            type_sort_fallback_per_harness:
                unsoundness_extract::type_sort_fallback_per_harness_by_crate(project),
            constant_zero_per_harness:
                unsoundness_extract::constant_zero_fallback_per_harness_by_crate(project),
            internal_workaround_per_harness:
                unsoundness_extract::internal_workaround_per_harness_by_crate(project),
            unsupported_construct_per_harness:
                unsoundness_extract::unsupported_construct_per_harness_by_crate(project),
            unconstrained_assignment_per_harness:
                unsoundness_extract::unconstrained_assignment_per_harness_by_crate(project),
            bmc_store_coercion_per_harness: dph(project, UC::BmcStoreCoercionFallback),
            store_dropped_transition_per_harness: dph(project, UC::StoreDroppedTransition),
            diverging_call_drop_per_harness: dph(project, UC::DivergingCallDrop),
            offset_provenance_unresolved_per_harness: dph(project, UC::OffsetProvenanceUnresolved),
            kani_mem_overapprox_per_harness:
                unsoundness_extract::kani_mem_overapprox_per_harness_by_crate(project),
            inferable_predicate_per_harness: dph(project, UC::InferablePredicate),
            fp_bitvector_encoding_per_harness: dph(project, UC::FpBitvectorEncoding),
            rounding_assertion_bypass_per_harness: dph(project, UC::RoundingAssertionBypass),
            vec_field_fallback: dc(project, UC::VecFieldFallback),
            pointee_synthesis_fallback: dc(project, UC::PointeeSynthesisFallback),
            vec_field_fallback_per_harness: dph(project, UC::VecFieldFallback),
            pointee_synthesis_fallback_per_harness: dph(project, UC::PointeeSynthesisFallback),
            sound_approx_per_harness: unsoundness_extract::sound_approximation_per_harness_by_crate(
                project,
            ),
            assert_untranslatable:
                unsoundness_extract_fail_closed::assert_untranslatable_count_by_crate(project),
            heap_check_untranslatable:
                unsoundness_extract_fail_closed::heap_check_untranslatable_count_by_crate(project),
            heap_check_unknown_layout:
                unsoundness_extract_fail_closed::heap_check_unknown_layout_count_by_crate(project),
            iterator_unsoundness:
                unsoundness_extract_fail_closed::iterator_unsoundness_count_by_crate(project),
            bigint_unsoundness: unsoundness_extract_fail_closed::bigint_unsoundness_count_by_crate(
                project,
            ),
            iterator_unsoundness_per_harness:
                unsoundness_extract_fail_closed::iterator_unsoundness_per_harness_by_crate(project),
            bigint_unsoundness_per_harness:
                unsoundness_extract_fail_closed::bigint_unsoundness_per_harness_by_crate(project),
            harness_names_by_crate: project
                .metadata
                .iter()
                .map(|metadata| {
                    (
                        metadata.crate_name.as_str(),
                        metadata
                            .proof_harnesses
                            .iter()
                            .map(|harness| harness.pretty_name.clone())
                            .collect(),
                    )
                })
                .collect(),
        }
    }

    pub(crate) fn get_for_crate(&self, crate_name: &str) -> CrateUnsoundnessCounts {
        let c = |map: &BTreeMap<&str, usize>| map.get(crate_name).copied().unwrap_or(0);
        let ph = |map: &BTreeMap<&str, &BTreeMap<String, usize>>| {
            map.get(crate_name).map(|m| (*m).clone()).unwrap_or_default()
        };
        let sound_approx_per_harness =
            self.sound_approx_per_harness.get(crate_name).cloned().unwrap_or_default();
        let sound_approx_crate_totals = sum_sound_approx_categories(&sound_approx_per_harness);
        CrateUnsoundnessCounts {
            constant_zero_fallback: c(&self.constant_zero_fallback),
            internal_workaround: c(&self.internal_workaround),
            chc_fallback: c(&self.chc_fallback),
            type_sort_fallback: c(&self.type_sort_fallback),
            signedness_fallback: c(&self.signedness_fallback),
            unsupported_construct_fallback: c(&self.unsupported_construct_fallback),
            unconstrained_assignment: c(&self.unconstrained_assignment),
            bmc_store_coercion_fallback: c(&self.bmc_store_coercion_fallback),
            store_dropped_transition: c(&self.store_dropped_transition),
            diverging_call_drop: c(&self.diverging_call_drop),
            offset_provenance_unresolved: c(&self.offset_provenance_unresolved),
            kani_mem_overapprox: c(&self.kani_mem_overapprox),
            inferable_predicate: c(&self.inferable_predicate),
            fp_bitvector_encoding: c(&self.fp_bitvector_encoding),
            rounding_assertion_bypass: c(&self.rounding_assertion_bypass),
            chc_fallback_per_harness: ph(&self.chc_fallback_per_harness),
            signedness_fallback_per_harness: ph(&self.signedness_fallback_per_harness),
            type_sort_fallback_per_harness: ph(&self.type_sort_fallback_per_harness),
            constant_zero_per_harness: ph(&self.constant_zero_per_harness),
            internal_workaround_per_harness: ph(&self.internal_workaround_per_harness),
            unsupported_construct_per_harness: ph(&self.unsupported_construct_per_harness),
            unconstrained_assignment_per_harness: ph(&self.unconstrained_assignment_per_harness),
            bmc_store_coercion_per_harness: ph(&self.bmc_store_coercion_per_harness),
            store_dropped_transition_per_harness: ph(&self.store_dropped_transition_per_harness),
            diverging_call_drop_per_harness: ph(&self.diverging_call_drop_per_harness),
            offset_provenance_unresolved_per_harness: ph(
                &self.offset_provenance_unresolved_per_harness
            ),
            kani_mem_overapprox_per_harness: ph(&self.kani_mem_overapprox_per_harness),
            inferable_predicate_per_harness: ph(&self.inferable_predicate_per_harness),
            fp_bitvector_encoding_per_harness: ph(&self.fp_bitvector_encoding_per_harness),
            rounding_assertion_bypass_per_harness: ph(&self.rounding_assertion_bypass_per_harness),
            vec_field_fallback: c(&self.vec_field_fallback),
            pointee_synthesis_fallback: c(&self.pointee_synthesis_fallback),
            vec_field_fallback_per_harness: ph(&self.vec_field_fallback_per_harness),
            pointee_synthesis_fallback_per_harness: ph(&self.pointee_synthesis_fallback_per_harness),
            sound_approx_per_harness,
            sound_approx_crate_totals,
            assert_untranslatable: c(&self.assert_untranslatable),
            heap_check_untranslatable: c(&self.heap_check_untranslatable),
            heap_check_unknown_layout: c(&self.heap_check_unknown_layout),
            iterator_unsoundness: c(&self.iterator_unsoundness),
            bigint_unsoundness: c(&self.bigint_unsoundness),
            iterator_unsoundness_per_harness: ph(&self.iterator_unsoundness_per_harness),
            harness_names: self.harness_names_by_crate.get(crate_name).cloned().unwrap_or_default(),
            bigint_unsoundness_per_harness: ph(&self.bigint_unsoundness_per_harness),
        }
    }
}

/// Per-crate unsoundness counts for a single harness's crate.
#[derive(Default)]
pub(crate) struct CrateUnsoundnessCounts {
    pub(crate) constant_zero_fallback: usize,
    pub(crate) internal_workaround: usize,
    pub(crate) chc_fallback: usize,
    pub(crate) type_sort_fallback: usize,
    pub(crate) signedness_fallback: usize,
    pub(crate) unsupported_construct_fallback: usize,
    pub(crate) unconstrained_assignment: usize,
    pub(crate) bmc_store_coercion_fallback: usize,
    pub(crate) store_dropped_transition: usize,
    pub(crate) diverging_call_drop: usize,
    pub(crate) offset_provenance_unresolved: usize,
    pub(crate) kani_mem_overapprox: usize,
    pub(crate) inferable_predicate: usize,
    pub(crate) fp_bitvector_encoding: usize,
    pub(crate) rounding_assertion_bypass: usize,
    /// Per-harness CHC fallback counts (#2959). When non-empty, per-harness
    /// count is preferred over crate-level `chc_fallback` for demotion decisions.
    pub(crate) chc_fallback_per_harness: BTreeMap<String, usize>,
    /// Per-harness signedness fallback counts (#2959 Phase 2).
    pub(crate) signedness_fallback_per_harness: BTreeMap<String, usize>,
    /// Per-harness type-sort fallback counts (#2959 Phase 2).
    pub(crate) type_sort_fallback_per_harness: BTreeMap<String, usize>,
    pub(crate) constant_zero_per_harness: BTreeMap<String, usize>,
    pub(crate) internal_workaround_per_harness: BTreeMap<String, usize>,
    pub(crate) unsupported_construct_per_harness: BTreeMap<String, usize>,
    pub(crate) unconstrained_assignment_per_harness: BTreeMap<String, usize>,
    pub(crate) bmc_store_coercion_per_harness: BTreeMap<String, usize>,
    pub(crate) store_dropped_transition_per_harness: BTreeMap<String, usize>,
    pub(crate) diverging_call_drop_per_harness: BTreeMap<String, usize>,
    /// Per-harness offset-provenance-unresolved counts (crate-total mirror).
    pub(crate) offset_provenance_unresolved_per_harness: BTreeMap<String, usize>,
    /// Per-harness kani::mem over-approximation counts (Part of #3165).
    pub(crate) kani_mem_overapprox_per_harness: BTreeMap<String, usize>,
    pub(crate) inferable_predicate_per_harness: BTreeMap<String, usize>,
    pub(crate) fp_bitvector_encoding_per_harness: BTreeMap<String, usize>,
    pub(crate) rounding_assertion_bypass_per_harness: BTreeMap<String, usize>,
    /// Reclassified-to-demoting unsound symbolic substitutions (vec field load /
    /// pointee synthesis): a nonzero count demotes PROOF to FAILURE.
    pub(crate) vec_field_fallback: usize,
    pub(crate) pointee_synthesis_fallback: usize,
    pub(crate) vec_field_fallback_per_harness: BTreeMap<String, usize>,
    pub(crate) pointee_synthesis_fallback_per_harness: BTreeMap<String, usize>,
    /// Aggregated per-harness sound-approximation categories (#3303).
    /// harness_name -> [(category_name, count)]
    pub(crate) sound_approx_per_harness: BTreeMap<String, Vec<(String, usize)>>,
    /// Crate-level sound-approximation totals derived from per-harness data (#3447).
    /// Used as fallback when a CTREX harness has no attributable per-harness entry.
    pub(crate) sound_approx_crate_totals: Vec<(String, usize)>,
    /// Fail-closed counters (Part of #3447): deliberately injected failures.
    /// These force CTREX on untranslatable constructs — any CTREX with these
    /// nonzero is an encoding gap, not a genuine bug.
    pub(crate) assert_untranslatable: usize,
    pub(crate) heap_check_untranslatable: usize,
    pub(crate) heap_check_unknown_layout: usize,
    pub(crate) iterator_unsoundness: usize,
    pub(crate) bigint_unsoundness: usize,
    pub(crate) iterator_unsoundness_per_harness: BTreeMap<String, usize>,
    /// Proof-harness pretty names of this crate (see `harness_names_by_crate`).
    pub(crate) harness_names: BTreeSet<String>,
    pub(crate) bigint_unsoundness_per_harness: BTreeMap<String, usize>,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::demotion::demote_for_all_unsoundness;
    use crate::test_support::{
        all_single_category_metadata, chc_translation_drop_count_by_crate, md_with, test_harness,
        test_metadata, test_metadata_all, test_result,
    };
    use crate::verification_result::{FailedProperties, VerificationStatus};
    use trust_mc_metadata::{
        AggregateEncodingGapInfo, BigIntUnsoundnessInfo, BmcStoreCoercionFallbackInfo,
        ChcTranslationDropInfo, DivergingCallDropInfo, FpBitvectorEncodingInfo,
        InferablePredicateInfo, IteratorUnsoundnessInfo, KaniMemOverapproxInfo,
        OffsetProvenanceUnresolvedInfo, RoundingAssertionBypassInfo, StoreDroppedTransitionInfo,
        StubApproximationInfo,
    };

    macro_rules! sparse_case {
        ($metadata_field:ident, $info_ty:ident, $category:expr, $count_field:ident, $per_harness_field:ident) => {{
            let mut project = Project::default();
            project.metadata = vec![md_with(|md| {
                md.crate_name = "crate_sparse".to_string();
                // Task #65: both harnesses must be KNOWN proof harnesses so the
                // dirty entry attributes to crate_sparse::dirty alone; an
                // unknown key would fail closed against the clean harness too.
                md.proof_harnesses = vec![
                    test_harness("crate_sparse::clean", "crate_sparse"),
                    test_harness("crate_sparse::dirty", "crate_sparse"),
                ];
                #[allow(clippy::needless_update)]
                let info = $info_ty {
                    count: 0,
                    per_harness: BTreeMap::from([("crate_sparse::dirty".to_string(), 3)]),
                    ..Default::default()
                };
                md.$metadata_field = Some(info);
            })];

            let per_harness = diagnostic_per_harness_by_crate(&project, $category);
            assert_eq!(per_harness["crate_sparse"].get("crate_sparse::dirty"), Some(&3));

            let crate_counts =
                UnsoundnessCounts::from_project(&project).get_for_crate("crate_sparse");
            assert_eq!(crate_counts.$count_field, 0);
            assert_eq!(crate_counts.$per_harness_field.get("crate_sparse::dirty"), Some(&3));

            let mut clean_result = test_result(VerificationStatus::Success, FailedProperties::None);
            let clean_harness = test_harness("crate_sparse::clean", "crate_sparse");
            demote_for_all_unsoundness(&mut clean_result, &clean_harness, &crate_counts);
            assert_eq!(clean_result.status, VerificationStatus::Success);

            let mut dirty_result = test_result(VerificationStatus::Success, FailedProperties::None);
            let dirty_harness = test_harness("crate_sparse::dirty", "crate_sparse");
            demote_for_all_unsoundness(&mut dirty_result, &dirty_harness, &crate_counts);
            assert_eq!(dirty_result.status, VerificationStatus::Failure);
            assert_eq!(dirty_result.demotion_reasons, vec![format!("{}=3", $category.json_key())]);
        }};
    }

    #[test]
    fn test_unsoundness_counts_get_for_crate_returns_defaults_for_unknown_crate() {
        let mut project = Project::default();
        project.metadata = vec![test_metadata_all(
            "crate_a",
            Some(1),
            Some(2),
            Some(8),
            Some((3, 0)),
            Some(4),
            Some(5),
            Some(7),
            Some(9),
        )];

        let counts = UnsoundnessCounts::from_project(&project);
        let unknown = counts.get_for_crate("nonexistent_crate");

        assert_eq!(unknown.constant_zero_fallback, 0);
        assert_eq!(unknown.internal_workaround, 0);
        assert_eq!(unknown.chc_fallback, 0);
        assert_eq!(unknown.type_sort_fallback, 0);
        assert_eq!(unknown.signedness_fallback, 0);
        assert_eq!(unknown.unsupported_construct_fallback, 0);
        assert_eq!(unknown.unconstrained_assignment, 0);
    }

    #[test]
    fn test_unsoundness_counts_from_project() {
        let mut project = Project::default();
        project.metadata = vec![test_metadata_all(
            "crate_a",
            Some(1),
            Some(2),
            Some(8),
            Some((3, 0)),
            Some(4),
            Some(5),
            Some(7),
            Some(9),
        )];

        let counts = UnsoundnessCounts::from_project(&project);
        let crate_counts = counts.get_for_crate("crate_a");

        assert_eq!(crate_counts.constant_zero_fallback, 1);
        assert_eq!(crate_counts.internal_workaround, 0);
        assert_eq!(crate_counts.chc_fallback, 5);
        assert_eq!(crate_counts.type_sort_fallback, 9);
        assert_eq!(crate_counts.signedness_fallback, 0);
        assert_eq!(crate_counts.unsupported_construct_fallback, 0);
        assert_eq!(crate_counts.unconstrained_assignment, 0);
    }

    #[test]
    fn test_unsoundness_counts_extracts_fail_closed_iterator_and_bigint() {
        let mut project = Project::default();
        project.metadata = vec![md_with(|md| {
            md.crate_name = "crate_fail_closed".to_string();
            md.iterator_unsoundness = Some(IteratorUnsoundnessInfo {
                chc_skip_count: 2,
                bmc_skip_count: 1,
                per_harness: BTreeMap::from([("crate_fail_closed::h".to_string(), 3)]),
            });
            md.bigint_unsoundness = Some(BigIntUnsoundnessInfo {
                chc_skip_count: 4,
                per_harness: BTreeMap::from([("crate_fail_closed::h".to_string(), 4)]),
            });
        })];

        let counts = UnsoundnessCounts::from_project(&project).get_for_crate("crate_fail_closed");

        assert_eq!(counts.iterator_unsoundness, 3);
        assert_eq!(counts.bigint_unsoundness, 4);
        assert_eq!(counts.iterator_unsoundness_per_harness.get("crate_fail_closed::h"), Some(&3));
        assert_eq!(counts.bigint_unsoundness_per_harness.get("crate_fail_closed::h"), Some(&4));
    }

    #[test]
    fn test_unsoundness_counts_get_for_crate_aggregates_sound_approx_totals() {
        let mut project = Project::default();
        project.metadata = vec![md_with(|md| {
            md.crate_name = "crate_sound".to_string();
            md.aggregate_encoding_gap = Some(AggregateEncodingGapInfo {
                count: 7,
                per_harness: BTreeMap::from([
                    ("crate_sound::a".to_string(), 2),
                    ("crate_sound::b".to_string(), 5),
                ]),
                per_harness_reasons: BTreeMap::new(),
            });
            md.stub_approximation = Some(StubApproximationInfo {
                count: 3,
                per_harness: BTreeMap::from([
                    ("crate_sound::a".to_string(), 1),
                    ("crate_sound::c".to_string(), 2),
                ]),
            });
        })];

        let counts = UnsoundnessCounts::from_project(&project).get_for_crate("crate_sound");

        assert_eq!(
            counts.sound_approx_crate_totals,
            vec![("aggregate_encoding_gap".to_string(), 7), ("stub_approximation".to_string(), 3),]
        );
    }

    #[test]
    fn test_new_hard_gated_categories_from_project_metadata_wiring() {
        let mut project = Project::default();
        project.metadata = vec![md_with(|md| {
            md.crate_name = "crate_hard_gate".to_string();
            md.bmc_store_coercion_fallbacks =
                Some(BmcStoreCoercionFallbackInfo { count: 1, ..Default::default() });
            md.store_dropped_transitions =
                Some(StoreDroppedTransitionInfo { count: 2, ..Default::default() });
            md.diverging_call_drops =
                Some(DivergingCallDropInfo { count: 3, ..Default::default() });
            md.kani_mem_overapprox = Some(KaniMemOverapproxInfo { count: 4, ..Default::default() });
            md.inferable_predicates =
                Some(InferablePredicateInfo { count: 5, ..Default::default() });
            md.fp_bitvector_encoding =
                Some(FpBitvectorEncodingInfo { count: 6, ..Default::default() });
            md.rounding_assertion_bypass =
                Some(RoundingAssertionBypassInfo { count: 7, ..Default::default() });
        })];

        let crate_counts =
            UnsoundnessCounts::from_project(&project).get_for_crate("crate_hard_gate");

        assert_eq!(crate_counts.bmc_store_coercion_fallback, 1);
        assert_eq!(crate_counts.store_dropped_transition, 2);
        assert_eq!(crate_counts.diverging_call_drop, 3);
        assert_eq!(crate_counts.kani_mem_overapprox, 4);
        assert_eq!(crate_counts.inferable_predicate, 5);
        assert_eq!(crate_counts.fp_bitvector_encoding, 6);
        assert_eq!(crate_counts.rounding_assertion_bypass, 7);

        let harness = test_harness("crate_hard_gate::h", "crate_hard_gate");
        let mut result = test_result(VerificationStatus::Success, FailedProperties::None);
        demote_for_all_unsoundness(&mut result, &harness, &crate_counts);

        assert_eq!(result.status, VerificationStatus::Failure);
        assert_eq!(
            result.demotion_reasons,
            vec![
                "bmc_store_coercion_fallback=1",
                "store_dropped_transition=2",
                "diverging_call_drop=3",
                "kani_mem_overapprox=4",
                "inferable_predicate=5",
                "fp_bitvector_encoding=6",
                "rounding_assertion_bypass=7",
            ]
        );
    }

    #[test]
    fn test_new_demoted_per_harness_metadata_keeps_nonempty_map_when_total_is_zero() {
        sparse_case!(
            bmc_store_coercion_fallbacks,
            BmcStoreCoercionFallbackInfo,
            UnsoundnessCategory::BmcStoreCoercionFallback,
            bmc_store_coercion_fallback,
            bmc_store_coercion_per_harness
        );
        sparse_case!(
            store_dropped_transitions,
            StoreDroppedTransitionInfo,
            UnsoundnessCategory::StoreDroppedTransition,
            store_dropped_transition,
            store_dropped_transition_per_harness
        );
        sparse_case!(
            diverging_call_drops,
            DivergingCallDropInfo,
            UnsoundnessCategory::DivergingCallDrop,
            diverging_call_drop,
            diverging_call_drop_per_harness
        );
        sparse_case!(
            offset_provenance_unresolved,
            OffsetProvenanceUnresolvedInfo,
            UnsoundnessCategory::OffsetProvenanceUnresolved,
            offset_provenance_unresolved,
            offset_provenance_unresolved_per_harness
        );
        sparse_case!(
            kani_mem_overapprox,
            KaniMemOverapproxInfo,
            UnsoundnessCategory::KaniMemOverapprox,
            kani_mem_overapprox,
            kani_mem_overapprox_per_harness
        );
        sparse_case!(
            inferable_predicates,
            InferablePredicateInfo,
            UnsoundnessCategory::InferablePredicate,
            inferable_predicate,
            inferable_predicate_per_harness
        );
        sparse_case!(
            fp_bitvector_encoding,
            FpBitvectorEncodingInfo,
            UnsoundnessCategory::FpBitvectorEncoding,
            fp_bitvector_encoding,
            fp_bitvector_encoding_per_harness
        );
        sparse_case!(
            rounding_assertion_bypass,
            RoundingAssertionBypassInfo,
            UnsoundnessCategory::RoundingAssertionBypass,
            rounding_assertion_bypass,
            rounding_assertion_bypass_per_harness
        );
    }

    /// Round-trip test: metadata with all unsoundness categories nonzero →
    /// UnsoundnessCounts → CrateUnsoundnessCounts → demotion fires.
    /// Proves #2424 acceptance criterion 1: nonzero counters gate the verdict.
    #[test]
    fn test_metadata_roundtrip_all_categories_demote() {
        use trust_mc_metadata::{IntoOptionDropInfo, VecFieldFallbackInfo};

        let mut project = Project::default();
        let mut md = test_metadata_all(
            "test_crate",
            Some(1),      // constant_zero_fallback
            Some(2),      // assume_dropped_transition
            Some(3),      // store_dropped_transition
            Some((4, 1)), // iterator_unsoundness (chc=4, bmc=1)
            Some(5),      // bigint_unsoundness
            Some(6),      // chc_fallback
            Some(8),      // unhandled_calls
            Some(9),      // type_sort_fallback
        );
        md.into_option_drops = Some(IntoOptionDropInfo { count: 10, ..Default::default() });
        md.vec_field_fallbacks = Some(VecFieldFallbackInfo { count: 11, ..Default::default() });
        md.chc_translation_drops = Some(ChcTranslationDropInfo {
            place_count: 2,
            constant_count: 3,
            field_projection_count: 1,
            ..Default::default()
        });
        project.metadata = vec![md];

        let unsoundness = UnsoundnessCounts::from_project(&project);
        let crate_counts = unsoundness.get_for_crate("test_crate");

        assert_eq!(crate_counts.constant_zero_fallback, 1);
        assert_eq!(crate_counts.internal_workaround, 0);
        assert_eq!(crate_counts.chc_fallback, 6);
        assert_eq!(crate_counts.type_sort_fallback, 9);

        let harness = test_harness("test_crate::harness", "test_crate");
        let mut result = test_result(VerificationStatus::Success, FailedProperties::None);
        demote_for_all_unsoundness(&mut result, &harness, &crate_counts);

        assert_eq!(
            result.status,
            VerificationStatus::Failure,
            "Metadata with nonzero dropped-constraint counters must demote PROOF to FAILURE"
        );
        assert!(matches!(result.failed_properties, FailedProperties::Other));
    }

    #[test]
    fn test_chc_translation_drop_is_sound_approximation_no_demotion() {
        let cases = [
            (
                "place_count",
                ChcTranslationDropInfo {
                    place_count: 1,
                    constant_count: 0,
                    field_projection_count: 0,
                    ..Default::default()
                },
            ),
            (
                "constant_count",
                ChcTranslationDropInfo {
                    place_count: 0,
                    constant_count: 1,
                    field_projection_count: 0,
                    ..Default::default()
                },
            ),
            (
                "field_projection_count",
                ChcTranslationDropInfo {
                    place_count: 0,
                    constant_count: 0,
                    field_projection_count: 1,
                    ..Default::default()
                },
            ),
        ];

        for (field_name, drop_info) in cases {
            let mut project = Project::default();
            let mut md = test_metadata("c", None, None);
            md.chc_translation_drops = Some(drop_info);
            project.metadata = vec![md];

            let counts = chc_translation_drop_count_by_crate(&project);
            assert_eq!(
                counts.get("c"),
                Some(&1),
                "{field_name} must contribute to chc_translation_drop_count_by_crate"
            );

            let crate_counts = UnsoundnessCounts::from_project(&project).get_for_crate("c");
            let harness = test_harness("c::h", "c");
            let mut result = test_result(VerificationStatus::Success, FailedProperties::None);
            demote_for_all_unsoundness(&mut result, &harness, &crate_counts);
            assert_eq!(
                result.status,
                VerificationStatus::Success,
                "chc_translation_drop ({field_name}) is sound over-approximation — must NOT demote (#3099)"
            );
        }
    }

    /// Proves each category independently gates the verdict when it is the
    /// only nonzero counter.
    #[test]
    fn test_each_category_independently_demotes_via_metadata() {
        for (category_name, md) in all_single_category_metadata() {
            let mut project = Project::default();
            project.metadata = vec![md.clone()];
            let crate_counts = UnsoundnessCounts::from_project(&project).get_for_crate("c");
            let harness = test_harness("c::h", "c");
            let mut result = test_result(VerificationStatus::Success, FailedProperties::None);
            demote_for_all_unsoundness(&mut result, &harness, &crate_counts);
            assert_eq!(
                result.status,
                VerificationStatus::Failure,
                "Category '{category_name}' alone must demote Success to Failure"
            );
        }
    }

    /// Verifies that `all_single_category_metadata` covers exactly the
    /// `DEMOTED_CATEGORIES` list (#2973, #3715).
    #[test]
    fn test_demotion_coverage_exhaustive() {
        let test_categories: Vec<&str> =
            all_single_category_metadata().iter().map(|(name, _)| *name).collect();

        let demoted_keys: Vec<&str> = DEMOTED_CATEGORIES.iter().map(|c| c.json_key()).collect();

        for key in &demoted_keys {
            assert!(
                test_categories.contains(key),
                "DEMOTED_CATEGORIES entry '{key}' missing from all_single_category_metadata(). \
                 Add a test entry for this category."
            );
        }

        for cat in &test_categories {
            assert!(
                demoted_keys.contains(cat),
                "all_single_category_metadata() entry '{cat}' not in DEMOTED_CATEGORIES. \
                 Add it to DEMOTED_CATEGORIES or remove the test entry."
            );
        }

        assert_eq!(
            test_categories.len()
                + FAIL_CLOSED_CATEGORIES.len()
                + SOUND_APPROXIMATION_CATEGORIES.len(),
            trust_mc_metadata::UNSOUNDNESS_CATEGORY_COUNT,
            "Unsoundness category count mismatch: {} demoted + {} fail-closed + {} sound-approx != {} total.",
            test_categories.len(),
            FAIL_CLOSED_CATEGORIES.len(),
            SOUND_APPROXIMATION_CATEGORIES.len(),
            trust_mc_metadata::UNSOUNDNESS_CATEGORY_COUNT,
        );
    }
}
