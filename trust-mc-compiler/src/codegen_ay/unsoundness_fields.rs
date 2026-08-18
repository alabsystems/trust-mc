// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Unsoundness counter collection for AY codegen metadata.
//! Extracted from `codegen_results.rs` (#2679).

use std::collections::BTreeMap;
use tracing::{debug, warn};
use trust_mc_metadata::{
    AbstractedFallbackInfo, AggregateEncodingGapInfo, AssertUntranslatableInfo,
    AssumeDroppedTransitionInfo, BigIntUnsoundnessInfo, BmcStoreCoercionFallbackInfo,
    ChcCoerceEqDropInfo, ChcFallbackInfo, ChcTranslationDropInfo, ConstantZeroFallbackInfo,
    DivergingCallDropInfo, ErrorBlockedFmtInfo, FpBitvectorEncodingInfo,
    HeapCheckUnknownLayoutInfo, HeapCheckUntranslatableInfo, InferablePredicateInfo,
    InternalWorkaroundInfo, IntoOptionDropInfo, IteratorUnsoundnessInfo, KaniMemOverapproxInfo,
    KnownStdlibUnconstrainedInfo, OffsetProvenanceUnresolvedInfo, PointeeSynthesisFallbackInfo,
    PtrMetadataUnconstrainedInfo, RoundingAssertionBypassInfo, SignednessFallbackInfo,
    SortHarmonizeFreshVarInfo, StaticInitIncompleteInfo, StoreDroppedTransitionInfo,
    StubApproximationInfo, TypeSortFallbackInfo, UnconstrainedAssignmentInfo, UnhandledCallInfo,
    UnsupportedConstructFallbackInfo, VecFieldFallbackInfo,
};

use super::chc::take_inferable_summary_names_by_fn;
use super::store_coercion::take_bmc_store_coercion_fallback_count;
use super::unsoundness_per_harness::take_per_harness_accumulator;
use super::{
    get_bmc_iterator_unsound_skip_count, get_chc_assume_dropped_transition_count,
    get_chc_bigint_unsound_skip_count, get_chc_iterator_unsound_skip_count,
    get_chc_store_dropped_transition_count, take_aggregate_encoding_gap_by_fn,
    take_aggregate_encoding_gap_count, take_chc_coerce_eq_dropped_constraint_count,
    take_chc_coerce_eq_dropped_constraint_counts_by_fn, take_chc_diverging_call_drop_count,
    take_chc_offset_provenance_unresolved_count, take_fp_bitvector_encoding_by_fn,
    take_fp_bitvector_encoding_count, take_inferable_predicate_count,
    take_kani_mem_overapprox_by_fn, take_kani_mem_overapprox_count,
    take_offset_provenance_unresolved_by_fn, take_ptr_metadata_unconstrained_by_fn,
    take_ptr_metadata_unconstrained_count, take_rounding_assertion_bypass_count,
    take_sort_harmonize_fresh_var_count, take_static_init_incomplete_by_fn,
    take_static_init_incomplete_count, take_store_dropped_by_fn, take_stub_approximation_by_fn,
    take_stub_approximation_count,
};

/// Collected unsoundness counter values from codegen (#2679).
/// Captures global unsoundness counters for both live and dead-code metadata paths.
pub(crate) struct UnsoundnessFields {
    pub(crate) iterator_unsoundness: Option<IteratorUnsoundnessInfo>,
    pub(crate) bigint_unsoundness: Option<BigIntUnsoundnessInfo>,
    pub(crate) chc_fallbacks: Option<ChcFallbackInfo>,
    pub(crate) chc_translation_drops: Option<ChcTranslationDropInfo>,
    pub(crate) chc_coerce_eq_drops: Option<ChcCoerceEqDropInfo>,
    pub(crate) assume_dropped_transitions: Option<AssumeDroppedTransitionInfo>,
    pub(crate) store_dropped_transitions: Option<StoreDroppedTransitionInfo>,
    pub(crate) constant_zero_fallbacks: Option<ConstantZeroFallbackInfo>,
    pub(crate) unhandled_calls: Option<UnhandledCallInfo>,
    pub(crate) error_blocked_fmt: Option<ErrorBlockedFmtInfo>,
    pub(crate) known_stdlib_unconstrained: Option<KnownStdlibUnconstrainedInfo>,
    pub(crate) inferable_predicates: Option<InferablePredicateInfo>,
    pub(crate) diverging_call_drops: Option<DivergingCallDropInfo>,
    pub(crate) offset_provenance_unresolved: Option<OffsetProvenanceUnresolvedInfo>,
    pub(crate) assert_untranslatable: Option<AssertUntranslatableInfo>,
    pub(crate) heap_check_untranslatable: Option<HeapCheckUntranslatableInfo>,
    pub(crate) heap_check_unknown_layout: Option<HeapCheckUnknownLayoutInfo>,
    pub(crate) type_sort_fallbacks: Option<TypeSortFallbackInfo>,
    pub(crate) signedness_fallbacks: Option<SignednessFallbackInfo>,
    pub(crate) into_option_drops: Option<IntoOptionDropInfo>,
    pub(crate) internal_workarounds: Option<InternalWorkaroundInfo>,
    pub(crate) abstracted_fallbacks: Option<AbstractedFallbackInfo>,
    pub(crate) vec_field_fallbacks: Option<VecFieldFallbackInfo>,
    pub(crate) pointee_synthesis_fallbacks: Option<PointeeSynthesisFallbackInfo>,
    pub(crate) unsupported_construct_fallbacks: Option<UnsupportedConstructFallbackInfo>,
    pub(crate) unconstrained_assignments: Option<UnconstrainedAssignmentInfo>,
    pub(crate) bmc_store_coercion_fallbacks: Option<BmcStoreCoercionFallbackInfo>,
    pub(crate) kani_mem_overapprox: Option<KaniMemOverapproxInfo>,
    pub(crate) sort_harmonize_fresh_var_fallbacks: Option<SortHarmonizeFreshVarInfo>,
    pub(crate) ptr_metadata_unconstrained: Option<PtrMetadataUnconstrainedInfo>,
    pub(crate) static_init_incomplete: Option<StaticInitIncompleteInfo>,
    pub(crate) fp_bitvector_encoding: Option<FpBitvectorEncodingInfo>,
    pub(crate) aggregate_encoding_gap: Option<AggregateEncodingGapInfo>,
    pub(crate) stub_approximation: Option<StubApproximationInfo>,
    pub(crate) rounding_assertion_bypass: Option<RoundingAssertionBypassInfo>,
}

/// Collect CHC-specific unsoundness counters (coerce-eq, assume, store drops).
fn collect_chc_drop_fields() -> (
    Option<ChcCoerceEqDropInfo>,
    Option<AssumeDroppedTransitionInfo>,
    Option<StoreDroppedTransitionInfo>,
) {
    let coerce_eq_global_count = take_chc_coerce_eq_dropped_constraint_count();
    let coerce_eq_per_harness = take_chc_coerce_eq_dropped_constraint_counts_by_fn();
    let coerce_eq_run_sum = coerce_eq_per_harness.values().copied().sum::<usize>();
    let coerce_eq_total = coerce_eq_run_sum.max(coerce_eq_global_count);
    if coerce_eq_total != coerce_eq_run_sum {
        debug!(
            coerce_eq_global_count,
            coerce_eq_run_sum, "coerce-eq global/per-harness count mismatch; using max"
        );
    }
    let chc_coerce_eq_drops = if coerce_eq_per_harness.is_empty() && coerce_eq_total == 0 {
        None
    } else {
        warn!(
            coerce_eq_drop_count = coerce_eq_total,
            harness_count = coerce_eq_per_harness.len(),
            "CHC dropped call-result equality constraints due to sort mismatch"
        );
        Some(ChcCoerceEqDropInfo {
            total_count: coerce_eq_total,
            per_harness: coerce_eq_per_harness,
        })
    };

    let assume_drop_count = get_chc_assume_dropped_transition_count();
    let assume_dropped = if assume_drop_count > 0 {
        warn!(
            assume_drop_count,
            "CHC dropped kani::assume semantics (unconstrained fallback or missing target relation)"
        );
        Some(AssumeDroppedTransitionInfo { count: assume_drop_count, ..Default::default() })
    } else {
        None
    };

    let store_drop_count = get_chc_store_dropped_transition_count();
    let store_drop_per_harness = take_store_dropped_by_fn();
    let store_dropped = if store_drop_count > 0 || !store_drop_per_harness.is_empty() {
        let effective_count =
            store_drop_count.max(store_drop_per_harness.values().copied().sum::<usize>());
        warn!(
            effective_count,
            harness_count = store_drop_per_harness.len(),
            "CHC dropped store transitions due to untranslatable projections"
        );
        Some(StoreDroppedTransitionInfo {
            count: effective_count,
            per_harness: store_drop_per_harness,
        })
    } else {
        None
    };

    (chc_coerce_eq_drops, assume_dropped, store_dropped)
}

// Fallback, fail-closed, and statement-level collector functions moved to
// unsoundness_fields_collectors.rs per #4206.
use super::unsoundness_fields_collectors::{
    collect_fail_closed_fields, collect_fallback_fields, collect_statement_counter_fields,
};

/// Merge per-harness data into an Info struct's per_harness field.
///
/// KEY-SPACE CONTRACT (task #65): several Info structs below SEED
/// `per_harness` with a per-FUNCTION-keyed map (`take_*_by_fn`) and this
/// merge REPLACES it with the harness-keyed accumulator only when the
/// accumulator is non-empty. On the harness codegen path every increment
/// happens inside a snapshot window, so the replacement is the precise,
/// harness-keyed attribution. On paths without snapshot windows (e.g. the
/// codegen_results writer) the fn-keyed seed SURVIVES into metadata. The
/// driver therefore treats `per_harness` as a MIXED key space and
/// fail-closes on keys that name no known proof harness (see
/// trust-mc-driver demotion.rs `attributable_to_harness`); a fn-keyed
/// survivor counts against every harness of the crate instead of silently
/// resolving to 0 (the pre-#65 fail-open).
fn merge_ph(info: &mut Option<impl HasPerHarness>, ph: BTreeMap<String, usize>) {
    if ph.is_empty() {
        return;
    }
    if let Some(info) = info {
        info.set_per_harness(ph);
    }
}

trait HasPerHarness {
    fn set_per_harness(&mut self, ph: BTreeMap<String, usize>);
}

macro_rules! impl_has_per_harness {
    ($($ty:ty),+ $(,)?) => {
        $(
            impl HasPerHarness for $ty {
                fn set_per_harness(&mut self, ph: BTreeMap<String, usize>) {
                    self.per_harness = ph;
                }
            }
        )+
    };
}

impl_has_per_harness!(
    ConstantZeroFallbackInfo,
    IntoOptionDropInfo,
    InternalWorkaroundInfo,
    AbstractedFallbackInfo,
    AssumeDroppedTransitionInfo,
    IteratorUnsoundnessInfo,
    BigIntUnsoundnessInfo,
    VecFieldFallbackInfo,
    PointeeSynthesisFallbackInfo,
    UnsupportedConstructFallbackInfo,
    UnconstrainedAssignmentInfo,
    BmcStoreCoercionFallbackInfo,
    SortHarmonizeFreshVarInfo,
    InferablePredicateInfo,
    PtrMetadataUnconstrainedInfo,
    StaticInitIncompleteInfo,
    FpBitvectorEncodingInfo,
    AggregateEncodingGapInfo,
    StubApproximationInfo,
    RoundingAssertionBypassInfo,
);

/// Collect per-harness-aware iterator and BigInt unsoundness fields (Part of #3080).
fn collect_per_harness_aware_fields(
    ph: &mut super::unsoundness_per_harness::PerHarnessAccumulator,
) -> (Option<IteratorUnsoundnessInfo>, Option<BigIntUnsoundnessInfo>) {
    let chc_skip = get_chc_iterator_unsound_skip_count();
    let bmc_skip = get_bmc_iterator_unsound_skip_count();
    let iter_ph = std::mem::take(&mut ph.iterator_unsoundness);
    let iterator_unsoundness = if chc_skip > 0 || bmc_skip > 0 || !iter_ph.is_empty() {
        Some(IteratorUnsoundnessInfo {
            chc_skip_count: chc_skip,
            bmc_skip_count: bmc_skip,
            per_harness: iter_ph,
        })
    } else {
        None
    };
    let bigint_ph = std::mem::take(&mut ph.bigint_unsoundness);
    let bigint_unsoundness = if get_chc_bigint_unsound_skip_count() > 0 || !bigint_ph.is_empty() {
        Some(BigIntUnsoundnessInfo {
            chc_skip_count: get_chc_bigint_unsound_skip_count(),
            per_harness: bigint_ph,
        })
    } else {
        None
    };
    (iterator_unsoundness, bigint_unsoundness)
}

/// Read all global unsoundness counters and return the collected metadata fields.
///
/// Counters using `take_*` semantics are consumed (reset to zero) on read.
/// Per-harness accumulator data (Part of #3080) is merged into `per_harness` fields.
pub(crate) fn collect_unsoundness_fields() -> UnsoundnessFields {
    let mut ph = take_per_harness_accumulator();
    let (iterator_unsoundness, bigint_unsoundness) = collect_per_harness_aware_fields(&mut ph);

    let (chc_coerce_eq_drops, mut assume_dropped_transitions, store_dropped_transitions) =
        collect_chc_drop_fields();
    let (
        chc_fallbacks,
        chc_translation_drops,
        unhandled_calls,
        error_blocked_fmt,
        known_stdlib_unconstrained,
        mut constant_zero_fallbacks,
        type_sort_fallbacks,
        signedness_fallbacks,
    ) = collect_fallback_fields();
    let (assert_untranslatable, heap_check_untranslatable, heap_check_unknown_layout) =
        collect_fail_closed_fields();
    let (
        mut into_option_drops,
        mut internal_workarounds,
        mut abstracted_fallbacks,
        mut vec_field_fallbacks,
        mut pointee_synthesis_fallbacks,
        mut unsupported_construct_fallbacks,
        mut unconstrained_assignments,
    ) = collect_statement_counter_fields();

    // Merge per-harness accumulated data into Info structs (Part of #3080).
    merge_ph(&mut constant_zero_fallbacks, ph.constant_zero_fallback);
    merge_ph(&mut into_option_drops, ph.into_option_drop);
    merge_ph(&mut internal_workarounds, ph.internal_workaround);
    merge_ph(&mut abstracted_fallbacks, ph.abstracted_fallback);
    merge_ph(&mut assume_dropped_transitions, ph.assume_dropped_transition);
    merge_ph(&mut vec_field_fallbacks, ph.vec_field_fallback);
    merge_ph(&mut pointee_synthesis_fallbacks, ph.pointee_synthesis_fallback);
    merge_ph(&mut unsupported_construct_fallbacks, ph.unsupported_construct_fallback);
    merge_ph(&mut unconstrained_assignments, ph.unconstrained_assignment);

    // Part of #3064: BMC store coercion fallback counter.
    let bmc_store_coercion_count = take_bmc_store_coercion_fallback_count();
    let mut bmc_store_coercion_fallbacks = (bmc_store_coercion_count > 0).then(|| {
        warn!(bmc_store_coercion_count, "BMC store coercion fresh-symbolic substitution (#3064)");
        BmcStoreCoercionFallbackInfo { count: bmc_store_coercion_count, ..Default::default() }
    });
    merge_ph(&mut bmc_store_coercion_fallbacks, ph.bmc_store_coercion_fallback);

    // Part of #3395: solver-inferable function summary counter.
    let inferable_count = take_inferable_predicate_count();
    let inferable_summary_names = take_inferable_summary_names_by_fn();
    let mut inferable_predicates = (inferable_count > 0 || !inferable_summary_names.is_empty())
        .then(|| {
            debug!(
                inferable_count,
                summary_name_entries = inferable_summary_names.len(),
                "CHC call dispatch: calls encoded with solver-inferable function summaries"
            );
            InferablePredicateInfo {
                count: inferable_count,
                per_harness_summaries: inferable_summary_names,
                ..Default::default()
            }
        });
    // Part of #3493: merge per-harness inferable predicate counts.
    merge_ph(&mut inferable_predicates, ph.inferable_predicate);

    let diverging_call_drop_count = take_chc_diverging_call_drop_count(); // #3164
    let diverging_call_drops = (diverging_call_drop_count > 0).then(|| {
        warn!(
            diverging_call_drop_count,
            "CHC call dispatch: diverging calls dropped without rules"
        );
        DivergingCallDropInfo { count: diverging_call_drop_count, ..Default::default() }
    });

    let offset_provenance_unresolved_count = take_chc_offset_provenance_unresolved_count();
    // marker: offset_isize_overflow_precise. Charge each demotion to the harness
    // that produced it, instead of the crate total (`per_harness.is_empty()`
    // fallback) which would leak an isize-overflowing offset harness's doubt onto
    // its siblings.
    //
    // The map is now HARNESS-keyed: `absorb_fn_keyed_for_harness` folds the
    // per-FUNCTION recorder output onto the owning harness at its codegen
    // boundary. Previously this used the raw per-FUNCTION map, whose keys name
    // no proof harness — and the driver's fail-closed `attributable_to_harness`
    // charges such keys against EVERY harness, which is precisely the sibling
    // leak this comment says it wants to avoid. Any residual fn-keyed entries
    // (a writer path outside a per-harness codegen window) are still merged in,
    // so the fail-closed behaviour is preserved for genuinely unattributable
    // records rather than discarded.
    let mut offset_provenance_unresolved_per_harness =
        std::mem::take(&mut ph.offset_provenance_unresolved);
    for (k, v) in take_offset_provenance_unresolved_by_fn() {
        *offset_provenance_unresolved_per_harness.entry(k).or_default() += v;
    }
    let offset_provenance_unresolved = (offset_provenance_unresolved_count > 0
        || !offset_provenance_unresolved_per_harness.is_empty())
    .then(|| {
        warn!(
            offset_provenance_unresolved_count,
            per_harness_entries = offset_provenance_unresolved_per_harness.len(),
            "CHC pointer offset/deref: alloc-bound check skipped on unresolved provenance"
        );
        OffsetProvenanceUnresolvedInfo {
            count: offset_provenance_unresolved_count,
            per_harness: offset_provenance_unresolved_per_harness,
        }
    });

    // Part of #3165: kani::mem over-approximation counter with per-harness granularity.
    let kani_mem_count = take_kani_mem_overapprox_count();
    // HARNESS-keyed (see the offset-provenance note above): folded onto the
    // owning harness by `absorb_fn_keyed_for_harness`, with any residual
    // fn-keyed entries merged in so the driver's fail-closed attribution still
    // covers genuinely unattributable records.
    let mut kani_mem_per_harness = std::mem::take(&mut ph.kani_mem_overapprox);
    for (k, v) in take_kani_mem_overapprox_by_fn() {
        *kani_mem_per_harness.entry(k).or_default() += v;
    }
    let kani_mem_overapprox = (kani_mem_count > 0).then(|| {
        debug!(
            kani_mem_count,
            per_harness_entries = kani_mem_per_harness.len(),
            "kani::mem predicates over-approximated as true (sound but no memory safety assurance)"
        );
        KaniMemOverapproxInfo { count: kani_mem_count, per_harness: kani_mem_per_harness }
    });

    // Part of #3263: sort harmonize fresh-variable fallback counter.
    let sort_harmonize_count = take_sort_harmonize_fresh_var_count();
    let mut sort_harmonize_fresh_var_fallbacks = (sort_harmonize_count > 0).then(|| {
        debug!(
            sort_harmonize_count,
            "Sort harmonization created fresh unconstrained symbolics at phi merge points (#3263)"
        );
        SortHarmonizeFreshVarInfo { count: sort_harmonize_count, ..Default::default() }
    });
    merge_ph(&mut sort_harmonize_fresh_var_fallbacks, ph.sort_harmonize_fresh_var);

    // Part of #3447: PtrMetadata unconstrained, static init incomplete, FP-as-BV counters.
    // Per-function maps provide function-level attribution; per-harness accumulator
    // provides harness-level attribution needed for CTREX classification.
    let ptr_meta_count = take_ptr_metadata_unconstrained_count();
    let ptr_meta_per_fn = take_ptr_metadata_unconstrained_by_fn();
    let mut ptr_metadata_unconstrained =
        (ptr_meta_count > 0 || !ptr_meta_per_fn.is_empty()).then(|| {
            debug!(
                ptr_meta_count,
                per_fn_entries = ptr_meta_per_fn.len(),
                "PtrMetadata resolved to unconstrained symbolic (sound over-approximation)"
            );
            PtrMetadataUnconstrainedInfo { count: ptr_meta_count, per_harness: ptr_meta_per_fn }
        });
    merge_ph(&mut ptr_metadata_unconstrained, ph.ptr_metadata_unconstrained);

    let static_init_count = take_static_init_incomplete_count();
    let static_init_per_fn = take_static_init_incomplete_by_fn();
    let mut static_init_incomplete = (static_init_count > 0 || !static_init_per_fn.is_empty())
        .then(|| {
            debug!(
                static_init_count,
                per_fn_entries = static_init_per_fn.len(),
                "Static initializer encoding incomplete (sound over-approximation)"
            );
            StaticInitIncompleteInfo { count: static_init_count, per_harness: static_init_per_fn }
        });
    merge_ph(&mut static_init_incomplete, ph.static_init_incomplete);

    let fp_bv_count = take_fp_bitvector_encoding_count();
    let fp_bv_per_fn = take_fp_bitvector_encoding_by_fn();
    let mut fp_bitvector_encoding = (fp_bv_count > 0 || !fp_bv_per_fn.is_empty()).then(|| {
        debug!(
            fp_bv_count,
            per_fn_entries = fp_bv_per_fn.len(),
            "Float types encoded as bitvectors instead of FP sorts (sound over-approximation)"
        );
        FpBitvectorEncodingInfo { count: fp_bv_count, per_harness: fp_bv_per_fn }
    });
    merge_ph(&mut fp_bitvector_encoding, ph.fp_bitvector_encoding);

    let agg_gap_count = take_aggregate_encoding_gap_count();
    let agg_gap_per_fn = take_aggregate_encoding_gap_by_fn();
    let mut aggregate_encoding_gap = (agg_gap_count > 0 || !agg_gap_per_fn.is_empty()).then(|| {
        debug!(
            agg_gap_count,
            per_fn_entries = agg_gap_per_fn.len(),
            "Aggregate/discriminant encoding gap (sound over-approximation)"
        );
        AggregateEncodingGapInfo { count: agg_gap_count, per_harness: agg_gap_per_fn }
    });
    merge_ph(&mut aggregate_encoding_gap, ph.aggregate_encoding_gap);

    let stub_approx_count = take_stub_approximation_count();
    let stub_approx_per_fn = take_stub_approximation_by_fn();
    let mut stub_approximation =
        (stub_approx_count > 0 || !stub_approx_per_fn.is_empty()).then(|| {
            debug!(
                stub_approx_count,
                per_fn_entries = stub_approx_per_fn.len(),
                "Stub returned unconstrained symbolic (sound over-approximation)"
            );
            StubApproximationInfo { count: stub_approx_count, per_harness: stub_approx_per_fn }
        });
    merge_ph(&mut stub_approximation, ph.stub_approximation);

    // Part of #3779: rounding assertion bypass counter.
    let rounding_bypass_count = take_rounding_assertion_bypass_count();
    let mut rounding_assertion_bypass = (rounding_bypass_count > 0).then(|| {
        debug!(
            rounding_bypass_count,
            "Float rounding assertions weakened to finiteness tautology (sound over-approximation)"
        );
        RoundingAssertionBypassInfo { count: rounding_bypass_count, ..Default::default() }
    });
    merge_ph(&mut rounding_assertion_bypass, ph.rounding_assertion_bypass);

    UnsoundnessFields {
        iterator_unsoundness,
        bigint_unsoundness,
        chc_fallbacks,
        chc_translation_drops,
        chc_coerce_eq_drops,
        assume_dropped_transitions,
        store_dropped_transitions,
        constant_zero_fallbacks,
        unhandled_calls,
        error_blocked_fmt,
        known_stdlib_unconstrained,
        inferable_predicates,
        diverging_call_drops,
        offset_provenance_unresolved,
        assert_untranslatable,
        heap_check_untranslatable,
        heap_check_unknown_layout,
        type_sort_fallbacks,
        signedness_fallbacks,
        into_option_drops,
        internal_workarounds,
        abstracted_fallbacks,
        vec_field_fallbacks,
        pointee_synthesis_fallbacks,
        unsupported_construct_fallbacks,
        unconstrained_assignments,
        bmc_store_coercion_fallbacks,
        kani_mem_overapprox,
        sort_harmonize_fresh_var_fallbacks,
        ptr_metadata_unconstrained,
        static_init_incomplete,
        fp_bitvector_encoding,
        aggregate_encoding_gap,
        stub_approximation,
        rounding_assertion_bypass,
    }
}
