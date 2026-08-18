// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Per-harness unsoundness counter accumulator (Part of #3080).
//!
//! Extracted from `unsoundness_fields.rs` to keep file sizes under 500 lines.
//!
//! During codegen, `snapshot_counters` captures the current counter values
//! before each harness's `codegen_items()` call. After codegen,
//! `record_harness_deltas` computes the per-harness delta and stores it.
//! `collect_unsoundness_fields` then drains the accumulated per-harness maps
//! into the metadata Info structs.

use std::cell::RefCell;
use std::collections::BTreeMap;

use super::{
    get_abstracted_fallback_count, get_aggregate_encoding_gap_count,
    get_bmc_iterator_unsound_skip_count, get_chc_assume_dropped_transition_count,
    get_chc_bigint_unsound_skip_count, get_chc_iterator_unsound_skip_count,
    get_constant_zero_fallback_count, get_fp_bitvector_encoding_count,
    get_inferable_predicate_count, get_internal_workaround_count, get_into_option_dropped_count,
    get_pointee_synthesis_fallback_count, get_ptr_metadata_unconstrained_count,
    get_rounding_assertion_bypass_count, get_sort_harmonize_fresh_var_count,
    get_static_init_incomplete_count, get_stub_approximation_count,
    get_unconstrained_assignment_count, get_unsupported_construct_fallback_count,
    get_vec_field_fallback_count, store_coercion::get_bmc_store_coercion_fallback_count,
};

/// Snapshot of all crate-level unsoundness counters at a point in time.
///
/// Includes the original 14 categories plus 5 #3447 statement-level counters
/// (ptr_metadata, static_init, fp_bitvector, aggregate_gap, stub_approx).
#[derive(Default)]
pub(in crate::codegen_ay) struct CounterSnapshot {
    pub(in crate::codegen_ay) constant_zero_fallback: usize,
    pub(in crate::codegen_ay) into_option_drop: usize,
    pub(in crate::codegen_ay) internal_workaround: usize,
    pub(in crate::codegen_ay) abstracted_fallback: usize,
    pub(in crate::codegen_ay) assume_dropped_transition: usize,
    pub(in crate::codegen_ay) iterator_unsoundness: usize,
    pub(in crate::codegen_ay) bigint_unsoundness: usize,
    pub(in crate::codegen_ay) vec_field_fallback: usize,
    pub(in crate::codegen_ay) pointee_synthesis_fallback: usize,
    pub(in crate::codegen_ay) unsupported_construct_fallback: usize,
    pub(in crate::codegen_ay) unconstrained_assignment: usize,
    pub(in crate::codegen_ay) bmc_store_coercion_fallback: usize,
    pub(in crate::codegen_ay) sort_harmonize_fresh_var: usize,
    /// Part of #3493: inferable predicate count for per-harness CTREX classification.
    pub(in crate::codegen_ay) inferable_predicate: usize,
    /// Part of #3447: PtrMetadata resolved to unconstrained symbolic.
    pub(in crate::codegen_ay) ptr_metadata_unconstrained: usize,
    /// Part of #3447: static initializer encoding incomplete.
    pub(in crate::codegen_ay) static_init_incomplete: usize,
    /// Part of #3447: float types encoded as bitvectors.
    pub(in crate::codegen_ay) fp_bitvector_encoding: usize,
    /// Part of #3447: aggregate/discriminant encoding gap.
    pub(in crate::codegen_ay) aggregate_encoding_gap: usize,
    /// Part of #3447: stub returned unconstrained symbolic.
    pub(in crate::codegen_ay) stub_approximation: usize,
    /// Part of #3779: float rounding assertion weakened to finiteness tautology.
    pub(in crate::codegen_ay) rounding_assertion_bypass: usize,
}

/// Per-harness accumulated counts for all crate-level categories.
#[derive(Default)]
pub(super) struct PerHarnessAccumulator {
    pub(super) constant_zero_fallback: BTreeMap<String, usize>,
    pub(super) into_option_drop: BTreeMap<String, usize>,
    pub(super) internal_workaround: BTreeMap<String, usize>,
    pub(super) abstracted_fallback: BTreeMap<String, usize>,
    pub(super) assume_dropped_transition: BTreeMap<String, usize>,
    pub(super) iterator_unsoundness: BTreeMap<String, usize>,
    pub(super) bigint_unsoundness: BTreeMap<String, usize>,
    pub(super) vec_field_fallback: BTreeMap<String, usize>,
    pub(super) pointee_synthesis_fallback: BTreeMap<String, usize>,
    pub(super) unsupported_construct_fallback: BTreeMap<String, usize>,
    pub(super) unconstrained_assignment: BTreeMap<String, usize>,
    pub(super) bmc_store_coercion_fallback: BTreeMap<String, usize>,
    pub(super) sort_harmonize_fresh_var: BTreeMap<String, usize>,
    /// Part of #3493: inferable predicate per-harness accumulator.
    pub(super) inferable_predicate: BTreeMap<String, usize>,
    /// Part of #3447: PtrMetadata unconstrained per-harness accumulator.
    pub(super) ptr_metadata_unconstrained: BTreeMap<String, usize>,
    /// Part of #3447: static init incomplete per-harness accumulator.
    pub(super) static_init_incomplete: BTreeMap<String, usize>,
    /// Part of #3447: FP bitvector encoding per-harness accumulator.
    pub(super) fp_bitvector_encoding: BTreeMap<String, usize>,
    /// Part of #3447: aggregate encoding gap per-harness accumulator.
    pub(super) aggregate_encoding_gap: BTreeMap<String, usize>,
    /// Part of #3447: stub approximation per-harness accumulator.
    pub(super) stub_approximation: BTreeMap<String, usize>,
    /// Part of #3779: rounding assertion bypass per-harness accumulator.
    pub(super) rounding_assertion_bypass: BTreeMap<String, usize>,
    /// HARNESS-keyed offset-provenance-unresolved, absorbed from the
    /// per-FUNCTION map at each harness's codegen boundary. See
    /// [`absorb_fn_keyed_for_harness`] for why this exists.
    pub(super) offset_provenance_unresolved: BTreeMap<String, usize>,
    /// HARNESS-keyed kani::mem over-approximation, absorbed the same way.
    pub(super) kani_mem_overapprox: BTreeMap<String, usize>,
}

/// Fold a drained per-FUNCTION map into a HARNESS-keyed entry.
///
/// Why this is needed, and why it is sound:
///
/// `record_offset_provenance_unresolved_for_fn` / `record_kani_mem_overapprox_for_fn`
/// document their intent as "attributes the demotion to the harness whose
/// codegen accumulated it so it cannot leak onto siblings" — but their callers
/// key by FUNCTION name, not harness name. The driver treats `per_harness` as a
/// mixed key space and is deliberately fail-closed: `attributable_to_harness`
/// (trust-mc-driver/src/demotion.rs) charges any key that names no known proof
/// harness against EVERY harness of the crate. So a function-keyed entry leaks
/// to all siblings — exactly the outcome the comment says it wanted to avoid,
/// and it demotes their genuine proofs.
///
/// Attribution here is unambiguous because `codegen_items` is invoked ONCE PER
/// HARNESS (`compiler_interface.rs`, `&[MonoItem::Fn(*harness)]`), each harness
/// gets its own `.smt2`, and those problems are disjoint. Whatever these
/// counters accumulated between one harness's codegen entry and exit was
/// produced by that harness's own reachable code, so folding the drained map
/// under that harness's name is precise — strictly MORE precise than the
/// fail-closed charge-everyone fallback, never less conservative for the
/// harness that actually caused it.
///
/// Note this does NOT relax the driver's fail-closed rule: it removes the
/// unattributable keys that make the rule fire spuriously.
pub(in crate::codegen_ay) fn absorb_fn_keyed_for_harness(
    harness_name: &str,
    offset_provenance_by_fn: &BTreeMap<String, usize>,
    kani_mem_by_fn: &BTreeMap<String, usize>,
) {
    fn fold(
        acc: &mut BTreeMap<String, usize>,
        harness_name: &str,
        by_fn: &BTreeMap<String, usize>,
    ) {
        let total: usize = by_fn.values().copied().sum();
        if total > 0 {
            *acc.entry(harness_name.to_owned()).or_default() += total;
        }
    }
    PER_HARNESS_ACC.with(|acc| {
        let mut acc = acc.borrow_mut();
        fold(&mut acc.offset_provenance_unresolved, harness_name, offset_provenance_by_fn);
        fold(&mut acc.kani_mem_overapprox, harness_name, kani_mem_by_fn);
    });
}

thread_local! {
    static PER_HARNESS_ACC: RefCell<PerHarnessAccumulator> =
        const { RefCell::new(PerHarnessAccumulator {
            constant_zero_fallback: BTreeMap::new(),
            into_option_drop: BTreeMap::new(),
            internal_workaround: BTreeMap::new(),
            abstracted_fallback: BTreeMap::new(),
            assume_dropped_transition: BTreeMap::new(),
            iterator_unsoundness: BTreeMap::new(),
            bigint_unsoundness: BTreeMap::new(),
            vec_field_fallback: BTreeMap::new(),
            pointee_synthesis_fallback: BTreeMap::new(),
            unsupported_construct_fallback: BTreeMap::new(),
            unconstrained_assignment: BTreeMap::new(),
            bmc_store_coercion_fallback: BTreeMap::new(),
            sort_harmonize_fresh_var: BTreeMap::new(),
            inferable_predicate: BTreeMap::new(),
            ptr_metadata_unconstrained: BTreeMap::new(),
            static_init_incomplete: BTreeMap::new(),
            fp_bitvector_encoding: BTreeMap::new(),
            aggregate_encoding_gap: BTreeMap::new(),
            stub_approximation: BTreeMap::new(),
            rounding_assertion_bypass: BTreeMap::new(),
            offset_provenance_unresolved: BTreeMap::new(),
            kani_mem_overapprox: BTreeMap::new(),
        }) };
}

/// Take a non-destructive snapshot of all crate-level unsoundness counters.
pub(in crate::codegen_ay) fn snapshot_counters() -> CounterSnapshot {
    CounterSnapshot {
        constant_zero_fallback: get_constant_zero_fallback_count(),
        into_option_drop: get_into_option_dropped_count(),
        internal_workaround: get_internal_workaround_count(),
        abstracted_fallback: get_abstracted_fallback_count(),
        assume_dropped_transition: get_chc_assume_dropped_transition_count(),
        iterator_unsoundness: get_chc_iterator_unsound_skip_count()
            + get_bmc_iterator_unsound_skip_count(),
        bigint_unsoundness: get_chc_bigint_unsound_skip_count(),
        vec_field_fallback: get_vec_field_fallback_count() as usize,
        pointee_synthesis_fallback: get_pointee_synthesis_fallback_count(),
        unsupported_construct_fallback: get_unsupported_construct_fallback_count(),
        unconstrained_assignment: get_unconstrained_assignment_count(),
        bmc_store_coercion_fallback: get_bmc_store_coercion_fallback_count(),
        sort_harmonize_fresh_var: get_sort_harmonize_fresh_var_count(),
        inferable_predicate: get_inferable_predicate_count(),
        ptr_metadata_unconstrained: get_ptr_metadata_unconstrained_count(),
        static_init_incomplete: get_static_init_incomplete_count(),
        fp_bitvector_encoding: get_fp_bitvector_encoding_count(),
        aggregate_encoding_gap: get_aggregate_encoding_gap_count(),
        stub_approximation: get_stub_approximation_count(),
        rounding_assertion_bypass: get_rounding_assertion_bypass_count(),
    }
}

/// Record per-harness deltas from before/after snapshots into the accumulator.
pub(in crate::codegen_ay) fn record_harness_deltas(
    harness_name: &str,
    before: &CounterSnapshot,
    after: &CounterSnapshot,
) {
    /// Insert non-zero delta into map.
    fn insert_delta(map: &mut BTreeMap<String, usize>, name: &str, before: usize, after: usize) {
        let delta = after.saturating_sub(before);
        if delta > 0 {
            map.insert(name.to_owned(), delta);
        }
    }

    PER_HARNESS_ACC.with(|acc| {
        let mut acc = acc.borrow_mut();
        insert_delta(
            &mut acc.constant_zero_fallback,
            harness_name,
            before.constant_zero_fallback,
            after.constant_zero_fallback,
        );
        insert_delta(
            &mut acc.into_option_drop,
            harness_name,
            before.into_option_drop,
            after.into_option_drop,
        );
        insert_delta(
            &mut acc.internal_workaround,
            harness_name,
            before.internal_workaround,
            after.internal_workaround,
        );
        insert_delta(
            &mut acc.abstracted_fallback,
            harness_name,
            before.abstracted_fallback,
            after.abstracted_fallback,
        );
        insert_delta(
            &mut acc.assume_dropped_transition,
            harness_name,
            before.assume_dropped_transition,
            after.assume_dropped_transition,
        );
        insert_delta(
            &mut acc.iterator_unsoundness,
            harness_name,
            before.iterator_unsoundness,
            after.iterator_unsoundness,
        );
        insert_delta(
            &mut acc.bigint_unsoundness,
            harness_name,
            before.bigint_unsoundness,
            after.bigint_unsoundness,
        );
        insert_delta(
            &mut acc.vec_field_fallback,
            harness_name,
            before.vec_field_fallback,
            after.vec_field_fallback,
        );
        insert_delta(
            &mut acc.pointee_synthesis_fallback,
            harness_name,
            before.pointee_synthesis_fallback,
            after.pointee_synthesis_fallback,
        );
        insert_delta(
            &mut acc.unsupported_construct_fallback,
            harness_name,
            before.unsupported_construct_fallback,
            after.unsupported_construct_fallback,
        );
        insert_delta(
            &mut acc.unconstrained_assignment,
            harness_name,
            before.unconstrained_assignment,
            after.unconstrained_assignment,
        );
        insert_delta(
            &mut acc.bmc_store_coercion_fallback,
            harness_name,
            before.bmc_store_coercion_fallback,
            after.bmc_store_coercion_fallback,
        );
        insert_delta(
            &mut acc.sort_harmonize_fresh_var,
            harness_name,
            before.sort_harmonize_fresh_var,
            after.sort_harmonize_fresh_var,
        );
        insert_delta(
            &mut acc.inferable_predicate,
            harness_name,
            before.inferable_predicate,
            after.inferable_predicate,
        );
        // Part of #3447: statement-level diagnostic counters for CTREX reclassification.
        insert_delta(
            &mut acc.ptr_metadata_unconstrained,
            harness_name,
            before.ptr_metadata_unconstrained,
            after.ptr_metadata_unconstrained,
        );
        insert_delta(
            &mut acc.static_init_incomplete,
            harness_name,
            before.static_init_incomplete,
            after.static_init_incomplete,
        );
        insert_delta(
            &mut acc.fp_bitvector_encoding,
            harness_name,
            before.fp_bitvector_encoding,
            after.fp_bitvector_encoding,
        );
        insert_delta(
            &mut acc.aggregate_encoding_gap,
            harness_name,
            before.aggregate_encoding_gap,
            after.aggregate_encoding_gap,
        );
        insert_delta(
            &mut acc.stub_approximation,
            harness_name,
            before.stub_approximation,
            after.stub_approximation,
        );
        insert_delta(
            &mut acc.rounding_assertion_bypass,
            harness_name,
            before.rounding_assertion_bypass,
            after.rounding_assertion_bypass,
        );
    });
}

/// Reset the per-harness accumulator (called at session start).
pub(in crate::codegen_ay) fn reset_per_harness_accumulator() {
    PER_HARNESS_ACC.with(|acc| {
        *acc.borrow_mut() = PerHarnessAccumulator::default();
    });
}

/// Drain the per-harness accumulator, returning the accumulated maps.
pub(super) fn take_per_harness_accumulator() -> PerHarnessAccumulator {
    PER_HARNESS_ACC.with(|acc| std::mem::take(&mut *acc.borrow_mut()))
}
