// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Process-global diagnostic counter registry for CHC encoding.
//!
//! Consolidates all process-global AtomicUsize/AtomicU64 diagnostic counters
//! and OnceLock<Mutex<BTreeMap>> maps that were previously scattered across 8+
//! files. Per-context counters mirror into these globals at increment-time.
//! reset_all() drains globals for session reset.
//! Metadata emission (unsoundness_fields.rs) reads Tier 2 via take_*/get_*.
//!
//! Extracted from `diagnostics.rs` — Part of #4206.

use std::collections::BTreeMap;
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};
use std::sync::{Mutex, OnceLock};

/// Consolidated process-global diagnostic counters for CHC and statement codegen.
///
/// All AtomicUsize/AtomicU64 counters that were previously scattered across
/// individual source files are now fields of this single struct. The static
/// `GLOBAL_COUNTERS` instance provides the single source of truth.
pub(in crate::codegen_ay) struct GlobalDiagnosticCounters {
    // === Type translation ===
    pub(in crate::codegen_ay) place_translation_drop: AtomicUsize,
    /// Recognized-clean SoundHavoc drops split out of `place_translation_drop`
    /// so an all-SoundHavoc proof reports clean (Part of #unsound-havoc-split).
    pub(in crate::codegen_ay) sound_havoc_drop: AtomicUsize,
    pub(in crate::codegen_ay) const_translation_drop: AtomicUsize,
    pub(in crate::codegen_ay) unsupported_field_projection: AtomicUsize,

    // === Call dispatch ===
    pub(in crate::codegen_ay) unhandled_call: AtomicUsize,
    pub(in crate::codegen_ay) error_blocked_fmt: AtomicUsize,
    pub(in crate::codegen_ay) known_stdlib_unconstrained: AtomicUsize,
    pub(in crate::codegen_ay) inferable_predicate: AtomicUsize,
    pub(in crate::codegen_ay) diverging_call_drop: AtomicUsize,
    pub(in crate::codegen_ay) offset_provenance_unresolved: AtomicUsize,
    pub(in crate::codegen_ay) coerce_eq_dropped_constraint: AtomicUsize,

    // === Assertion encoding ===
    pub(in crate::codegen_ay) assume_dropped_transition: AtomicUsize,
    pub(in crate::codegen_ay) assert_untranslatable: AtomicUsize,

    // === Heap checks ===
    pub(in crate::codegen_ay) heap_check_untranslatable: AtomicUsize,
    pub(in crate::codegen_ay) heap_check_unknown_layout: AtomicUsize,

    // === Store encoding ===
    pub(in crate::codegen_ay) store_dropped_transition: AtomicUsize,

    // === Stubs ===
    pub(in crate::codegen_ay) iterator_unsound_skip: AtomicUsize,
    pub(in crate::codegen_ay) bigint_unsound_skip: AtomicUsize,

    // === Over-approximation ===
    pub(in crate::codegen_ay) kani_mem_overapprox: AtomicUsize,
    pub(in crate::codegen_ay) ptr_metadata_unconstrained: AtomicUsize,
    pub(in crate::codegen_ay) static_init_incomplete: AtomicUsize,
    pub(in crate::codegen_ay) fp_bitvector_encoding: AtomicUsize,
    pub(in crate::codegen_ay) aggregate_encoding_gap: AtomicUsize,
    pub(in crate::codegen_ay) stub_approximation: AtomicUsize,
    pub(in crate::codegen_ay) recursive_unwind_exhausted: AtomicUsize,

    // === Assertion bypass ===
    pub(in crate::codegen_ay) rounding_assertion_bypass: AtomicUsize,

    // === Type-sort fallback ===
    pub(in crate::codegen_ay) type_sort_fallback: AtomicUsize,

    // === Signedness fallback ===
    // NOTE: signedness_fallback AtomicU64 moved to the shared crate counter
    // (Part of #2997: break shared→chc cycle for crate extraction).

    // === Telemetry ===
    pub(in crate::codegen_ay) range_spec_next_datatype_path: AtomicU64,
    pub(in crate::codegen_ay) range_spec_next_flattened_path: AtomicU64,
    pub(in crate::codegen_ay) range_spec_next_fail_closed_path: AtomicU64,
    pub(in crate::codegen_ay) vec_builder_pattern: AtomicU64,

    // === Per-function maps ===
    pub(in crate::codegen_ay) coerce_eq_dropped_by_fn: OnceLock<Mutex<BTreeMap<String, usize>>>,
    pub(in crate::codegen_ay) chc_fallback_counts: OnceLock<Mutex<BTreeMap<String, usize>>>,
    /// Per-function signedness fallback counts (Part of #2959).
    pub(in crate::codegen_ay) signedness_fallback_by_fn: OnceLock<Mutex<BTreeMap<String, usize>>>,
    /// Per-function type-sort fallback counts (Part of #2959).
    pub(in crate::codegen_ay) type_sort_fallback_by_fn: OnceLock<Mutex<BTreeMap<String, usize>>>,
    /// Per-function store-dropped-transition counts (Part of #2966).
    pub(in crate::codegen_ay) store_dropped_by_fn: OnceLock<Mutex<BTreeMap<String, usize>>>,
    /// Per-function unhandled-call counts (Part of #2966).
    pub(in crate::codegen_ay) unhandled_call_by_fn: OnceLock<Mutex<BTreeMap<String, usize>>>,
    /// Per-function translation-drop combined counts (Part of #2966).
    pub(in crate::codegen_ay) translation_drop_by_fn: OnceLock<Mutex<BTreeMap<String, usize>>>,
    /// Per-function recognized-clean SoundHavoc drop counts
    /// (Part of #unsound-havoc-split). Attributed via the same per-fn delta
    /// mechanism as `translation_drop_by_fn`.
    pub(in crate::codegen_ay) sound_havoc_drop_by_fn: OnceLock<Mutex<BTreeMap<String, usize>>>,
    /// Per-function kani::mem over-approximation counts (Part of #3165).
    pub(in crate::codegen_ay) kani_mem_overapprox_by_fn: OnceLock<Mutex<BTreeMap<String, usize>>>,
    /// Per-function offset-provenance-unresolved counts (marker:
    /// offset_isize_overflow_precise). Attributes the `OffsetProvenanceUnresolved`
    /// fail-closed demotion to the harness whose codegen accumulated it, so a
    /// genuinely-failing offset harness (e.g. an isize-overflowing `ptr.add`)
    /// does not leak its provenance doubt onto a sibling harness whose own
    /// offset site is fully discharged (e.g. a ZST twin) via the crate-global
    /// counter's `per_harness.is_empty()` fallback in the driver.
    pub(in crate::codegen_ay) offset_provenance_unresolved_by_fn:
        OnceLock<Mutex<BTreeMap<String, usize>>>,
    /// Per-function PtrMetadata unconstrained counts (Part of #3447).
    pub(in crate::codegen_ay) ptr_metadata_unconstrained_by_fn:
        OnceLock<Mutex<BTreeMap<String, usize>>>,
    /// Per-function static init incomplete counts (Part of #3447).
    pub(in crate::codegen_ay) static_init_incomplete_by_fn:
        OnceLock<Mutex<BTreeMap<String, usize>>>,
    /// Per-function FP bitvector encoding counts (Part of #3447).
    pub(in crate::codegen_ay) fp_bitvector_encoding_by_fn: OnceLock<Mutex<BTreeMap<String, usize>>>,
    /// Per-function aggregate encoding gap counts (Part of #3447).
    pub(in crate::codegen_ay) aggregate_encoding_gap_by_fn:
        OnceLock<Mutex<BTreeMap<String, usize>>>,
    /// Per-function stub approximation counts (Part of #3447).
    pub(in crate::codegen_ay) stub_approximation_by_fn: OnceLock<Mutex<BTreeMap<String, usize>>>,
    /// Per-function drop fallback reasons (Part of #3791).
    /// Outer key: fn_name, inner key: reason string, value: count.
    pub(in crate::codegen_ay) drop_fallback_reasons_by_fn:
        OnceLock<Mutex<BTreeMap<String, BTreeMap<String, usize>>>>,
    /// Per-function translation-drop site reasons (Part of #3794).
    /// Outer key: fn_name, inner key: site reason code, value: count.
    pub(in crate::codegen_ay) translation_drop_site_reasons_by_fn:
        OnceLock<Mutex<BTreeMap<String, BTreeMap<String, usize>>>>,
    /// Per-function inferable summary names (Part of #4031).
    /// Outer key: fn_name (translating function), inner key: P_inf_<callee> name, value: count.
    pub(in crate::codegen_ay) inferable_summary_names_by_fn:
        OnceLock<Mutex<BTreeMap<String, BTreeMap<String, usize>>>>,
    /// Per-function aggregate gap reason tags (Part of #4050).
    /// Outer key: fn_name, inner key: reason tag (e.g., "deref_base_no_state_var"), value: count.
    pub(in crate::codegen_ay) aggregate_gap_reasons_by_fn:
        OnceLock<Mutex<BTreeMap<String, BTreeMap<String, usize>>>>,
    /// Per-function recursive unwind exhaustion counts (Part of #4058).
    /// Records how many recursive-inline exhaustion events occurred per harness,
    /// so the compiler can emit `; RECURSIVE_UNWIND_ASSERTION:` SMT markers.
    pub(in crate::codegen_ay) recursive_unwind_by_fn: OnceLock<Mutex<BTreeMap<String, usize>>>,
    /// Per-function "the straight-line discharge proved the checks UNREACHABLE,
    /// not SAFE" flags. Lets the compiler emit a
    /// `; VACUOUS_ALL_CHECKS_UNREACHABLE:` SMT marker, which is the only way
    /// the distinction survives a discharge that replaces the system with
    /// `false => error`.
    pub(in crate::codegen_ay) vacuous_checks_by_fn: OnceLock<Mutex<BTreeMap<String, usize>>>,
}

/// Single process-global instance of all diagnostic counters (Part of #2906).
pub(in crate::codegen_ay) static GLOBAL_COUNTERS: GlobalDiagnosticCounters =
    GlobalDiagnosticCounters {
        place_translation_drop: AtomicUsize::new(0),
        sound_havoc_drop: AtomicUsize::new(0),
        const_translation_drop: AtomicUsize::new(0),
        unsupported_field_projection: AtomicUsize::new(0),
        unhandled_call: AtomicUsize::new(0),
        error_blocked_fmt: AtomicUsize::new(0),
        known_stdlib_unconstrained: AtomicUsize::new(0),
        inferable_predicate: AtomicUsize::new(0),
        diverging_call_drop: AtomicUsize::new(0),
        offset_provenance_unresolved: AtomicUsize::new(0),
        coerce_eq_dropped_constraint: AtomicUsize::new(0),
        assume_dropped_transition: AtomicUsize::new(0),
        assert_untranslatable: AtomicUsize::new(0),
        heap_check_untranslatable: AtomicUsize::new(0),
        heap_check_unknown_layout: AtomicUsize::new(0),
        store_dropped_transition: AtomicUsize::new(0),
        iterator_unsound_skip: AtomicUsize::new(0),
        bigint_unsound_skip: AtomicUsize::new(0),
        kani_mem_overapprox: AtomicUsize::new(0),
        ptr_metadata_unconstrained: AtomicUsize::new(0),
        static_init_incomplete: AtomicUsize::new(0),
        fp_bitvector_encoding: AtomicUsize::new(0),
        aggregate_encoding_gap: AtomicUsize::new(0),
        stub_approximation: AtomicUsize::new(0),
        recursive_unwind_exhausted: AtomicUsize::new(0),
        rounding_assertion_bypass: AtomicUsize::new(0),
        type_sort_fallback: AtomicUsize::new(0),
        range_spec_next_datatype_path: AtomicU64::new(0),
        range_spec_next_flattened_path: AtomicU64::new(0),
        range_spec_next_fail_closed_path: AtomicU64::new(0),
        vec_builder_pattern: AtomicU64::new(0),
        coerce_eq_dropped_by_fn: OnceLock::new(),
        chc_fallback_counts: OnceLock::new(),
        signedness_fallback_by_fn: OnceLock::new(),
        type_sort_fallback_by_fn: OnceLock::new(),
        store_dropped_by_fn: OnceLock::new(),
        unhandled_call_by_fn: OnceLock::new(),
        translation_drop_by_fn: OnceLock::new(),
        sound_havoc_drop_by_fn: OnceLock::new(),
        kani_mem_overapprox_by_fn: OnceLock::new(),
        offset_provenance_unresolved_by_fn: OnceLock::new(),
        ptr_metadata_unconstrained_by_fn: OnceLock::new(),
        static_init_incomplete_by_fn: OnceLock::new(),
        fp_bitvector_encoding_by_fn: OnceLock::new(),
        aggregate_encoding_gap_by_fn: OnceLock::new(),
        stub_approximation_by_fn: OnceLock::new(),
        drop_fallback_reasons_by_fn: OnceLock::new(),
        translation_drop_site_reasons_by_fn: OnceLock::new(),
        inferable_summary_names_by_fn: OnceLock::new(),
        aggregate_gap_reasons_by_fn: OnceLock::new(),
        recursive_unwind_by_fn: OnceLock::new(),
        vacuous_checks_by_fn: OnceLock::new(),
    };

impl GlobalDiagnosticCounters {
    fn usize_counters(&self) -> [&AtomicUsize; 26] {
        [
            &self.place_translation_drop,
            &self.sound_havoc_drop,
            &self.const_translation_drop,
            &self.unsupported_field_projection,
            &self.unhandled_call,
            &self.error_blocked_fmt,
            &self.known_stdlib_unconstrained,
            &self.inferable_predicate,
            &self.diverging_call_drop,
            &self.offset_provenance_unresolved,
            &self.coerce_eq_dropped_constraint,
            &self.assume_dropped_transition,
            &self.assert_untranslatable,
            &self.heap_check_untranslatable,
            &self.heap_check_unknown_layout,
            &self.store_dropped_transition,
            &self.iterator_unsound_skip,
            &self.bigint_unsound_skip,
            &self.kani_mem_overapprox,
            &self.type_sort_fallback,
            &self.ptr_metadata_unconstrained,
            &self.static_init_incomplete,
            &self.fp_bitvector_encoding,
            &self.aggregate_encoding_gap,
            &self.stub_approximation,
            &self.rounding_assertion_bypass,
        ]
    }

    fn u64_counters(&self) -> [&AtomicU64; 4] {
        [
            &self.range_spec_next_datatype_path,
            &self.range_spec_next_flattened_path,
            &self.range_spec_next_fail_closed_path,
            &self.vec_builder_pattern,
        ]
    }

    /// Reset all diagnostic counters to zero for process-reuse session reset.
    ///
    /// Replaces the scattered `take_*` calls in the old `reset_global_counters_for_session`.
    pub(in crate::codegen_ay) fn reset_all(&self) {
        for counter in self.usize_counters() {
            counter.swap(0, Ordering::Relaxed);
        }
        for counter in self.u64_counters() {
            counter.swap(0, Ordering::Relaxed);
        }
        // Also reset the signedness fallback counter which lives in shared.rs
        // (Part of #2997: break shared→chc cycle).
        crate::codegen_ay::shared::take_signedness_fallback_count();
        // Drain per-function maps
        if let Some(map) = self.coerce_eq_dropped_by_fn.get()
            && let Ok(mut guard) = map.lock()
        {
            guard.clear();
        }
        if let Some(map) = self.chc_fallback_counts.get()
            && let Ok(mut guard) = map.lock()
        {
            guard.clear();
        }
        if let Some(map) = self.signedness_fallback_by_fn.get()
            && let Ok(mut guard) = map.lock()
        {
            guard.clear();
        }
        if let Some(map) = self.type_sort_fallback_by_fn.get()
            && let Ok(mut guard) = map.lock()
        {
            guard.clear();
        }
        if let Some(map) = self.store_dropped_by_fn.get()
            && let Ok(mut guard) = map.lock()
        {
            guard.clear();
        }
        if let Some(map) = self.unhandled_call_by_fn.get()
            && let Ok(mut guard) = map.lock()
        {
            guard.clear();
        }
        if let Some(map) = self.translation_drop_by_fn.get()
            && let Ok(mut guard) = map.lock()
        {
            guard.clear();
        }
        if let Some(map) = self.sound_havoc_drop_by_fn.get()
            && let Ok(mut guard) = map.lock()
        {
            guard.clear();
        }
        if let Some(map) = self.kani_mem_overapprox_by_fn.get()
            && let Ok(mut guard) = map.lock()
        {
            guard.clear();
        }
        if let Some(map) = self.offset_provenance_unresolved_by_fn.get()
            && let Ok(mut guard) = map.lock()
        {
            guard.clear();
        }
        if let Some(map) = self.ptr_metadata_unconstrained_by_fn.get()
            && let Ok(mut guard) = map.lock()
        {
            guard.clear();
        }
        if let Some(map) = self.static_init_incomplete_by_fn.get()
            && let Ok(mut guard) = map.lock()
        {
            guard.clear();
        }
        if let Some(map) = self.fp_bitvector_encoding_by_fn.get()
            && let Ok(mut guard) = map.lock()
        {
            guard.clear();
        }
        if let Some(map) = self.aggregate_encoding_gap_by_fn.get()
            && let Ok(mut guard) = map.lock()
        {
            guard.clear();
        }
        if let Some(map) = self.stub_approximation_by_fn.get()
            && let Ok(mut guard) = map.lock()
        {
            guard.clear();
        }
        if let Some(map) = self.drop_fallback_reasons_by_fn.get()
            && let Ok(mut guard) = map.lock()
        {
            guard.clear();
        }
        if let Some(map) = self.translation_drop_site_reasons_by_fn.get()
            && let Ok(mut guard) = map.lock()
        {
            guard.clear();
        }
        if let Some(map) = self.inferable_summary_names_by_fn.get()
            && let Ok(mut guard) = map.lock()
        {
            guard.clear();
        }
        if let Some(map) = self.aggregate_gap_reasons_by_fn.get()
            && let Ok(mut guard) = map.lock()
        {
            guard.clear();
        }
        if let Some(map) = self.recursive_unwind_by_fn.get()
            && let Ok(mut guard) = map.lock()
        {
            guard.clear();
        }
        if let Some(map) = self.vacuous_checks_by_fn.get()
            && let Ok(mut guard) = map.lock()
        {
            guard.clear();
        }
    }

    // --- Per-function map helpers ---

    /// Lock a `OnceLock<Mutex<BTreeMap>>`, initializing on first access.
    pub(super) fn lock_map(
        slot: &OnceLock<Mutex<BTreeMap<String, usize>>>,
    ) -> std::sync::MutexGuard<'_, BTreeMap<String, usize>> {
        let mutex = slot.get_or_init(|| Mutex::new(BTreeMap::new()));
        match mutex.lock() {
            Ok(guard) => guard,
            Err(poisoned) => poisoned.into_inner(),
        }
    }

    /// Record (accumulate) a count for a function name in a per-function map.
    ///
    /// Uses `get_mut` before `entry` to avoid a `String` allocation when the
    /// key already exists (Part of #2267: allocation debt reduction).
    pub(super) fn record_for_fn(
        slot: &OnceLock<Mutex<BTreeMap<String, usize>>>,
        fn_name: &str,
        count: usize,
    ) {
        if count == 0 {
            return;
        }
        let mut guard = Self::lock_map(slot);
        if let Some(existing) = guard.get_mut(fn_name) {
            *existing += count;
        } else {
            guard.insert(fn_name.to_owned(), count);
        }
    }

    /// Drain a per-function map, returning its contents and resetting to empty.
    pub(super) fn take_map(
        slot: &OnceLock<Mutex<BTreeMap<String, usize>>>,
    ) -> BTreeMap<String, usize> {
        let mut guard = Self::lock_map(slot);
        std::mem::take(&mut *guard)
    }

    // Per-function map operations extracted to diagnostics_per_fn.rs per #3199.
}
