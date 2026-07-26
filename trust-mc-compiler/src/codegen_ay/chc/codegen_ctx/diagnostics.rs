// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Per-context diagnostic counters for CHC encoding quality.
//!
//! Replaces scattered `AtomicUsize::fetch_add` calls across 11+ files with
//! per-`ChcCtx` counters that mirror to process-global atomics at increment
//! time. This keeps per-context observability for tests while preserving the
//! existing global `unsoundness_fields.rs` metadata emission path.
//!
//! Benefits:
//! - Increment sites use `self.diagnostics.field.inc()` instead of importing
//!   a global atomic from another module
//! - Tests can read counters from the `ChcCtx` they own — no `Mutex<()>`
//!   serialization needed
//! - No end-of-translation flush step; counters are globally visible immediately
//!
//! Part of #2906: counter registry consolidation.

use std::cell::Cell;
use std::collections::BTreeMap;
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};

// GlobalDiagnosticCounters and GLOBAL_COUNTERS moved to diagnostics_global.rs per #4206.
pub(in crate::codegen_ay) use super::diagnostics_global::{
    GLOBAL_COUNTERS, GlobalDiagnosticCounters,
};

/// Per-function diagnostic counters for CHC encoding quality.
///
/// Counters that feed metadata use mirrored local+global storage:
/// - local value (`Cell<usize>`) for per-context testing
/// - global atomic (`GLOBAL_COUNTERS`) for metadata collection
///
/// `Default::default()` produces an all-zero/empty instance, so creating a
/// new `ChcCtx` automatically starts with fresh counters.
#[derive(Debug)]
pub(in crate::codegen_ay) struct ChcDiagnostics {
    // === Type translation ===
    /// Unsupported flattened-place reads that drop expression translation.
    /// Holds only NON-recognized-clean (fail-close) sound-fallback drops after
    /// the SoundHavoc split (Part of #unsound-havoc-split).
    pub(in crate::codegen_ay::chc) place_translation_drop: MirroredUsizeCounter,

    /// Recognized-clean SoundHavoc sound-fallback drops (certified fresh havoc),
    /// split out of `place_translation_drop` (Part of #unsound-havoc-split).
    pub(in crate::codegen_ay::chc) sound_havoc_drop: MirroredUsizeCounter,

    /// Unsupported constant translations that return `None`.
    pub(in crate::codegen_ay::chc) const_translation_drop: MirroredUsizeCounter,

    /// Unsupported MIR projection kinds dropped by `extract_field_projections`.
    pub(in crate::codegen_ay::chc) unsupported_field_projection: MirroredUsizeCounter,

    // === Call dispatch ===
    /// Function calls that fall through all dispatch stages.
    pub(in crate::codegen_ay::chc) unhandled_call: MirroredUsizeCounter,

    /// Formatting/panic calls error-blocked (dead-ended, not over-approximation).
    /// Part of #3379: sub-classified from unhandled_call.
    pub(in crate::codegen_ay::chc) error_blocked_fmt: MirroredUsizeCounter,

    /// Known stdlib calls left unconstrained (recognized over-approximation).
    /// Part of #3379: sub-classified from unhandled_call.
    pub(in crate::codegen_ay::chc) known_stdlib_unconstrained: MirroredUsizeCounter,

    /// Calls encoded with solver-inferable function summaries (Part of #3395).
    /// Instead of leaving the destination unconstrained, the return value is
    /// constrained to be an uninterpreted function of the call arguments.
    /// PDR must synthesize a consistent function summary.
    pub(in crate::codegen_ay::chc) inferable_predicate: MirroredUsizeCounter,

    /// Diverging calls (target=None) silently dropped without emitting rules.
    pub(in crate::codegen_ay::chc) diverging_call_drop: MirroredUsizeCounter,

    /// Pointer-offset / deref allocation-bound checks skipped on unresolved
    /// provenance (symbolic obj_id lane). Fail-open — demotes the harness.
    pub(in crate::codegen_ay::chc) offset_provenance_unresolved: MirroredUsizeCounter,

    /// Dropped call-result equality constraints caused by sort mismatch.
    pub(in crate::codegen_ay::chc) coerce_eq_dropped_constraint: MirroredUsizeCounter,

    // === Assertion encoding ===
    /// Dropped `kani::assume` semantics (missing target or encoding failure).
    pub(in crate::codegen_ay::chc) assume_dropped_transition: MirroredUsizeCounter,

    /// Assertions emitted as conservative error rules (untranslatable condition).
    pub(in crate::codegen_ay::chc) assert_untranslatable: MirroredUsizeCounter,

    // === Heap checks ===
    /// Heap safety checks with unsupported sort for boolean conversion.
    pub(in crate::codegen_ay::chc) heap_check_untranslatable: MirroredUsizeCounter,

    /// Heap safety checks with unknown pointee layout.
    pub(in crate::codegen_ay::chc) heap_check_unknown_layout: MirroredUsizeCounter,

    // === Store encoding ===
    /// Silently dropped store transitions (untranslatable projections).
    pub(in crate::codegen_ay::chc) store_dropped_transition: MirroredUsizeCounter,

    // === Stubs ===
    /// Iterator verification skips due to sort mismatch (unsound).
    pub(in crate::codegen_ay::chc) iterator_unsound_skip: MirroredUsizeCounter,

    /// BigInt/BigRational verification skips due to sort mismatch (unsound).
    pub(in crate::codegen_ay::chc) bigint_unsound_skip: MirroredUsizeCounter,

    // === Over-approximation ===
    /// kani::mem predicates over-approximated as true (#3165).
    pub(in crate::codegen_ay::chc) kani_mem_overapprox: MirroredUsizeCounter,

    /// PtrMetadata resolved to unconstrained symbolic (#3447).
    pub(in crate::codegen_ay::chc) ptr_metadata_unconstrained: MirroredUsizeCounter,

    /// Static initializer encoding returned None for composite types (#3447).
    pub(in crate::codegen_ay::chc) static_init_incomplete: MirroredUsizeCounter,

    /// Aggregate/discriminant encoding gap (#3447).
    pub(in crate::codegen_ay::chc) aggregate_encoding_gap: MirroredUsizeCounter,

    /// Stub approximation — stub returned unconstrained symbolic (#3447).
    pub(in crate::codegen_ay::chc) stub_approximation: MirroredUsizeCounter,

    /// Recursive inline unwind budget exhausted (Part of #3929).
    /// Self-recursive call exceeded harness unwind depth; result is
    /// nondeterministic over-approximation instead of generic None fallback.
    pub(in crate::codegen_ay::chc) recursive_unwind_exhausted: MirroredUsizeCounter,

    // === Assertion bypass ===
    /// Float rounding assertion weakened to finiteness tautology (#3779).
    pub(in crate::codegen_ay::chc) rounding_assertion_bypass: MirroredUsizeCounter,

    // === Demoted fallback ===
    /// Local count of `record_fallback()` events for this translation.
    /// Unlike the per-function global map, this stays scoped to one `ChcCtx`.
    pub(in crate::codegen_ay::chc) fallback_count: Cell<usize>,

    /// Per-property error-relation ids (`error_p{id}`) registered for
    /// copy / copy_nonoverlapping / write_bytes SPAN-access UB checks
    /// (alignment / count-overflow / allocation-bound). Recorded at
    /// check-emission time, when the pointer's offset lane is still a symbolic
    /// SSA var so the check has not folded yet. After scalarization const-folds
    /// a fully-concrete (stack-allocation) access, any of these whose check
    /// rule collapsed to an UNCONDITIONAL violation marks a PRECISE,
    /// PROVENANCE-INDEPENDENT genuine failure: the alignment/overflow/bound
    /// obligation does not rest on the over-approximated obj_id lane, so a
    /// const-folded violation is a real bug, not a spurious over-approximation.
    /// At `translate()` finalization this discharges exactly THIS function's
    /// `offset_provenance_unresolved` contribution (`MirroredUsizeCounter::
    /// local`) so the genuine counterexample is no longer masked as an
    /// `EncodingGap` by the provenance-unresolved doubt the same function
    /// accumulated while lowering the pointer arithmetic that produced the
    /// definitely-bad pointer. Per-function `local` bounds the discharge, so
    /// sibling harnesses' fail-closed nets in the crate-global counter stay
    /// intact.
    pub(in crate::codegen_ay::chc) intrinsic_span_property_ids: Vec<u32>,

    /// The exact span-access UB check expressions (alignment / count-overflow /
    /// allocation-bound) produced by `heap_span_access_checks` for
    /// copy / copy_nonoverlapping, eligible for `intrinsic_span_property_ids`
    /// tagging at their drain site. This DELIBERATELY excludes the
    /// range-disjointness obligation: `copy` (overlapping) legally overlaps but
    /// is encoded via the copy_nonoverlapping path, so its disjointness check is
    /// a spurious (non-provenance) violation that must stay masked, not be
    /// promoted to a genuine counterexample. Only checks that are PRECISE and
    /// PROVENANCE-INDEPENDENT — and correct for BOTH copy variants — are
    /// admitted here. Emptied is fine; membership is checked at the drain.
    pub(in crate::codegen_ay::chc) span_check_exprs: std::collections::HashSet<ay_bindings::Expr>,

    // === Per-function maps ===
    /// Per-function dropped coercion constraint map.
    /// Arc<str> keys: O(1) clone from ChcCtx.fn_name instead of O(n) String clone.
    pub(in crate::codegen_ay::chc) coerce_dropped_by_fn: BTreeMap<Arc<str>, usize>,

    // === Type-sort fallback ===
    /// Type-sort translation fallbacks from static `translate_ty`/`translate_adt_ty`.
    /// Captured in `translate_inner` by snapshotting the global TYPE_SORT_FALLBACK_COUNT.
    pub(in crate::codegen_ay::chc) type_sort_fallback: Cell<usize>,

    // === Signedness fallback ===
    /// Signedness fallback events from cast/coerce/comparison paths.
    /// Captured in `translate_inner` by snapshotting the shared signedness fallback counter.
    pub(in crate::codegen_ay::chc) signedness_fallback: Cell<usize>,

    // === Telemetry ===
    /// RangeSpecNext datatype path selections.
    pub(in crate::codegen_ay::chc) range_spec_next_datatype_path: MirroredU64Counter,

    /// RangeSpecNext flattened path selections.
    pub(in crate::codegen_ay::chc) range_spec_next_flattened_path: MirroredU64Counter,

    /// RangeSpecNext fail-closed path selections.
    pub(in crate::codegen_ay::chc) range_spec_next_fail_closed_path: MirroredU64Counter,

    /// Vec builder pattern detections (for-range-push). Part of #3348.
    pub(in crate::codegen_ay::chc) vec_builder_pattern: MirroredU64Counter,

    /// Per-category sound fallback detail (Part of #3561 Phase 1).
    /// Maps category tag → count for the top-3 fallback clusters.
    /// Uncategorized sites still go through `place_translation_drop` alone.
    pub(in crate::codegen_ay::chc) sound_fallback_detail: BTreeMap<&'static str, usize>,
}

impl Default for ChcDiagnostics {
    fn default() -> Self {
        Self {
            place_translation_drop: MirroredUsizeCounter::new(
                &GLOBAL_COUNTERS.place_translation_drop,
            ),
            sound_havoc_drop: MirroredUsizeCounter::new(&GLOBAL_COUNTERS.sound_havoc_drop),
            const_translation_drop: MirroredUsizeCounter::new(
                &GLOBAL_COUNTERS.const_translation_drop,
            ),
            unsupported_field_projection: MirroredUsizeCounter::new(
                &GLOBAL_COUNTERS.unsupported_field_projection,
            ),
            unhandled_call: MirroredUsizeCounter::new(&GLOBAL_COUNTERS.unhandled_call),
            error_blocked_fmt: MirroredUsizeCounter::new(&GLOBAL_COUNTERS.error_blocked_fmt),
            known_stdlib_unconstrained: MirroredUsizeCounter::new(
                &GLOBAL_COUNTERS.known_stdlib_unconstrained,
            ),
            inferable_predicate: MirroredUsizeCounter::new(&GLOBAL_COUNTERS.inferable_predicate),
            diverging_call_drop: MirroredUsizeCounter::new(&GLOBAL_COUNTERS.diverging_call_drop),
            offset_provenance_unresolved: MirroredUsizeCounter::new(
                &GLOBAL_COUNTERS.offset_provenance_unresolved,
            ),
            coerce_eq_dropped_constraint: MirroredUsizeCounter::new(
                &GLOBAL_COUNTERS.coerce_eq_dropped_constraint,
            ),
            assume_dropped_transition: MirroredUsizeCounter::new(
                &GLOBAL_COUNTERS.assume_dropped_transition,
            ),
            assert_untranslatable: MirroredUsizeCounter::new(
                &GLOBAL_COUNTERS.assert_untranslatable,
            ),
            heap_check_untranslatable: MirroredUsizeCounter::new(
                &GLOBAL_COUNTERS.heap_check_untranslatable,
            ),
            heap_check_unknown_layout: MirroredUsizeCounter::new(
                &GLOBAL_COUNTERS.heap_check_unknown_layout,
            ),
            store_dropped_transition: MirroredUsizeCounter::new(
                &GLOBAL_COUNTERS.store_dropped_transition,
            ),
            iterator_unsound_skip: MirroredUsizeCounter::new(
                &GLOBAL_COUNTERS.iterator_unsound_skip,
            ),
            bigint_unsound_skip: MirroredUsizeCounter::new(&GLOBAL_COUNTERS.bigint_unsound_skip),
            kani_mem_overapprox: MirroredUsizeCounter::new(&GLOBAL_COUNTERS.kani_mem_overapprox),
            ptr_metadata_unconstrained: MirroredUsizeCounter::new(
                &GLOBAL_COUNTERS.ptr_metadata_unconstrained,
            ),
            static_init_incomplete: MirroredUsizeCounter::new(
                &GLOBAL_COUNTERS.static_init_incomplete,
            ),
            aggregate_encoding_gap: MirroredUsizeCounter::new(
                &GLOBAL_COUNTERS.aggregate_encoding_gap,
            ),
            stub_approximation: MirroredUsizeCounter::new(&GLOBAL_COUNTERS.stub_approximation),
            recursive_unwind_exhausted: MirroredUsizeCounter::new(
                &GLOBAL_COUNTERS.recursive_unwind_exhausted,
            ),
            rounding_assertion_bypass: MirroredUsizeCounter::new(
                &GLOBAL_COUNTERS.rounding_assertion_bypass,
            ),
            fallback_count: Cell::new(0),
            intrinsic_span_property_ids: Vec::new(),
            span_check_exprs: std::collections::HashSet::new(),
            coerce_dropped_by_fn: BTreeMap::new(),
            type_sort_fallback: Cell::new(0),
            signedness_fallback: Cell::new(0),
            range_spec_next_datatype_path: MirroredU64Counter::new(
                &GLOBAL_COUNTERS.range_spec_next_datatype_path,
            ),
            range_spec_next_flattened_path: MirroredU64Counter::new(
                &GLOBAL_COUNTERS.range_spec_next_flattened_path,
            ),
            range_spec_next_fail_closed_path: MirroredU64Counter::new(
                &GLOBAL_COUNTERS.range_spec_next_fail_closed_path,
            ),
            vec_builder_pattern: MirroredU64Counter::new(&GLOBAL_COUNTERS.vec_builder_pattern),
            sound_fallback_detail: BTreeMap::new(),
        }
    }
}

impl ChcDiagnostics {
    /// Drain global CHC diagnostic counters for process-reuse session reset.
    ///
    /// Delegates to `GLOBAL_COUNTERS.reset_all()` which resets all counters
    /// in a single consolidated call (Part of #2906).
    pub(in crate::codegen_ay) fn reset_global_counters_for_session() {
        GLOBAL_COUNTERS.reset_all();
    }
}

/// Local+global mirrored usize counter.
#[derive(Debug)]
pub(in crate::codegen_ay::chc) struct MirroredUsizeCounter {
    local: Cell<usize>,
    global: &'static AtomicUsize,
}

impl MirroredUsizeCounter {
    fn new(global: &'static AtomicUsize) -> Self {
        Self { local: Cell::new(0), global }
    }

    pub(in crate::codegen_ay::chc) fn get(&self) -> usize {
        self.local.get()
    }

    /// Subtract this context's `local` contribution from the process-global
    /// total and zero the local. Used to discharge a per-function fail-closed
    /// count when a PRECISE, const-folded intrinsic UB violation in the same
    /// function makes that function's accumulated doubt moot (the harness fails
    /// genuinely). `local` bounds the discharge to exactly this `ChcCtx`'s own
    /// increments, so other functions' contributions to the shared global are
    /// never removed. `saturating_sub` guards the (unreachable) underflow case.
    pub(in crate::codegen_ay::chc) fn discharge_local_into_global(&self) {
        let local = self.local.get();
        if local > 0 {
            // `local` is always <= this counter's share of `global`, but clamp
            // defensively so a future double-accounting path can never wrap.
            let mut cur = self.global.load(Ordering::Relaxed);
            loop {
                let next = cur.saturating_sub(local);
                match self.global.compare_exchange_weak(
                    cur,
                    next,
                    Ordering::Relaxed,
                    Ordering::Relaxed,
                ) {
                    Ok(_) => break,
                    Err(observed) => cur = observed,
                }
            }
            self.local.set(0);
        }
    }
}

/// Local+global mirrored u64 counter with usize local view for diagnostics/tests.
#[derive(Debug)]
pub(in crate::codegen_ay::chc) struct MirroredU64Counter {
    local: Cell<usize>,
    global: &'static AtomicU64,
}

impl MirroredU64Counter {
    fn new(global: &'static AtomicU64) -> Self {
        Self { local: Cell::new(0), global }
    }
}

/// Convenience extension for local diagnostic counters.
pub(in crate::codegen_ay::chc) trait CellCounter {
    /// Increment the counter by 1.
    #[track_caller]
    fn inc(&self);

    /// Increment the counter by 1 and return the new value.
    fn inc_get(&self) -> usize;
}

impl CellCounter for Cell<usize> {
    #[track_caller]
    fn inc(&self) {
        self.set(self.get() + 1);
    }

    fn inc_get(&self) -> usize {
        let new = self.get() + 1;
        self.set(new);
        new
    }
}

impl CellCounter for MirroredUsizeCounter {
    fn inc(&self) {
        self.local.set(self.local.get() + 1);
        self.global.fetch_add(1, Ordering::Relaxed);
    }

    fn inc_get(&self) -> usize {
        let new = self.local.get() + 1;
        self.local.set(new);
        self.global.fetch_add(1, Ordering::Relaxed);
        new
    }
}

impl CellCounter for MirroredU64Counter {
    fn inc(&self) {
        self.local.set(self.local.get() + 1);
        self.global.fetch_add(1, Ordering::Relaxed);
    }

    fn inc_get(&self) -> usize {
        let new = self.local.get() + 1;
        self.local.set(new);
        self.global.fetch_add(1, Ordering::Relaxed);
        new
    }
}

#[cfg(test)]
mod tests {
    use super::{CellCounter, MirroredUsizeCounter};
    use std::sync::atomic::{AtomicUsize, Ordering};

    /// `discharge_local_into_global` must remove exactly THIS context's `local`
    /// share from the shared global, leaving sibling contexts' contributions —
    /// the load-bearing fail-closed nets of other harnesses — untouched.
    #[test]
    fn discharge_local_into_global_removes_only_local_share() {
        static G: AtomicUsize = AtomicUsize::new(0);
        let fn_a = MirroredUsizeCounter::new(&G);
        let fn_b = MirroredUsizeCounter::new(&G);
        fn_a.inc();
        fn_a.inc(); // fn_a: local=2, global=2
        fn_b.inc();
        fn_b.inc();
        fn_b.inc(); // fn_b: local=3, global=5
        assert_eq!(G.load(Ordering::Relaxed), 5);

        // fn_a hit a definite intrinsic UB violation → discharge only its share.
        fn_a.discharge_local_into_global();
        assert_eq!(fn_a.get(), 0, "fn_a local zeroed");
        assert_eq!(fn_b.get(), 3, "fn_b local untouched");
        assert_eq!(G.load(Ordering::Relaxed), 3, "only fn_a's 2 removed from the shared global");
    }

    /// A context that never incremented must not perturb the global on discharge
    /// (no spurious underflow, no change).
    #[test]
    fn discharge_local_into_global_noop_when_local_zero() {
        static G: AtomicUsize = AtomicUsize::new(7);
        let c = MirroredUsizeCounter::new(&G);
        c.discharge_local_into_global();
        assert_eq!(G.load(Ordering::Relaxed), 7);
    }

    /// `saturating_sub` guards a global smaller than local (should never occur,
    /// but must never wrap to a huge value).
    #[test]
    fn discharge_local_into_global_saturates() {
        static G: AtomicUsize = AtomicUsize::new(0);
        let c = MirroredUsizeCounter::new(&G);
        c.inc();
        c.inc(); // local=2, global=2
        // Externally drain the global below `local` to force the clamp path.
        G.store(1, Ordering::Relaxed);
        c.discharge_local_into_global();
        assert_eq!(G.load(Ordering::Relaxed), 0, "clamped at zero, no wraparound");
    }
}
