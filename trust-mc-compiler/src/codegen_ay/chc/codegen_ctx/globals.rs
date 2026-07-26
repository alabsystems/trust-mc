// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Global statics, counters, and thread-local accumulators for CHC codegen.
//!
//! Extracted from codegen_ctx.rs per #2408.

use ay_bindings::{Expr, Sort};
use std::cell::RefCell;
use std::collections::BTreeMap;
use std::sync::Arc;
use std::sync::OnceLock;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use tracing::warn;
use trust_mc_core::chc::VarDecl;

use super::diagnostics::GLOBAL_COUNTERS;

/// Check if CHC debug tracing is enabled (#861).
/// Returns true if the CLI flag is set or CHC_DEBUG=1/true.
pub(in crate::codegen_ay::chc) fn chc_debug_enabled() -> bool {
    if CHC_DEBUG_FLAG.load(Ordering::Relaxed) {
        return true;
    }
    static CHC_DEBUG: OnceLock<bool> = OnceLock::new();
    *CHC_DEBUG.get_or_init(|| {
        // Part of #2267: use eq_ignore_ascii_case to avoid String allocation from to_lowercase().
        std::env::var("CHC_DEBUG")
            .map(|v| v == "1" || v.eq_ignore_ascii_case("true"))
            .unwrap_or(false)
    })
}
pub(in crate::codegen_ay::chc) static CHC_DEBUG_FLAG: AtomicBool = AtomicBool::new(false);

/// Global counter for generating unique undefined variable names in CHC encoding.
/// Each None construction gets a fresh symbolic variable for soundness (#679 audit).
pub(in crate::codegen_ay::chc) static UNDEF_COUNTER: AtomicU64 = AtomicU64::new(0);

/// Generate a fresh unique CHC name: `{prefix}_{counter}`.
///
/// Avoids the intermediate `format!("{}_{}", prefix, UNDEF_COUNTER.fetch_add(1, ...)))`
/// allocation that callers would otherwise need. Uses `write!` to a pre-sized buffer.
/// Part of #2267.
pub(in crate::codegen_ay::chc) fn chc_fresh_name(prefix: &str) -> String {
    use std::fmt::Write;
    let n = UNDEF_COUNTER.fetch_add(1, Ordering::SeqCst);
    let mut name = String::with_capacity(prefix.len() + 1 + 20);
    name.push_str(prefix);
    name.push('_');
    let _ = write!(&mut name, "{n}");
    name
}

/// Reset the UNDEF_COUNTER to zero for process-reuse scenarios (Part of #2360).
/// Returns the previous counter value (drain pattern).
pub(in crate::codegen_ay) fn take_undef_counter() -> u64 {
    UNDEF_COUNTER.swap(0, Ordering::Relaxed)
}

// Thread-local accumulator for VarDecls created by static methods (e.g. `coerce_store_value`)
// that cannot access `self.vc`. Drained into `ChcVc` in `translate()` before returning.
// Part of #2317: fixes undeclared `__store_val_N` fresh symbolics.
thread_local! {
    pub(in crate::codegen_ay::chc) static PENDING_FRESH_VAR_DECLS: RefCell<Vec<VarDecl>> = const { RefCell::new(Vec::new()) };
    // Thread-local accumulator for DT sorts discovered by immutable paths
    // (e.g. `option_unwrap_value` field_select) that cannot access `self.vc`.
    // Drained into `ChcVc` alongside PENDING_FRESH_VAR_DECLS in `translate()`.
    // Part of #4053: fixes undeclared `value_Option_bool` from inline Option unwrap.
    pub(in crate::codegen_ay::chc) static PENDING_DATATYPE_SORTS: RefCell<Vec<Sort>> = const { RefCell::new(Vec::new()) };
}

/// Clears `PENDING_FRESH_VAR_DECLS` when unwinding out of CHC translation.
///
/// `translate_inner()` drains pending declarations on the success path. This guard
/// covers panic paths so stale declarations cannot leak into a later translation
/// on the same thread (Part of #2950).
pub(in crate::codegen_ay::chc) struct PendingFreshVarDeclsPanicGuard;

impl PendingFreshVarDeclsPanicGuard {
    #[must_use]
    pub(in crate::codegen_ay::chc) fn arm() -> Self {
        Self
    }
}

impl Drop for PendingFreshVarDeclsPanicGuard {
    fn drop(&mut self) {
        if std::thread::panicking() {
            PENDING_FRESH_VAR_DECLS.with(|decls| {
                decls.borrow_mut().clear();
            });
            PENDING_DATATYPE_SORTS.with(|sorts| {
                sorts.borrow_mut().clear();
            });
        }
    }
}

/// Push a DT sort to the thread-local pending list for late declaration.
/// Called from immutable codegen paths (e.g. `option_unwrap_value`) that
/// generate DT field_select expressions without `&mut self` access.
/// Part of #4053.
pub(in crate::codegen_ay::chc) fn push_pending_datatype_sort(sort: Sort) {
    PENDING_DATATYPE_SORTS.with(|sorts| {
        sorts.borrow_mut().push(sort);
    });
}

/// Push a fresh VarDecl to the thread-local pending list.
/// Called from static methods that create fresh symbolic variables.
///
/// Part of #2267: accepts `impl Into<Arc<str>>` to avoid String allocation
/// when called with `Arc<str>` from state_vars.
pub(in crate::codegen_ay::chc) fn push_pending_var_decl(name: impl Into<Arc<str>>, sort: Sort) {
    PENDING_FRESH_VAR_DECLS.with(|decls| {
        decls.borrow_mut().push(VarDecl::new(name, sort));
    });
}

/// Declare a pending variable and return its Expr in one step.
///
/// Combines `push_pending_var_decl` + `Expr::var` with a single name
/// allocation instead of two. The name is moved into the Expr and a
/// borrow is used for the VarDecl registration.
#[must_use]
pub(in crate::codegen_ay::chc) fn declare_pending_var(name: String, sort: Sort) -> Expr {
    let expr = Expr::var(&*name, sort.clone());
    push_pending_var_decl(name, sort);
    expr
}

// Diagnostic counters (TYPE_SORT_FALLBACK_COUNT, UNHANDLED_CALL_COUNT,
// CHC_FALLBACK_COUNTS) consolidated into GLOBAL_COUNTERS (Part of #2906).
// Functions below delegate to GLOBAL_COUNTERS fields/methods.

/// Record a type-sort fallback in a static translation function (Part of #2240).
/// Increments the global counter and emits a warning with the site description.
pub(in crate::codegen_ay::chc) fn record_type_sort_fallback(site: &str) {
    GLOBAL_COUNTERS.type_sort_fallback.fetch_add(1, Ordering::Relaxed);
    warn!(site, "CHC type-sort fallback: substituted hard-coded sort for untranslatable type");
}

/// Reset the type-sort fallback counter, returning the previous value (Part of #2360).
pub(in crate::codegen_ay) fn take_type_sort_fallback_count() -> usize {
    GLOBAL_COUNTERS.type_sort_fallback.swap(0, Ordering::Relaxed)
}

#[cfg(test)]
pub(in crate::codegen_ay) fn set_type_sort_fallback_count_for_test(count: usize) {
    GLOBAL_COUNTERS.type_sort_fallback.store(count, Ordering::Relaxed);
}

/// Get the current unhandled call count (#2573).
#[cfg(test)]
pub(in crate::codegen_ay) fn get_chc_unhandled_call_count() -> usize {
    GLOBAL_COUNTERS.unhandled_call.load(Ordering::Relaxed)
}

/// Reset the unhandled call counter, returning the previous value (#2573).
pub(in crate::codegen_ay) fn take_chc_unhandled_call_count() -> usize {
    GLOBAL_COUNTERS.unhandled_call.swap(0, Ordering::Relaxed)
}

/// Set the unhandled call count for testing (#2602).
#[cfg(test)]
pub(in crate::codegen_ay) fn set_chc_unhandled_call_count_for_test(count: usize) {
    GLOBAL_COUNTERS.unhandled_call.store(count, Ordering::Relaxed);
}

/// Reset the error-blocked-fmt counter, returning the previous value (#3379).
pub(in crate::codegen_ay) fn take_error_blocked_fmt_count() -> usize {
    GLOBAL_COUNTERS.error_blocked_fmt.swap(0, Ordering::Relaxed)
}

/// Reset the known-stdlib-unconstrained counter, returning the previous value (#3379).
pub(in crate::codegen_ay) fn take_known_stdlib_unconstrained_count() -> usize {
    GLOBAL_COUNTERS.known_stdlib_unconstrained.swap(0, Ordering::Relaxed)
}

/// Non-destructive read of the inferable-predicate counter (Part of #3493).
pub(in crate::codegen_ay) fn get_inferable_predicate_count() -> usize {
    GLOBAL_COUNTERS.inferable_predicate.load(Ordering::Relaxed)
}

/// Reset the inferable-predicate counter, returning the previous value (#3395).
pub(in crate::codegen_ay) fn take_inferable_predicate_count() -> usize {
    GLOBAL_COUNTERS.inferable_predicate.swap(0, Ordering::Relaxed)
}

/// Reset the diverging call drop counter, returning the previous value (#3164).
pub(in crate::codegen_ay) fn take_chc_diverging_call_drop_count() -> usize {
    GLOBAL_COUNTERS.diverging_call_drop.swap(0, Ordering::Relaxed)
}

/// Reset the offset-provenance-unresolved counter, returning the previous value.
pub(in crate::codegen_ay) fn take_chc_offset_provenance_unresolved_count() -> usize {
    GLOBAL_COUNTERS.offset_provenance_unresolved.swap(0, Ordering::Relaxed)
}

/// Record per-function offset-provenance-unresolved count (marker:
/// offset_isize_overflow_precise). Attributes the demotion to the harness
/// whose codegen accumulated it so it cannot leak onto siblings.
pub(in crate::codegen_ay::chc) fn record_offset_provenance_unresolved_for_fn(
    fn_name: &str,
    count: usize,
) {
    GLOBAL_COUNTERS.record_offset_provenance_unresolved_for_fn(fn_name, count);
}

/// Take (drain) the per-function offset-provenance-unresolved map.
pub(in crate::codegen_ay) fn take_offset_provenance_unresolved_by_fn() -> BTreeMap<String, usize> {
    GLOBAL_COUNTERS.take_offset_provenance_unresolved_by_fn()
}

/// Reset the kani::mem over-approximation counter, returning the previous value (#3165).
pub(in crate::codegen_ay) fn take_kani_mem_overapprox_count() -> usize {
    GLOBAL_COUNTERS.kani_mem_overapprox.swap(0, Ordering::Relaxed)
}

/// Record per-function kani::mem over-approximation delta (Part of #3165).
pub(in crate::codegen_ay::chc) fn record_kani_mem_overapprox_for_fn(fn_name: &str, count: usize) {
    GLOBAL_COUNTERS.record_kani_mem_overapprox_for_fn(fn_name, count);
}

/// Take (drain) the per-function kani::mem over-approximation map (Part of #3165).
pub(in crate::codegen_ay) fn take_kani_mem_overapprox_by_fn() -> BTreeMap<String, usize> {
    GLOBAL_COUNTERS.take_kani_mem_overapprox_by_fn()
}

/// Delegate to GLOBAL_COUNTERS for per-function fallback counts (Part of #2906).
/// Visible to the whole codegen_ay layer: the emit-time degenerate-system
/// fail-close (#67, `split_emit_chc`) bumps the count from outside `chc`.
pub(in crate::codegen_ay) fn set_chc_fallback_count_for_fn(fn_name: &str, fallback_count: usize) {
    GLOBAL_COUNTERS.set_chc_fallback_count_for_fn(fn_name, fallback_count);
}

#[cfg(test)]
pub(in crate::codegen_ay::chc) fn get_chc_fallback_counts() -> BTreeMap<String, usize> {
    GLOBAL_COUNTERS.get_chc_fallback_counts()
}

// W1:3920 added this function; its caller in compiler_interface.rs is not yet committed.
// Allow dead_code until W1 commits the caller. (Build gate fix for clippy -D warnings)
#[allow(dead_code)]
pub(in crate::codegen_ay) fn get_chc_fallback_count_for_fn(fn_name: &str) -> usize {
    GLOBAL_COUNTERS.get_chc_fallback_count_for_fn(fn_name)
}

pub(in crate::codegen_ay) fn take_chc_fallback_counts() -> BTreeMap<String, usize> {
    GLOBAL_COUNTERS.take_chc_fallback_counts()
}

/// Part of #4058: per-harness recursive unwind exhaustion count.
#[allow(dead_code)] // Call site wired in W1:4385 INCOMPLETE
pub(in crate::codegen_ay) fn get_recursive_unwind_count_for_fn(fn_name: &str) -> usize {
    GLOBAL_COUNTERS.get_recursive_unwind_count_for_fn(fn_name)
}

/// Part of #4058: record per-function recursive unwind exhaustion count.
pub(in crate::codegen_ay::chc) fn record_recursive_unwind_for_fn(fn_name: &str, count: usize) {
    GLOBAL_COUNTERS.record_recursive_unwind_for_fn(fn_name, count);
}

#[cfg(test)]
pub(in crate::codegen_ay) fn clear_chc_fallback_counts() {
    GLOBAL_COUNTERS.clear_chc_fallback_counts();
}

#[cfg(test)]
pub(in crate::codegen_ay) fn set_chc_fallback_count_for_test(fn_name: &str, fallback_count: usize) {
    set_chc_fallback_count_for_fn(fn_name, fallback_count);
}

// --- Per-function signedness/type-sort fallback maps (Part of #2959) ---

/// Record per-function signedness fallback delta after CHC translation.
pub(in crate::codegen_ay::chc) fn record_signedness_fallback_for_fn(fn_name: &str, count: usize) {
    GLOBAL_COUNTERS.record_signedness_fallback_for_fn(fn_name, count);
}

/// Take (drain) the per-function signedness fallback map for metadata emission.
pub(in crate::codegen_ay) fn take_signedness_fallback_by_fn() -> BTreeMap<String, usize> {
    GLOBAL_COUNTERS.take_signedness_fallback_by_fn()
}

/// Record per-function type-sort fallback delta after CHC translation.
pub(in crate::codegen_ay::chc) fn record_type_sort_fallback_for_fn(fn_name: &str, count: usize) {
    GLOBAL_COUNTERS.record_type_sort_fallback_for_fn(fn_name, count);
}

/// Take (drain) the per-function type-sort fallback map for metadata emission.
pub(in crate::codegen_ay) fn take_type_sort_fallback_by_fn() -> BTreeMap<String, usize> {
    GLOBAL_COUNTERS.take_type_sort_fallback_by_fn()
}

/// Record per-function store-dropped-transition delta after CHC translation (Part of #2966).
pub(in crate::codegen_ay::chc) fn record_store_dropped_for_fn(fn_name: &str, count: usize) {
    GLOBAL_COUNTERS.record_store_dropped_for_fn(fn_name, count);
}

/// Take (drain) the per-function store-dropped-transition map for metadata emission.
pub(in crate::codegen_ay) fn take_store_dropped_by_fn() -> BTreeMap<String, usize> {
    GLOBAL_COUNTERS.take_store_dropped_by_fn()
}

/// Record per-function unhandled-call delta after CHC translation (Part of #2966).
pub(in crate::codegen_ay::chc) fn record_unhandled_call_for_fn(fn_name: &str, count: usize) {
    GLOBAL_COUNTERS.record_unhandled_call_for_fn(fn_name, count);
}

/// Take (drain) the per-function unhandled-call map for metadata emission.
pub(in crate::codegen_ay) fn take_unhandled_call_by_fn() -> BTreeMap<String, usize> {
    GLOBAL_COUNTERS.take_unhandled_call_by_fn()
}

/// Record per-function translation-drop combined delta after CHC translation (Part of #2966).
pub(in crate::codegen_ay::chc) fn record_translation_drop_for_fn(fn_name: &str, count: usize) {
    GLOBAL_COUNTERS.record_translation_drop_for_fn(fn_name, count);
}

/// Take (drain) the per-function translation-drop map for metadata emission.
pub(in crate::codegen_ay) fn take_translation_drop_by_fn() -> BTreeMap<String, usize> {
    GLOBAL_COUNTERS.take_translation_drop_by_fn()
}

/// Record per-function recognized-clean SoundHavoc-drop delta after CHC
/// translation (Part of #unsound-havoc-split).
pub(in crate::codegen_ay::chc) fn record_sound_havoc_drop_for_fn(fn_name: &str, count: usize) {
    GLOBAL_COUNTERS.record_sound_havoc_drop_for_fn(fn_name, count);
}

/// Take (drain) the per-function SoundHavoc-drop map for metadata emission.
pub(in crate::codegen_ay) fn take_sound_havoc_drop_by_fn() -> BTreeMap<String, usize> {
    GLOBAL_COUNTERS.take_sound_havoc_drop_by_fn()
}

// --- PtrMetadata unconstrained (Part of #3447) ---

/// Non-destructive read of the PtrMetadata unconstrained counter.
pub(in crate::codegen_ay) fn get_ptr_metadata_unconstrained_count() -> usize {
    GLOBAL_COUNTERS.ptr_metadata_unconstrained.load(Ordering::Relaxed)
}

/// Reset the PtrMetadata unconstrained counter, returning the previous value.
pub(in crate::codegen_ay) fn take_ptr_metadata_unconstrained_count() -> usize {
    GLOBAL_COUNTERS.ptr_metadata_unconstrained.swap(0, Ordering::Relaxed)
}

/// Record per-function PtrMetadata unconstrained delta.
pub(in crate::codegen_ay::chc) fn record_ptr_metadata_unconstrained_for_fn(
    fn_name: &str,
    count: usize,
) {
    GLOBAL_COUNTERS.record_ptr_metadata_unconstrained_for_fn(fn_name, count);
}

/// Take (drain) the per-function PtrMetadata unconstrained map.
pub(in crate::codegen_ay) fn take_ptr_metadata_unconstrained_by_fn() -> BTreeMap<String, usize> {
    GLOBAL_COUNTERS.take_ptr_metadata_unconstrained_by_fn()
}

// --- Static init incomplete (Part of #3447) ---

/// Non-destructive read of the static init incomplete counter.
pub(in crate::codegen_ay) fn get_static_init_incomplete_count() -> usize {
    GLOBAL_COUNTERS.static_init_incomplete.load(Ordering::Relaxed)
}

/// Reset the static init incomplete counter, returning the previous value.
pub(in crate::codegen_ay) fn take_static_init_incomplete_count() -> usize {
    GLOBAL_COUNTERS.static_init_incomplete.swap(0, Ordering::Relaxed)
}

/// Record per-function static init incomplete delta.
pub(in crate::codegen_ay::chc) fn record_static_init_incomplete_for_fn(
    fn_name: &str,
    count: usize,
) {
    GLOBAL_COUNTERS.record_static_init_incomplete_for_fn(fn_name, count);
}

/// Take (drain) the per-function static init incomplete map.
pub(in crate::codegen_ay) fn take_static_init_incomplete_by_fn() -> BTreeMap<String, usize> {
    GLOBAL_COUNTERS.take_static_init_incomplete_by_fn()
}

// --- FP bitvector encoding (Part of #3447) ---

/// Non-destructive read of the FP bitvector encoding counter.
pub(in crate::codegen_ay) fn get_fp_bitvector_encoding_count() -> usize {
    GLOBAL_COUNTERS.fp_bitvector_encoding.load(Ordering::Relaxed)
}

/// Increment the FP bitvector encoding counter. Used from static `translate_ty`.
pub(in crate::codegen_ay) fn record_fp_bitvector_encoding() {
    GLOBAL_COUNTERS.fp_bitvector_encoding.fetch_add(1, Ordering::Relaxed);
}

/// Reset the FP bitvector encoding counter, returning the previous value.
pub(in crate::codegen_ay) fn take_fp_bitvector_encoding_count() -> usize {
    GLOBAL_COUNTERS.fp_bitvector_encoding.swap(0, Ordering::Relaxed)
}

/// Record per-function FP bitvector encoding delta.
pub(in crate::codegen_ay::chc) fn record_fp_bitvector_encoding_for_fn(fn_name: &str, count: usize) {
    GLOBAL_COUNTERS.record_fp_bitvector_encoding_for_fn(fn_name, count);
}

/// Take (drain) the per-function FP bitvector encoding map.
pub(in crate::codegen_ay) fn take_fp_bitvector_encoding_by_fn() -> BTreeMap<String, usize> {
    GLOBAL_COUNTERS.take_fp_bitvector_encoding_by_fn()
}

// --- Aggregate encoding gap (Part of #3447) ---

/// Non-destructive read of the aggregate encoding gap counter.
pub(in crate::codegen_ay) fn get_aggregate_encoding_gap_count() -> usize {
    GLOBAL_COUNTERS.aggregate_encoding_gap.load(Ordering::Relaxed)
}

/// Reset the aggregate encoding gap counter, returning the previous value.
pub(in crate::codegen_ay) fn take_aggregate_encoding_gap_count() -> usize {
    GLOBAL_COUNTERS.aggregate_encoding_gap.swap(0, Ordering::Relaxed)
}

/// Record per-function aggregate encoding gap delta.
pub(in crate::codegen_ay::chc) fn record_aggregate_encoding_gap_for_fn(
    fn_name: &str,
    count: usize,
) {
    GLOBAL_COUNTERS.record_aggregate_encoding_gap_for_fn(fn_name, count);
}

/// Take (drain) the per-function aggregate encoding gap map.
pub(in crate::codegen_ay) fn take_aggregate_encoding_gap_by_fn() -> BTreeMap<String, usize> {
    GLOBAL_COUNTERS.take_aggregate_encoding_gap_by_fn()
}

// --- Stub approximation (Part of #3447) ---

/// Non-destructive read of the stub approximation counter.
pub(in crate::codegen_ay) fn get_stub_approximation_count() -> usize {
    GLOBAL_COUNTERS.stub_approximation.load(Ordering::Relaxed)
}

/// Reset the stub approximation counter, returning the previous value.
pub(in crate::codegen_ay) fn take_stub_approximation_count() -> usize {
    GLOBAL_COUNTERS.stub_approximation.swap(0, Ordering::Relaxed)
}

/// Record per-function stub approximation delta.
pub(in crate::codegen_ay::chc) fn record_stub_approximation_for_fn(fn_name: &str, count: usize) {
    GLOBAL_COUNTERS.record_stub_approximation_for_fn(fn_name, count);
}

/// Take (drain) the per-function stub approximation map.
pub(in crate::codegen_ay) fn take_stub_approximation_by_fn() -> BTreeMap<String, usize> {
    GLOBAL_COUNTERS.take_stub_approximation_by_fn()
}

// --- Rounding assertion bypass (Part of #3779) ---

/// Non-destructive read of the rounding assertion bypass counter.
pub(in crate::codegen_ay) fn get_rounding_assertion_bypass_count() -> usize {
    GLOBAL_COUNTERS.rounding_assertion_bypass.load(Ordering::Relaxed)
}

/// Reset the rounding assertion bypass counter, returning the previous value.
pub(in crate::codegen_ay) fn take_rounding_assertion_bypass_count() -> usize {
    GLOBAL_COUNTERS.rounding_assertion_bypass.swap(0, Ordering::Relaxed)
}

// --- Drop fallback reasons (Part of #3791) ---

/// Record a drop fallback reason for a specific function.
pub(in crate::codegen_ay::chc) fn record_drop_fallback_reason_for_fn(fn_name: &str, reason: &str) {
    GLOBAL_COUNTERS.record_drop_fallback_reason_for_fn(fn_name, reason);
}

/// Take (drain) the per-function drop fallback reasons map.
pub(in crate::codegen_ay) fn take_drop_fallback_reasons_by_fn()
-> BTreeMap<String, BTreeMap<String, usize>> {
    GLOBAL_COUNTERS.take_drop_fallback_reasons_by_fn()
}

// --- Translation-drop site reasons (Part of #3794) ---

/// Record a translation-drop site reason for a specific function.
pub(in crate::codegen_ay::chc) fn record_translation_drop_site_reason_for_fn(
    fn_name: &str,
    reason: &str,
) {
    GLOBAL_COUNTERS.record_translation_drop_site_reason_for_fn(fn_name, reason);
}

/// Take (drain) the per-function translation-drop site reasons map.
pub(in crate::codegen_ay) fn take_translation_drop_site_reasons_by_fn()
-> BTreeMap<String, BTreeMap<String, usize>> {
    GLOBAL_COUNTERS.take_translation_drop_site_reasons_by_fn()
}

// --- Inferable summary names (Part of #4031) ---

/// Record an inferable summary name for a specific function.
pub(in crate::codegen_ay::chc) fn record_inferable_summary_name_for_fn(
    fn_name: &str,
    summary_name: &str,
) {
    GLOBAL_COUNTERS.record_inferable_summary_name_for_fn(fn_name, summary_name);
}

/// Take (drain) the per-function inferable summary names map.
#[allow(dead_code)] // Reached via `chc` re-exports in metadata/tests.
pub(in crate::codegen_ay) fn take_inferable_summary_names_by_fn()
-> BTreeMap<String, BTreeMap<String, usize>> {
    GLOBAL_COUNTERS.take_inferable_summary_names_by_fn()
}

// --- Aggregate gap reasons (Part of #4050) ---

/// Record a per-site aggregate gap reason for a specific function.
pub(in crate::codegen_ay::chc) fn record_aggregate_gap_reason_for_fn(fn_name: &str, reason: &str) {
    GLOBAL_COUNTERS.record_aggregate_gap_reason_for_fn(fn_name, reason);
}
