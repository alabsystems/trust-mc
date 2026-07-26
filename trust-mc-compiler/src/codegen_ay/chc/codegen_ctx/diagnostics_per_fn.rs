// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Per-function diagnostic map operations on `GlobalDiagnosticCounters`.
//!
//! Split from diagnostics.rs per #3199.
//! Contains: record/take/get/clear/set methods for 7 per-function metric maps.

use std::collections::BTreeMap;

use super::diagnostics::GlobalDiagnosticCounters;

impl GlobalDiagnosticCounters {
    // --- Coerce-eq per-function map operations ---

    pub(in crate::codegen_ay) fn record_coerce_eq_dropped_for_fn(
        &self,
        fn_name: &str,
        count: usize,
    ) {
        Self::record_for_fn(&self.coerce_eq_dropped_by_fn, fn_name, count);
    }

    pub(in crate::codegen_ay) fn take_coerce_eq_dropped_by_fn(&self) -> BTreeMap<String, usize> {
        Self::take_map(&self.coerce_eq_dropped_by_fn)
    }

    #[cfg(all(test, feature = "compiler-corpus-tests"))]
    pub(in crate::codegen_ay) fn get_coerce_eq_dropped_by_fn(&self) -> BTreeMap<String, usize> {
        Self::lock_map(&self.coerce_eq_dropped_by_fn).clone()
    }

    #[cfg(test)]
    pub(in crate::codegen_ay) fn clear_coerce_eq_dropped_by_fn(&self) {
        Self::lock_map(&self.coerce_eq_dropped_by_fn).clear();
    }

    #[cfg(test)]
    pub(in crate::codegen_ay) fn set_coerce_eq_dropped_for_test(
        &self,
        fn_name: &str,
        count: usize,
    ) {
        let mut guard = Self::lock_map(&self.coerce_eq_dropped_by_fn);
        if count == 0 {
            guard.remove(fn_name);
        } else if let Some(existing) = guard.get_mut(fn_name) {
            *existing = count;
        } else {
            guard.insert(fn_name.to_owned(), count);
        }
    }

    // --- CHC fallback counts map operations ---

    pub(in crate::codegen_ay) fn set_chc_fallback_count_for_fn(&self, fn_name: &str, count: usize) {
        let mut guard = Self::lock_map(&self.chc_fallback_counts);
        if count == 0 {
            guard.remove(fn_name);
        } else if let Some(existing) = guard.get_mut(fn_name) {
            *existing = count;
        } else {
            guard.insert(fn_name.to_owned(), count);
        }
    }

    pub(in crate::codegen_ay) fn take_chc_fallback_counts(&self) -> BTreeMap<String, usize> {
        Self::take_map(&self.chc_fallback_counts)
    }

    #[allow(dead_code)] // W1:3920: caller not yet committed
    pub(in crate::codegen_ay) fn get_chc_fallback_count_for_fn(&self, fn_name: &str) -> usize {
        Self::lock_map(&self.chc_fallback_counts).get(fn_name).copied().unwrap_or(0)
    }

    #[cfg(test)]
    pub(in crate::codegen_ay) fn get_chc_fallback_counts(&self) -> BTreeMap<String, usize> {
        Self::lock_map(&self.chc_fallback_counts).clone()
    }

    #[cfg(test)]
    pub(in crate::codegen_ay) fn clear_chc_fallback_counts(&self) {
        Self::lock_map(&self.chc_fallback_counts).clear();
    }

    // --- Signedness/type-sort per-function maps (Part of #2959) ---

    pub(in crate::codegen_ay) fn record_signedness_fallback_for_fn(
        &self,
        fn_name: &str,
        count: usize,
    ) {
        Self::record_for_fn(&self.signedness_fallback_by_fn, fn_name, count);
    }

    pub(in crate::codegen_ay) fn take_signedness_fallback_by_fn(&self) -> BTreeMap<String, usize> {
        Self::take_map(&self.signedness_fallback_by_fn)
    }

    pub(in crate::codegen_ay) fn record_type_sort_fallback_for_fn(
        &self,
        fn_name: &str,
        count: usize,
    ) {
        Self::record_for_fn(&self.type_sort_fallback_by_fn, fn_name, count);
    }

    pub(in crate::codegen_ay) fn take_type_sort_fallback_by_fn(&self) -> BTreeMap<String, usize> {
        Self::take_map(&self.type_sort_fallback_by_fn)
    }

    // --- Store-dropped per-function map (Part of #2966) ---

    pub(in crate::codegen_ay) fn record_store_dropped_for_fn(&self, fn_name: &str, count: usize) {
        Self::record_for_fn(&self.store_dropped_by_fn, fn_name, count);
    }

    pub(in crate::codegen_ay) fn take_store_dropped_by_fn(&self) -> BTreeMap<String, usize> {
        Self::take_map(&self.store_dropped_by_fn)
    }

    // --- Unhandled-call per-function map (Part of #2966) ---

    pub(in crate::codegen_ay) fn record_unhandled_call_for_fn(&self, fn_name: &str, count: usize) {
        Self::record_for_fn(&self.unhandled_call_by_fn, fn_name, count);
    }

    pub(in crate::codegen_ay) fn take_unhandled_call_by_fn(&self) -> BTreeMap<String, usize> {
        Self::take_map(&self.unhandled_call_by_fn)
    }

    // --- Translation-drop per-function map (Part of #2966) ---

    pub(in crate::codegen_ay) fn record_translation_drop_for_fn(
        &self,
        fn_name: &str,
        count: usize,
    ) {
        Self::record_for_fn(&self.translation_drop_by_fn, fn_name, count);
    }

    pub(in crate::codegen_ay) fn take_translation_drop_by_fn(&self) -> BTreeMap<String, usize> {
        Self::take_map(&self.translation_drop_by_fn)
    }

    // --- SoundHavoc-drop per-function map (Part of #unsound-havoc-split) ---

    pub(in crate::codegen_ay) fn record_sound_havoc_drop_for_fn(
        &self,
        fn_name: &str,
        count: usize,
    ) {
        Self::record_for_fn(&self.sound_havoc_drop_by_fn, fn_name, count);
    }

    pub(in crate::codegen_ay) fn take_sound_havoc_drop_by_fn(&self) -> BTreeMap<String, usize> {
        Self::take_map(&self.sound_havoc_drop_by_fn)
    }

    // --- kani::mem over-approximation per-function map (Part of #3165) ---

    pub(in crate::codegen_ay) fn record_kani_mem_overapprox_for_fn(
        &self,
        fn_name: &str,
        count: usize,
    ) {
        Self::record_for_fn(&self.kani_mem_overapprox_by_fn, fn_name, count);
    }

    pub(in crate::codegen_ay) fn take_kani_mem_overapprox_by_fn(&self) -> BTreeMap<String, usize> {
        Self::take_map(&self.kani_mem_overapprox_by_fn)
    }

    // --- offset-provenance-unresolved per-function map (marker:
    // offset_isize_overflow_precise) ---

    pub(in crate::codegen_ay) fn record_offset_provenance_unresolved_for_fn(
        &self,
        fn_name: &str,
        count: usize,
    ) {
        Self::record_for_fn(&self.offset_provenance_unresolved_by_fn, fn_name, count);
    }

    pub(in crate::codegen_ay) fn take_offset_provenance_unresolved_by_fn(
        &self,
    ) -> BTreeMap<String, usize> {
        Self::take_map(&self.offset_provenance_unresolved_by_fn)
    }

    // --- PtrMetadata unconstrained per-function map (Part of #3447) ---

    pub(in crate::codegen_ay) fn record_ptr_metadata_unconstrained_for_fn(
        &self,
        fn_name: &str,
        count: usize,
    ) {
        Self::record_for_fn(&self.ptr_metadata_unconstrained_by_fn, fn_name, count);
    }

    pub(in crate::codegen_ay) fn take_ptr_metadata_unconstrained_by_fn(
        &self,
    ) -> BTreeMap<String, usize> {
        Self::take_map(&self.ptr_metadata_unconstrained_by_fn)
    }

    // --- Static init incomplete per-function map (Part of #3447) ---

    pub(in crate::codegen_ay) fn record_static_init_incomplete_for_fn(
        &self,
        fn_name: &str,
        count: usize,
    ) {
        Self::record_for_fn(&self.static_init_incomplete_by_fn, fn_name, count);
    }

    pub(in crate::codegen_ay) fn take_static_init_incomplete_by_fn(
        &self,
    ) -> BTreeMap<String, usize> {
        Self::take_map(&self.static_init_incomplete_by_fn)
    }

    // --- FP bitvector encoding per-function map (Part of #3447) ---

    pub(in crate::codegen_ay) fn record_fp_bitvector_encoding_for_fn(
        &self,
        fn_name: &str,
        count: usize,
    ) {
        Self::record_for_fn(&self.fp_bitvector_encoding_by_fn, fn_name, count);
    }

    pub(in crate::codegen_ay) fn take_fp_bitvector_encoding_by_fn(
        &self,
    ) -> BTreeMap<String, usize> {
        Self::take_map(&self.fp_bitvector_encoding_by_fn)
    }

    // --- Aggregate encoding gap per-function map (Part of #3447) ---

    pub(in crate::codegen_ay) fn record_aggregate_encoding_gap_for_fn(
        &self,
        fn_name: &str,
        count: usize,
    ) {
        Self::record_for_fn(&self.aggregate_encoding_gap_by_fn, fn_name, count);
    }

    pub(in crate::codegen_ay) fn take_aggregate_encoding_gap_by_fn(
        &self,
    ) -> BTreeMap<String, usize> {
        Self::take_map(&self.aggregate_encoding_gap_by_fn)
    }

    // --- Stub approximation per-function map (Part of #3447) ---

    pub(in crate::codegen_ay) fn record_stub_approximation_for_fn(
        &self,
        fn_name: &str,
        count: usize,
    ) {
        Self::record_for_fn(&self.stub_approximation_by_fn, fn_name, count);
    }

    pub(in crate::codegen_ay) fn take_stub_approximation_by_fn(&self) -> BTreeMap<String, usize> {
        Self::take_map(&self.stub_approximation_by_fn)
    }

    // --- Drop fallback reasons per-function map (Part of #3791) ---

    pub(in crate::codegen_ay) fn record_drop_fallback_reason_for_fn(
        &self,
        fn_name: &str,
        reason: &str,
    ) {
        use std::sync::Mutex;
        let mutex = self.drop_fallback_reasons_by_fn.get_or_init(|| Mutex::new(BTreeMap::new()));
        let mut guard = match mutex.lock() {
            Ok(g) => g,
            Err(poisoned) => poisoned.into_inner(),
        };
        let reasons = guard.entry(fn_name.to_owned()).or_default();
        *reasons.entry(reason.to_owned()).or_insert(0) += 1;
    }

    pub(in crate::codegen_ay) fn take_drop_fallback_reasons_by_fn(
        &self,
    ) -> BTreeMap<String, BTreeMap<String, usize>> {
        use std::sync::Mutex;
        let mutex = self.drop_fallback_reasons_by_fn.get_or_init(|| Mutex::new(BTreeMap::new()));
        let mut guard = match mutex.lock() {
            Ok(g) => g,
            Err(poisoned) => poisoned.into_inner(),
        };
        std::mem::take(&mut *guard)
    }

    // --- Translation-drop site reasons per-function map (Part of #3794) ---

    pub(in crate::codegen_ay) fn record_translation_drop_site_reason_for_fn(
        &self,
        fn_name: &str,
        reason: &str,
    ) {
        use std::sync::Mutex;
        let mutex =
            self.translation_drop_site_reasons_by_fn.get_or_init(|| Mutex::new(BTreeMap::new()));
        let mut guard = match mutex.lock() {
            Ok(g) => g,
            Err(poisoned) => poisoned.into_inner(),
        };
        let reasons = guard.entry(fn_name.to_owned()).or_default();
        *reasons.entry(reason.to_owned()).or_insert(0) += 1;
    }

    pub(in crate::codegen_ay) fn take_translation_drop_site_reasons_by_fn(
        &self,
    ) -> BTreeMap<String, BTreeMap<String, usize>> {
        use std::sync::Mutex;
        let mutex =
            self.translation_drop_site_reasons_by_fn.get_or_init(|| Mutex::new(BTreeMap::new()));
        let mut guard = match mutex.lock() {
            Ok(g) => g,
            Err(poisoned) => poisoned.into_inner(),
        };
        std::mem::take(&mut *guard)
    }

    pub(in crate::codegen_ay) fn get_translation_drop_site_reason_count_for_fn(
        &self,
        fn_name: &str,
        reason: &str,
    ) -> usize {
        use std::sync::Mutex;
        let mutex =
            self.translation_drop_site_reasons_by_fn.get_or_init(|| Mutex::new(BTreeMap::new()));
        let guard = match mutex.lock() {
            Ok(g) => g,
            Err(poisoned) => poisoned.into_inner(),
        };
        guard.get(fn_name).and_then(|reasons| reasons.get(reason)).copied().unwrap_or(0)
    }

    // --- Recursive unwind per-function map (Part of #4058) ---

    pub(in crate::codegen_ay) fn record_recursive_unwind_for_fn(
        &self,
        fn_name: &str,
        count: usize,
    ) {
        Self::record_for_fn(&self.recursive_unwind_by_fn, fn_name, count);
    }

    #[allow(dead_code)] // Call site wired in W1:4385 INCOMPLETE
    pub(in crate::codegen_ay) fn get_recursive_unwind_count_for_fn(&self, fn_name: &str) -> usize {
        Self::lock_map(&self.recursive_unwind_by_fn).get(fn_name).copied().unwrap_or(0)
    }

    // --- Inferable summary names per-function map (Part of #4031) ---

    pub(in crate::codegen_ay) fn record_inferable_summary_name_for_fn(
        &self,
        fn_name: &str,
        summary_name: &str,
    ) {
        use std::sync::Mutex;
        let mutex = self.inferable_summary_names_by_fn.get_or_init(|| Mutex::new(BTreeMap::new()));
        let mut guard = match mutex.lock() {
            Ok(g) => g,
            Err(poisoned) => poisoned.into_inner(),
        };
        let summaries = guard.entry(fn_name.to_owned()).or_default();
        *summaries.entry(summary_name.to_owned()).or_insert(0) += 1;
    }

    #[allow(dead_code)] // Reached via `chc` re-exports in metadata/tests.
    pub(in crate::codegen_ay) fn take_inferable_summary_names_by_fn(
        &self,
    ) -> BTreeMap<String, BTreeMap<String, usize>> {
        use std::sync::Mutex;
        let mutex = self.inferable_summary_names_by_fn.get_or_init(|| Mutex::new(BTreeMap::new()));
        let mut guard = match mutex.lock() {
            Ok(g) => g,
            Err(poisoned) => poisoned.into_inner(),
        };
        std::mem::take(&mut *guard)
    }

    // --- Aggregate gap reasons per-function map (Part of #4050) ---

    pub(in crate::codegen_ay) fn record_aggregate_gap_reason_for_fn(
        &self,
        fn_name: &str,
        reason: &str,
    ) {
        use std::sync::Mutex;
        let mutex = self.aggregate_gap_reasons_by_fn.get_or_init(|| Mutex::new(BTreeMap::new()));
        let mut guard = match mutex.lock() {
            Ok(g) => g,
            Err(poisoned) => poisoned.into_inner(),
        };
        let reasons = guard.entry(fn_name.to_owned()).or_default();
        *reasons.entry(reason.to_owned()).or_insert(0) += 1;
    }

    #[cfg(test)]
    pub(in crate::codegen_ay) fn take_aggregate_gap_reasons_by_fn(
        &self,
    ) -> BTreeMap<String, BTreeMap<String, usize>> {
        use std::sync::Mutex;
        let mutex = self.aggregate_gap_reasons_by_fn.get_or_init(|| Mutex::new(BTreeMap::new()));
        let mut guard = match mutex.lock() {
            Ok(g) => g,
            Err(poisoned) => poisoned.into_inner(),
        };
        std::mem::take(&mut *guard)
    }
}
