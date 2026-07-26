// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Region array management for heap allocations and sort-to-suffix helper.
//!
//! Extracted from heap_state.rs per design D2 (file-decomposition-500loc-compliance).

use std::sync::Arc;

use ay_bindings::Sort;

use super::heap_state::ChcHeapState;
use crate::codegen_ay::types::bv8_sort;

impl ChcHeapState {
    /// Assigns a region array for a heap allocation (#1443).
    ///
    /// Per designs/archive/2026-02-01-heap-modeling-phase4.md: each heap allocation gets
    /// a disjoint region array. This preserves non-aliasing information for the
    /// SMT solver, reducing aliasing analysis burden.
    ///
    /// Returns (input_array_name, output_array_name) for the region.
    /// Names are `Arc<str>` for O(1) sharing across maps. Part of #2267 D3.
    ///
    /// # Contracts
    /// REQUIRES: obj_id is a valid allocation ID (typically from next_alloc_id())
    /// REQUIRES: elem_sort is a valid Sort for region element type
    /// REQUIRES: fn_name is non-empty (used for unique naming)
    /// ENSURES: result.0 (input name) is non-empty and unique across allocations
    /// ENSURES: result.1 (output name) == result.0 + "__out"
    /// ENSURES: region_arrays contains entry for obj_id after call
    /// ENSURES: idempotent - repeated calls with same obj_id return same names
    pub(in crate::codegen_ay::chc) fn assign_region_array(
        &mut self,
        obj_id: u32,
        elem_sort: Sort,
        fn_name: &str,
    ) -> (Arc<str>, String) {
        // Check if region already assigned
        if let Some((existing_name, existing_sort)) = self.region_arrays.get(&obj_id).cloned() {
            // Part of #1453: Allow upgrade from bv8 (raw bytes) to typed sort.
            // Allocations create bv8 regions, but typed stores should use typed regions.
            // If existing is bv8 and requested is typed, upgrade the region.
            let existing_is_bv8 = existing_sort.bitvec_width() == Some(8);
            let requested_is_typed = elem_sort != bv8_sort();

            if existing_sort == elem_sort {
                // Same sort - return existing
                let out_name = crate::codegen_ay::names::out_name(&existing_name);
                return (existing_name, out_name);
            } else if existing_is_bv8 && requested_is_typed {
                // Upgrade from bv8 to typed sort (#1453)
                // Remove old region and create new with typed sort
                self.region_arrays.remove(&obj_id);
                self.array_name_to_elem_sort.remove(existing_name.as_ref());

                let type_suffix = Self::sort_to_type_suffix(&elem_sort);
                let (arr_name, out_name) =
                    crate::codegen_ay::names::region_array_name_pair(fn_name, obj_id, &type_suffix);

                self.region_arrays.insert(obj_id, (Arc::clone(&arr_name), elem_sort.clone()));
                self.array_name_to_elem_sort.insert(Arc::clone(&arr_name), elem_sort);
                tracing::debug!(
                    obj_id,
                    old_name = %existing_name,
                    arr_name = %arr_name,
                    "CHC: upgraded region array from bv8 to typed sort (#1453)"
                );

                return (arr_name, out_name);
            } else if !existing_is_bv8 && !requested_is_typed {
                // Typed region already exists, BV8 requested (e.g., alloc stub
                // post-predeclaration). The typed sort is more precise than BV8 —
                // silently use the existing typed region. The alloc stub does not
                // depend on the region being BV8; it just uses BV8 as a default
                // because it doesn't know the element type at allocation time.
                tracing::debug!(
                    obj_id,
                    existing = ?existing_sort,
                    "CHC: region already typed, BV8 request silently absorbed"
                );
                let out_name = crate::codegen_ay::names::out_name(&existing_name);
                return (existing_name, out_name);
            }
            // Different non-bv8 sorts — warn and use existing (genuinely mismatched types)
            tracing::warn!(
                obj_id,
                existing = ?existing_sort,
                requested = ?elem_sort,
                "CHC: region array sort mismatch - using existing"
            );
            let out_name = crate::codegen_ay::names::out_name(&existing_name);
            return (existing_name, out_name);
        }

        // Create region array: region_<obj_id>_<type>
        // Type name is derived from sort for readability
        // Part of #2267: region_array_name_pair generates both names from one buffer.
        let type_suffix = Self::sort_to_type_suffix(&elem_sort);
        let (arr_name, out_name) =
            crate::codegen_ay::names::region_array_name_pair(fn_name, obj_id, &type_suffix);

        self.region_arrays.insert(obj_id, (Arc::clone(&arr_name), elem_sort.clone()));
        self.array_name_to_elem_sort.insert(Arc::clone(&arr_name), elem_sort.clone());

        tracing::debug!(
            obj_id,
            arr_name = %arr_name,
            "CHC: assigned region array for heap allocation"
        );

        (arr_name, out_name)
    }

    /// Aliases a new allocation's region to the most recent existing region.
    ///
    /// Used by realloc: the new allocation shares the old allocation's region
    /// array so that data written before realloc is visible through the new pointer.
    /// Finds the region with the highest obj_id less than new_obj_id (the most
    /// recent allocation before this realloc).
    /// Part of #1836: realloc data preservation.
    ///
    /// Returns true if aliasing succeeded (a prior region was found), false otherwise.
    pub(in crate::codegen_ay::chc) fn alias_most_recent_region(&mut self, new_obj_id: u32) -> bool {
        // Find the most recent region (highest obj_id < new_obj_id)
        let most_recent = self.region_arrays.keys().filter(|&&id| id < new_obj_id).max().copied();
        if let Some(old_obj_id) = most_recent
            && let Some((arr_name, sort)) = self.region_arrays.get(&old_obj_id).cloned()
        {
            tracing::debug!(
                new_obj_id,
                old_obj_id,
                arr_name = %arr_name,
                "CHC: realloc aliasing new region to old allocation's region"
            );
            self.region_arrays.insert(new_obj_id, (arr_name, sort));
            return true;
        }
        false
    }

    /// Alias the new allocation's region to a specific old allocation's region.
    ///
    /// Unlike `alias_most_recent_region` (which guesses via max(id < new)),
    /// this uses the exact old_obj_id from `split_pointer` on the realloc's
    /// old pointer argument. Fix for #2553.
    ///
    /// Returns true if aliasing succeeded (old region was found), false otherwise.
    pub(in crate::codegen_ay::chc) fn alias_region(
        &mut self,
        old_obj_id: u32,
        new_obj_id: u32,
    ) -> bool {
        if let Some((arr_name, sort)) = self.region_arrays.get(&old_obj_id).cloned() {
            tracing::debug!(
                old_obj_id,
                new_obj_id,
                arr_name = %arr_name,
                "CHC: realloc aliasing new region to old allocation's region (exact)"
            );
            self.region_arrays.insert(new_obj_id, (arr_name, sort));
            return true;
        }
        false
    }

    /// Gets the region array for a heap allocation, if one was assigned.
    ///
    /// Returns Some((input_name, output_name, elem_sort)) if a region was assigned.
    /// Part of #1443: Used by load_from_memory and build_memory_store for region-aware ops.
    ///
    /// # Contracts
    /// REQUIRES: obj_id is a valid allocation ID
    /// ENSURES: result.is_some() IFF region_arrays.contains_key(obj_id)
    /// ENSURES: result.some().0 matches the input name from assign_region_array
    /// ENSURES: result.some().1 == result.some().0 + "__out"
    /// ENSURES: result.some().2 matches the elem_sort from assign_region_array
    /// ENSURES: pure - does not modify region_arrays
    pub(in crate::codegen_ay::chc) fn get_region_array(
        &self,
        obj_id: u32,
    ) -> Option<(Arc<str>, String, Sort)> {
        self.region_arrays.get(&obj_id).map(|(arr_name, sort)| {
            let o = crate::codegen_ay::names::out_name(arr_name);
            (Arc::clone(arr_name), o, sort.clone())
        })
    }

    /// Converts a Sort to a short type suffix for array naming.
    ///
    /// # Contracts
    /// REQUIRES: sort is a valid Sort (any Sort variant is accepted)
    /// ENSURES: result is non-empty string
    /// ENSURES: result contains only alphanumeric chars or underscore (safe for identifiers)
    /// ENSURES: pure - no side effects
    /// ENSURES: deterministic - same sort always produces same suffix
    /// ENSURES: "bvN" for BitVec(N), "bool" for Bool, "int" for Int, "real" for Real
    /// ENSURES: "arr" for Array, sanitized name for Datatype, "unknown" for other sorts
    pub(in crate::codegen_ay::chc) fn sort_to_type_suffix(
        sort: &Sort,
    ) -> std::borrow::Cow<'static, str> {
        use std::borrow::Cow;
        if let Some(width) = sort.bitvec_width() {
            // Common widths use static strings to avoid heap allocation. Part of #2267.
            match width {
                8 => Cow::Borrowed("bv8"),
                16 => Cow::Borrowed("bv16"),
                32 => Cow::Borrowed("bv32"),
                64 => Cow::Borrowed("bv64"),
                128 => Cow::Borrowed("bv128"),
                _ => Cow::Owned(format!("bv{width}")), // non-enum: u32 width fallback
            }
        } else if sort.is_bool() {
            Cow::Borrowed("bool")
        } else if sort.is_int() {
            Cow::Borrowed("int")
        } else if sort.is_real() {
            // BigRational uses Real sort (#911)
            Cow::Borrowed("real")
        } else if sort.is_array() {
            // Array sorts used for memory regions (#1443)
            Cow::Borrowed("arr")
        } else if let Some(name) = sort.datatype_name() {
            // Sanitize datatype name for use in identifier
            let sanitized: String =
                name.chars().filter(|c| c.is_alphanumeric() || *c == '_').collect();
            // Fallback to "dt" if sanitization produces empty string
            if sanitized.is_empty() { Cow::Borrowed("dt") } else { Cow::Owned(sanitized) }
        } else {
            Cow::Borrowed("unknown")
        }
    }
}
