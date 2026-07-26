// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Pointer-wrapper alias mirroring for CHC type-indexed memory stores.
//!
//! Part of #2912: keeps `ptr_T` and transparent wrappers (`NonNull<T>`,
//! `Unique<T>`) in sync so casted pointer reinterpretation does not read
//! unconstrained memory arrays.
//!
//! Extracted from memory_impl.rs per 500-LOC file size limit.

use std::sync::Arc;
use std::sync::atomic::Ordering;

use ay_bindings::{Expr, Sort};
use tracing::{debug, warn};

use super::types::ptr_sort;
use super::{ChcCtx, UNDEF_COUNTER, declare_pending_var};

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Return transparent pointer-wrapper alias keys for a primary type key.
    ///
    /// Keeps `ptr_T` and transparent wrappers (`NonNull<T>`, `Unique<T>`) in
    /// sync for type-indexed memory stores so casted pointer reinterpretation
    /// does not read unconstrained arrays.
    pub(in crate::codegen_ay::chc) fn pointer_wrapper_alias_keys(
        &self,
        type_key: &str,
    ) -> Vec<Arc<str>> {
        if let Some(inner) = type_key.strip_prefix("ptr_") {
            if inner.starts_with("ptr_")
                || inner.contains("NonNull_")
                || inner.contains("Unique_")
                || inner.starts_with("ref_")
            {
                return Vec::new();
            }
            let mut nonnull_suffix = String::with_capacity(9 + inner.len());
            nonnull_suffix.push_str("NonNull_");
            nonnull_suffix.push_str(inner);
            let mut unique_suffix = String::with_capacity(8 + inner.len());
            unique_suffix.push_str("Unique_");
            unique_suffix.push_str(inner);
            // Clone Arc<str> keys (O(1) atomic increment) instead of allocating new
            // Strings via .to_string(). Part of #2267.
            let mut aliases: Vec<Arc<str>> = self
                .heap_state
                .type_arrays
                .keys()
                .filter_map(|k| {
                    let key: &str = k;
                    if key.ends_with(&nonnull_suffix) || key.ends_with(&unique_suffix) {
                        Some(Arc::clone(k))
                    } else {
                        None
                    }
                })
                .collect();
            if !aliases.iter().any(|k| k.ends_with(&nonnull_suffix)) {
                let mut s = String::with_capacity(17 + inner.len());
                s.push_str("std_ptr_NonNull_");
                s.push_str(inner);
                aliases.push(Arc::from(s));
            }
            if !aliases.iter().any(|k| k.ends_with(&unique_suffix)) {
                let mut s = String::with_capacity(16 + inner.len());
                s.push_str("std_ptr_Unique_");
                s.push_str(inner);
                aliases.push(Arc::from(s));
            }
            return aliases;
        }
        if let Some((_, inner)) = type_key.rsplit_once("NonNull_") {
            let mut s = String::with_capacity(4 + inner.len());
            s.push_str("ptr_");
            s.push_str(inner);
            return vec![Arc::from(s)];
        }
        if let Some((_, inner)) = type_key.rsplit_once("Unique_") {
            let mut s = String::with_capacity(4 + inner.len());
            s.push_str("ptr_");
            s.push_str(inner);
            return vec![Arc::from(s)];
        }
        Vec::new()
    }

    /// Mirror a type-indexed store into pointer-wrapper alias arrays.
    ///
    /// Part of #2912: reads that reinterpret `*const T` bytes as `NonNull<T>`
    /// must observe the same symbolic memory cell.
    pub(in crate::codegen_ay::chc) fn mirror_pointer_wrapper_store_aliases(
        &mut self,
        addr: &Expr,
        value: &Expr,
        type_key: &str,
        elem_sort_hint: &Sort,
        signed: bool,
    ) {
        for alias_key in self.pointer_wrapper_alias_keys(type_key) {
            if *alias_key == *type_key {
                continue;
            }

            let (arr_name, arr_out_name, declared_elem_sort, is_new) = self
                .heap_state
                .get_or_create_type_array(&alias_key, elem_sort_hint.clone(), &self.fn_name);
            // Part of #3184: Mark alias array as written in a pointer alias store.
            // These are write-only unless explicitly read elsewhere.
            self.heap_state.mark_type_array_written(&arr_name, self.current_encode_bb);
            let arr_sort = Sort::array(ptr_sort(), declared_elem_sort.clone());
            // Part of #2970: register late-created alias arrays as state variable pairs.
            if is_new {
                self.push_late_state_var_pair(
                    Arc::clone(&arr_name),
                    &arr_out_name,
                    arr_sort.clone(),
                );
            }
            // Resolve CURRENT (possibly fragment-mid-renamed) names so composed
            // fragments don't double-bind the final `__out` variable.
            let (cur_in_name, cur_out_name, _) =
                self.current_array_state_names(&arr_name, &arr_out_name);
            let arr_base = if let Some(accumulated) = self.heap_state.get_store_chain(&alias_key) {
                accumulated.clone()
            } else {
                Expr::var(&*cur_in_name, arr_sort)
            };
            let value =
                Self::coerce_store_value(arr_base.sort(), value.clone(), signed, &self.diagnostics);
            let Some(array_sort) = arr_base.sort().array_sort() else {
                warn!(
                    alias_key = %alias_key,
                    "CHC: skipped pointer-wrapper alias store - base expression is not an array"
                );
                continue;
            };
            let expected_elem_sort = &array_sort.element_sort;
            let value = if value.sort() != expected_elem_sort {
                self.record_aggregate_gap("memory_ptr_alias_store_sort_mismatch");
                let sym_id = UNDEF_COUNTER.fetch_add(1, Ordering::Relaxed);
                let sym_name = crate::codegen_ay::names::store_coerce_name(&alias_key, sym_id);
                declare_pending_var(sym_name, expected_elem_sort.clone())
            } else {
                value
            };
            let store_expr = arr_base.store(addr.clone(), value);
            self.heap_state.accumulate_store(&alias_key, cur_out_name, store_expr);
            self.heap_state.mark_array_modified(&alias_key);

            // Re-lookup after potential registration above (#2967).
            if let Some(idx) = self.state_var_index_by_name(&arr_name) {
                self.mark_state_var_modified(idx);
            }

            debug!(
                type_key = %type_key,
                alias_key = %alias_key,
                "CHC: mirrored type-indexed store into pointer-wrapper alias"
            );
        }
    }
}
