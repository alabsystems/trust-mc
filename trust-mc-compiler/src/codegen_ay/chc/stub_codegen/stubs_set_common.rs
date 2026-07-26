// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Shared CHC set helpers for BTreeSet/HashSet stubs.
//! Converted from include!() to proper module per #2595.
//!
//! Part of #2308: shared set operations (insert, contains, remove, len, is_empty, clear, clone).

use std::collections::HashSet;

use ay_bindings::{Expr, Sort};
use rustc_public::mir::Operand;
use tracing::error;

use super::codegen_expr_signedness::arg_signedness_or_fallback;
use super::types::{POINTER_WIDTH, SignExtension, bool_sort, coerce_bitvec_width_safe, ptr_sort};
use super::{ChcCtx, CollectionCallResult, chc_fresh_name, declare_pending_var};
use crate::codegen_ay::shared::SignednessFallbackKind;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Resolves a set argument that may be passed by reference or value.
    ///
    /// Shared by BTreeSet and HashSet CHC translators.
    /// Delegates to `get_collection_arg` which handles ref_targets resolution
    /// and modified_locals output-state preference with graceful fallback.
    pub(in crate::codegen_ay::chc) fn resolve_set_arg_from_ref(
        &mut self,
        operand: &Operand,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        self.get_collection_arg(operand, modified_locals)
    }

    /// Convert a key expression to match the expected array index sort.
    ///
    /// CHC collection encodings may carry key/index sorts that differ from
    /// operand key sorts at call sites (for example BV8 key against BV64 index).
    #[must_use]
    pub(in crate::codegen_ay::chc) fn convert_key_to_array_index(
        &self,
        key: Expr,
        index_sort: &Sort,
        key_is_signed: bool,
    ) -> Expr {
        let key_sort = key.sort();

        // If sorts match, no conversion needed
        if key_sort == index_sort {
            return key;
        }

        // Convert BitVec to Int if array index is Int.
        if key_sort.is_bitvec() && index_sort.is_int() {
            return if key_is_signed { key.bv2int_signed() } else { key.bv2int() };
        }

        // Convert Int to BitVec if array index is BitVec.
        if key_sort.is_int()
            && let Some(width) = index_sort.bitvec_width()
        {
            return key.int2bv(width);
        }

        // Coerce BitVec width to match array index width.
        if key_sort.is_bitvec()
            && let Some(width) = index_sort.bitvec_width()
        {
            return coerce_bitvec_width_safe(
                key,
                width,
                SignExtension::for_signedness(key_is_signed),
            );
        }

        // Other conversions could be added here if needed.
        // For now, return as-is and let the solver report the mismatch.
        key
    }

    /// Normalizes a raw key expression to the set's array index sort.
    #[must_use]
    fn normalize_set_key_for_array(
        &self,
        set_expr: &Expr,
        key_raw: Expr,
        key_is_signed: bool,
    ) -> Option<Expr> {
        let index_sort = set_expr.sort().array_sort()?.index_sort.clone();
        Some(self.convert_key_to_array_index(key_raw, &index_sort, key_is_signed))
    }

    /// Shared new() for set-like `Array<Key, Bool>` encodings.
    ///
    /// Creates an empty set (const_array(key_sort, false)).
    /// `len_update`: Some(0) for length-tracked sets, None for symbolic-only.
    pub(in crate::codegen_ay::chc) fn translate_set_new_common(
        &self,
        dest_local: Option<usize>,
        len_update: Option<Expr>,
    ) -> Option<CollectionCallResult> {
        let set_sort = dest_local
            .and_then(|dest| {
                let dest_idx = self.try_state_idx_for_local(dest)?;
                self.state_var_mgr.output_state_vars.get(dest_idx)
            })
            .map(|(_, sort)| sort.clone())?;

        let key_sort = set_sort.array_sort()?.index_sort.clone();
        let empty_set = Expr::const_array(key_sort, Expr::bool_const(false));

        Some(CollectionCallResult::new_collection(empty_set, len_update))
    }

    /// Shared clear() for set-like `Array<Key, Bool>` encodings.
    ///
    /// Creates a fresh empty set from the existing set's key sort.
    /// `len_update`: Some(0) for length-tracked sets, None for symbolic-only.
    pub(in crate::codegen_ay::chc) fn translate_set_clear_common(
        &mut self,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
        len_update: Option<Expr>,
    ) -> Option<CollectionCallResult> {
        let set_expr = self.resolve_set_arg_from_ref(args.first()?, modified_locals)?;
        let key_sort = set_expr.sort().array_sort()?.index_sort.clone();
        let cleared = Expr::const_array(key_sort, Expr::bool_const(false));

        Some(CollectionCallResult::clear(cleared, len_update))
    }

    /// Shared clone() for set-like `Array<Key, Bool>` encodings.
    ///
    /// Clone is identity in SMT — arrays are structural values.
    pub(in crate::codegen_ay::chc) fn translate_set_clone_common(
        &mut self,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
    ) -> Option<CollectionCallResult> {
        let set = self.resolve_set_arg_from_ref(args.first()?, modified_locals)?;
        Some(CollectionCallResult::read_only(set))
    }

    /// Shared insert skeleton for set-like `Array<Key, Bool>` encodings.
    fn translate_set_insert_common(
        &self,
        set_expr: Expr,
        key: Expr,
        present_value: Expr,
    ) -> CollectionCallResult {
        let was_present = set_expr.clone().select(key.clone());
        let new_set = set_expr.store(key, present_value);
        CollectionCallResult::mutating(new_set, was_present.not(), None)
    }

    /// Shared contains skeleton for set-like `Array<Key, Bool>` encodings.
    fn translate_set_contains_common(&self, set_expr: Expr, key: Expr) -> CollectionCallResult {
        CollectionCallResult::read_only(set_expr.select(key))
    }

    /// Shared remove skeleton for set-like `Array<Key, Bool>` encodings.
    fn translate_set_remove_common(
        &self,
        set_expr: Expr,
        key: Expr,
        absent_value: Expr,
    ) -> CollectionCallResult {
        let was_present = set_expr.clone().select(key.clone());
        let new_set = set_expr.store(key, absent_value);
        CollectionCallResult::mutating(new_set, was_present, None)
    }

    // =========================================================================
    // Higher-level shared set operations (Part of #2308)
    //
    // These handle the full flow: arg resolution → key normalization →
    // error handling → core operation → optional length tracking.
    // Both BTreeSet and HashSet CHC translators delegate to these.
    // =========================================================================

    /// Explicit fail-closed path for unexpected non-array set sort encodings.
    ///
    /// Returns a result that `apply_collection_result` turns into an `error()`
    /// rule rather than silently producing a dead transition.
    fn set_non_array_failure(
        &self,
        collection: &str,
        operation: &str,
        set_sort: &Sort,
    ) -> CollectionCallResult {
        error!(
            "UNSOUND: {collection}{operation} received non-array set sort {:?}; forcing failure",
            set_sort
        );
        CollectionCallResult::forced_failure()
    }

    /// Full insert flow for set-like collections.
    ///
    /// Resolves args, normalizes key, performs insert, and optionally tracks length.
    /// `track_len`: if true, computes `ite(was_absent, old_len + 1, old_len)`.
    pub(in crate::codegen_ay::chc) fn translate_set_insert_full(
        &mut self,
        collection_name: &str,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
        track_len: bool,
    ) -> Option<CollectionCallResult> {
        if args.len() < 2 {
            return None;
        }
        let set = self.resolve_set_arg_from_ref(&args[0], modified_locals)?;
        let key_raw = self.translate_operand_with_modified(&args[1], modified_locals)?;
        let key_is_signed = arg_signedness_or_fallback(
            &args[1],
            self.body.locals(),
            "translate_set_insert_full",
            SignednessFallbackKind::Comparison,
        );
        let key = match self.normalize_set_key_for_array(&set, key_raw, key_is_signed) {
            Some(key) => key,
            None => {
                return Some(self.set_non_array_failure(collection_name, "Insert", set.sort()));
            }
        };

        let mut result = self.translate_set_insert_common(set, key, Expr::bool_const(true));

        if track_len {
            let was_absent = result.result.clone();
            if let Some(was_absent) = was_absent {
                result.len_update =
                    self.get_collection_len_var(&args[0], modified_locals).map(|(_, old_len)| {
                        let one = Expr::bitvec_const(1u64, POINTER_WIDTH);
                        let new_len = old_len.clone().bvadd(one);
                        Expr::ite(was_absent, new_len, old_len)
                    });
            }
        }

        Some(result)
    }

    /// Full contains flow for set-like collections.
    ///
    /// Resolves args by reference, normalizes key, performs lookup.
    pub(in crate::codegen_ay::chc) fn translate_set_contains_full(
        &mut self,
        collection_name: &str,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
    ) -> Option<CollectionCallResult> {
        if args.len() < 2 {
            return None;
        }
        let set = self.resolve_set_arg_from_ref(&args[0], modified_locals)?;
        let key_raw = self.resolve_set_arg_from_ref(&args[1], modified_locals)?;
        let key_is_signed = arg_signedness_or_fallback(
            &args[1],
            self.body.locals(),
            "translate_set_contains_full",
            SignednessFallbackKind::Comparison,
        );
        let key = match self.normalize_set_key_for_array(&set, key_raw, key_is_signed) {
            Some(key) => key,
            None => {
                return Some(self.set_non_array_failure(collection_name, "Contains", set.sort()));
            }
        };
        Some(self.translate_set_contains_common(set, key))
    }

    /// Full remove flow for set-like collections.
    ///
    /// Resolves args by reference, normalizes key, performs remove,
    /// and optionally tracks length.
    /// `track_len`: if true, computes `ite(was_present, old_len - 1, old_len)`.
    pub(in crate::codegen_ay::chc) fn translate_set_remove_full(
        &mut self,
        collection_name: &str,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
        track_len: bool,
    ) -> Option<CollectionCallResult> {
        if args.len() < 2 {
            return None;
        }
        let set = self.resolve_set_arg_from_ref(&args[0], modified_locals)?;
        let key_raw = self.resolve_set_arg_from_ref(&args[1], modified_locals)?;
        let key_is_signed = arg_signedness_or_fallback(
            &args[1],
            self.body.locals(),
            "translate_set_remove_full",
            SignednessFallbackKind::Comparison,
        );
        let key = match self.normalize_set_key_for_array(&set, key_raw, key_is_signed) {
            Some(key) => key,
            None => {
                return Some(self.set_non_array_failure(collection_name, "Remove", set.sort()));
            }
        };

        let mut result = self.translate_set_remove_common(set, key, Expr::bool_const(false));

        if track_len {
            let was_present = result.result.clone();
            if let Some(was_present) = was_present {
                result.len_update =
                    self.get_collection_len_var(&args[0], modified_locals).map(|(_, old_len)| {
                        let one = Expr::bitvec_const(1u64, POINTER_WIDTH);
                        let new_len = old_len.clone().bvsub(one);
                        Expr::ite(was_present, new_len, old_len)
                    });
            }
        }

        Some(result)
    }

    /// Full len() flow for set-like collections.
    ///
    /// Uses tracked length if available, falls back to symbolic.
    pub(in crate::codegen_ay::chc) fn translate_set_len_full(
        &self,
        collection_name: &str,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
    ) -> Option<CollectionCallResult> {
        let result = self
            .get_collection_len_var(args.first()?, modified_locals)
            .map(|(_, len)| len)
            .unwrap_or_else(|| {
                // Part of #3447: Record that set length is unconstrained
                // (no tracked length variable for this collection).
                self.record_aggregate_gap("set_len_unconstrained");
                let mut prefix = String::with_capacity(collection_name.len() + 4);
                prefix.push_str(collection_name);
                prefix.push_str("_len");
                declare_pending_var(chc_fresh_name(&prefix), ptr_sort())
            });
        Some(CollectionCallResult::read_only(result))
    }

    /// Full is_empty() flow for set-like collections.
    ///
    /// Uses tracked length == 0 if available, falls back to symbolic.
    pub(in crate::codegen_ay::chc) fn translate_set_is_empty_full(
        &self,
        collection_name: &str,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
    ) -> Option<CollectionCallResult> {
        let result = self
            .get_collection_len_var(args.first()?, modified_locals)
            .map(|(_, len)| {
                let zero = Expr::bitvec_const(0u64, POINTER_WIDTH);
                len.eq(zero)
            })
            .unwrap_or_else(|| {
                // Part of #3447: Record that set is_empty is unconstrained
                // (no tracked length variable for this collection).
                self.record_aggregate_gap("set_is_empty_unconstrained");
                let mut prefix = String::with_capacity(collection_name.len() + 9);
                prefix.push_str(collection_name);
                prefix.push_str("_is_empty");
                declare_pending_var(chc_fresh_name(&prefix), bool_sort())
            });
        Some(CollectionCallResult::read_only(result))
    }
}
