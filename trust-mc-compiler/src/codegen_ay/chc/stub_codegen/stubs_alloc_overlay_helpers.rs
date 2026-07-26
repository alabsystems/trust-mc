// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Overlay helper functions for alloc/realloc bounded constraint generation.
// Extracted from stubs_alloc.rs per #3107 (500 LOC decomposition target).
use super::ChcCtx;
use ay_bindings::{Expr, ExprValue, Sort};

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    pub(in crate::codegen_ay::chc) fn copyable_elem_bytes(elem_sort: &Sort) -> Option<usize> {
        if let Some(width) = elem_sort.bitvec_width() {
            return Some(((width as usize).saturating_add(7) / 8).max(1));
        }
        elem_sort.is_bool().then_some(1)
    }

    pub(in crate::codegen_ay::chc) fn sorted_type_array_keys(&self) -> Vec<&str> {
        let mut keys: Vec<&str> =
            self.heap_state.type_arrays.keys().map(std::convert::AsRef::as_ref).collect();
        keys.sort_unstable();
        keys
    }

    pub(in crate::codegen_ay::chc) fn zero_value_for_sort(elem_sort: &Sort) -> Option<Expr> {
        if let Some(width) = elem_sort.bitvec_width() {
            return Some(Expr::bitvec_const(0, width));
        }
        elem_sort.is_bool().then_some(Expr::bool_const(false))
    }

    pub(in crate::codegen_ay::chc) fn should_overlay_type_array(
        type_key: &str,
        elem_sort: &Sort,
    ) -> bool {
        matches!(
            type_key,
            "bool"
                | "i8"
                | "u8"
                | "i16"
                | "u16"
                | "i32"
                | "u32"
                | "i64"
                | "u64"
                | "i128"
                | "u128"
                | "isize"
                | "usize"
        ) && (elem_sort.is_bool() || elem_sort.bitvec_width().is_some())
    }

    /// Part of #3685: Eagerly pre-create typed type arrays for standard BV sizes
    /// that fit within the allocation window. Called during `alloc_zeroed` zero-init
    /// so the zero stores are emitted to typed arrays (e.g., bv32 for i32) that may
    /// not exist yet. Without this, the zero-init loop only writes to existing arrays,
    /// and later typed loads create fresh unconstrained arrays.
    pub(in crate::codegen_ay::chc) fn seed_typed_arrays_for_zeroed_alloc(
        &mut self,
        effective_window: usize,
    ) {
        use super::types::ptr_sort;
        use tracing::debug;

        const SEED_TYPES: &[(&str, u32, usize)] = &[
            ("i8", 8, 1),
            ("u8", 8, 1),
            ("i16", 16, 2),
            ("u16", 16, 2),
            ("i32", 32, 4),
            ("u32", 32, 4),
            ("i64", 64, 8),
            ("u64", 64, 8),
        ];
        for &(type_key, bv_width, elem_bytes) in SEED_TYPES {
            if elem_bytes > effective_window {
                continue;
            }
            if self.heap_state.type_arrays.contains_key(type_key) {
                continue;
            }
            let elem_sort = Sort::bitvec(bv_width);
            let (arr_name, arr_out_name, declared_elem_sort, is_new) =
                self.heap_state.get_or_create_type_array(type_key, elem_sort, &self.fn_name);
            if is_new {
                let arr_sort = Sort::array(ptr_sort(), declared_elem_sort);
                self.push_late_state_var_pair(
                    std::sync::Arc::clone(&arr_name),
                    &arr_out_name,
                    arr_sort,
                );
                debug!(
                    type_key,
                    bv_width, "zero_init: pre-created typed array for zeroed allocation (#3685)"
                );
            }
        }
    }

    /// Fix #3677: Emit region array copy constraints for realloc moved-branch.
    ///
    /// Region arrays are indexed by full 64-bit split-pointer addresses. After
    /// `alias_region(old_id, new_id)`, both IDs share the same array variable,
    /// but `select(region, (new_id<<32)|off)` is a different key than where the
    /// original store wrote at `(old_id<<32)|off`. This method emits explicit
    /// copy constraints: `region_out[new_addr] = region_in[old_addr]` for each
    /// offset in the copy window, matching the type array copy pattern.
    ///
    /// Store chain key subtlety: `ptr.write(42)` accumulates its store chain
    /// under `region_key(old_obj_id)` (e.g., `"region_1"`). After aliasing, the
    /// new obj_id shares the same array variable name but has a different region
    /// key (`"region_2"`). We must look up the store chain under the OLD key to
    /// capture in-block stores that haven't been drained yet.
    pub(in crate::codegen_ay::chc) fn add_realloc_region_copy_constraints(
        &mut self,
        old_ptr: &Expr,
        new_ptr: &Expr,
        old_size: &Expr,
        concrete_old_size: Option<usize>,
        effective_window: usize,
        constraints: &mut Vec<Expr>,
    ) {
        use super::types::{POINTER_WIDTH, ptr_sort};
        use tracing::debug;

        let Some(new_obj_id) = Self::try_extract_obj_id(new_ptr) else { return };
        let old_obj_id = Self::try_extract_obj_id(old_ptr);

        // Fix #3677: source and destination region variables can diverge after
        // bv8->typed upgrades. The old allocation may already use a typed
        // region (source), while the new allocation may get its own typed
        // region declaration after realloc (destination). Copy from the old
        // region when available, but always constrain the NEW allocation's
        // output region so subsequent loads through the new pointer see the
        // copied value.
        let Some((source_region_in, _source_region_out, source_region_sort)) = old_obj_id
            .and_then(|oid| self.heap_state.get_region_array(oid))
            .or_else(|| self.heap_state.get_region_array(new_obj_id))
        else {
            return;
        };

        // Ensure the destination allocation has a region array with the same
        // sort as the source BEFORE we emit the moved-copy constraint. Without
        // this, later typed loads can create the destination region too late,
        // leaving the copied value disconnected from the post-realloc read.
        let destination_region = self
            .heap_state
            .get_region_array(new_obj_id)
            .filter(|(_, _, existing_sort)| *existing_sort == source_region_sort)
            .unwrap_or_else(|| {
                let (in_name, out_name) =
                    self.assign_region_array_to_relation(new_obj_id, source_region_sort.clone());
                (in_name, out_name.to_string(), source_region_sort.clone())
            });
        let (destination_region_in, destination_region_out, destination_region_sort) =
            destination_region;

        let Some(elem_bytes) = Self::copyable_elem_bytes(&source_region_sort) else {
            return;
        };
        if elem_bytes > effective_window {
            return;
        }

        let arr_sort = Sort::array(ptr_sort(), destination_region_sort);

        // Look up the store chain under the old region key first — the store
        // from ptr.write(42) was accumulated under region_key(old_obj_id), not
        // region_key(new_obj_id), because it happened before aliasing.
        let old_region_key = old_obj_id.map(crate::codegen_ay::names::region_key);
        let new_region_key = crate::codegen_ay::names::region_key(new_obj_id);

        let arr_in = old_region_key
            .as_deref()
            .and_then(|k| self.heap_state.get_store_chain(k))
            .or_else(|| self.heap_state.get_store_chain(&new_region_key))
            .cloned()
            .unwrap_or_else(|| Expr::var(&*source_region_in, arr_sort.clone()));
        let mut moved_arr = arr_in.clone();
        let mut touched = false;

        for byte_offset in (0..effective_window).step_by(elem_bytes) {
            let bytes_needed = byte_offset + elem_bytes;
            let off_expr = Expr::bitvec_const(byte_offset as i128, POINTER_WIDTH);
            let old_addr = old_ptr.clone().bvadd(off_expr.clone());
            let new_addr = new_ptr.clone().bvadd(off_expr);
            let old_value = arr_in.clone().select(old_addr);
            let next_value = if concrete_old_size.is_some_and(|s| bytes_needed <= s) {
                old_value
            } else {
                let can_copy =
                    Expr::bitvec_const(bytes_needed as i128, POINTER_WIDTH).bvule(old_size.clone());
                let keep_value = moved_arr.clone().select(new_addr.clone());
                Expr::ite(can_copy, old_value, keep_value)
            };
            moved_arr = moved_arr.store(new_addr, next_value);
            touched = true;
        }

        if touched {
            let arr_out = Expr::var(&*destination_region_out, arr_sort);
            constraints.push(arr_out.eq(moved_arr));
            self.heap_state.mark_array_modified(&new_region_key);
            if let Some(idx) = self.state_var_index_by_name(&destination_region_in) {
                self.mark_state_var_modified(idx);
            }
            debug!(new_obj_id, ?old_obj_id, "CHC: realloc region copy constraints emitted (#3677)");
        }
    }

    /// Try to extract a concrete `usize` from a bitvec constant expression.
    /// Returns `None` for symbolic (non-constant) expressions.
    /// Used to bound the overlay byte window when allocation size is known at codegen time.
    pub(in crate::codegen_ay::chc) fn try_extract_concrete_usize(expr: &Expr) -> Option<usize> {
        match expr.value() {
            ExprValue::BitVecConst { value, .. } => u64::try_from(value).ok().map(|v| v as usize),
            // Part of #3007: Handle BvExtract over a constant, which arises when
            // Layout is packed as BV128 and size is extracted via extract(127, 64, bv128).
            ExprValue::BvExtract { high, low, expr: inner } => {
                if let ExprValue::BitVecConst { value, .. } = inner.value() {
                    let shifted = value >> (*low as usize);
                    let width = high - low + 1;
                    let mask = (num_bigint::BigInt::from(1) << (width as usize)) - 1;
                    let extracted = shifted & mask;
                    u64::try_from(&extracted).ok().map(|v| v as usize)
                } else if let ExprValue::BvConcat(hi_expr, lo_expr) = inner.value() {
                    // Part of #3107: Handle BvExtract over BvConcat algebraically.
                    // Layout is encoded as concat(size:bv64, align:bv64). When the
                    // concat hasn't been folded through a Var yet (intra-block),
                    // extract the relevant half directly.
                    let lo_width = lo_expr.sort().bitvec_width().unwrap_or(0);
                    let hi_width = hi_expr.sort().bitvec_width().unwrap_or(0);
                    if *low >= lo_width && *high < lo_width + hi_width {
                        // Entirely within the high half — delegate to the high expr.
                        let shifted_low = low - lo_width;
                        let shifted_high = high - lo_width;
                        if shifted_low == 0 && shifted_high + 1 == hi_width {
                            // Full extraction of the high half.
                            Self::try_extract_concrete_usize(hi_expr)
                        } else {
                            None
                        }
                    } else if *high < lo_width {
                        // Entirely within the low half.
                        if *low == 0 && *high + 1 == lo_width {
                            Self::try_extract_concrete_usize(lo_expr)
                        } else {
                            None
                        }
                    } else {
                        None
                    }
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// Records a concrete heap allocation size when a size expression is known.
    pub(in crate::codegen_ay::chc) fn record_known_heap_alloc_size_expr(
        &mut self,
        obj_id: u32,
        size_expr: &Expr,
    ) {
        if let Some(size) =
            Self::try_extract_concrete_usize(size_expr).and_then(|size| u32::try_from(size).ok())
        {
            self.heap_state.record_heap_alloc_size(obj_id, size);
        }
    }
}
