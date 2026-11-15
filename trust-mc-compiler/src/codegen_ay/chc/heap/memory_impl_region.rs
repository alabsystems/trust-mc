// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Region array load/store helpers for the CHC abstract heap model.
//!
//! Extracted from memory_impl.rs per #3053. Region arrays are per-allocation
//! typed arrays that preserve non-aliasing information that type-indexed arrays
//! lose. This module handles the region array lookup, bv8→typed upgrade, and
//! zeroed-allocation shortcut paths.

use std::sync::Arc;

use ay_bindings::{Expr, Sort};
use tracing::debug;

use super::ChcCtx;
use super::types::{bv8_sort, ptr_sort};

/// Pointer-indexed array sort: `(Array (_ BitVec POINTER_WIDTH) elem)`.
///
/// Replaces the repeated `Sort::array(ptr_sort(), elem)` pattern throughout
/// the heap model. Part of #3053.
#[inline]
pub(in crate::codegen_ay::chc) fn ptr_array_sort(elem: Sort) -> Sort {
    Sort::array(ptr_sort(), elem)
}

/// F4: a region read of an object after a store of another sort reached only
/// its type-indexed array. Not blessed: the read misses that store.
pub(in crate::codegen_ay::chc) const HEAP_REGION_STALE_AFTER_SUBSORT_STORE: &str =
    "heap_region_stale_after_subsort_store";

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// F4: record a read of `obj_id` answered from its region array, failing
    /// closed when a store of another sort already diverged it.
    fn note_region_read(&mut self, obj_id: u32) {
        self.heap_state.region_loaded_objs.insert(obj_id);
        if self.heap_state.region_diverged.contains(&obj_id) {
            debug!(
                obj_id,
                "CHC: region read after a sub-sort store to the type array — fail closed"
            );
            self.record_sound_fallback_reason(HEAP_REGION_STALE_AFTER_SUBSORT_STORE);
        }
    }

    /// F4: record that a store to `obj_id` reached only its type-indexed
    /// array. A region read of the object recorded earlier in encoding order
    /// fails closed here, since encoding order is not program order.
    fn note_region_divergence(&mut self, obj_id: u32) {
        self.heap_state.region_diverged.insert(obj_id);
        if self.heap_state.region_loaded_objs.contains(&obj_id) {
            debug!(obj_id, "CHC: sub-sort store after a region read of the object — fail closed");
            self.record_sound_fallback_reason(HEAP_REGION_STALE_AFTER_SUBSORT_STORE);
        }
    }

    /// F4 for a store whose address names no object: an interior-mutable
    /// write through a pointer the encoder holds only symbolically (the Cell
    /// lane's `&*b` receiver of a `Box<Cell<_>>`) reaches the type-indexed
    /// array alone, while a read of the same heap object at its constant
    /// address selects the object's region array and misses it: `b.set(200);
    /// let c = *b; assert!(c.get() < 100)` verified SUCCESSFUL clean. Every
    /// region object is marked diverged, so a region read of any of them, in
    /// either encoding order, fails closed.
    ///
    /// An address whose object half is a constant (`concat(obj, i * size)`,
    /// an element at a symbolic index) can only reach that object, so only it
    /// is marked.
    pub(in crate::codegen_ay::chc) fn note_symbolic_store_may_alias_regions(
        &mut self,
        addr: &Expr,
    ) {
        let obj = match addr.value() {
            ay_bindings::ExprValue::BvConcat(high, _) if high.sort().bitvec_width() == Some(32) => {
                match high.value() {
                    ay_bindings::ExprValue::BitVecConst { value, .. } => {
                        u32::try_from(value.clone()).ok()
                    }
                    _ => None,
                }
            }
            _ => None,
        };
        let objs: Vec<u32> = match obj {
            Some(obj) => vec![obj],
            None => self.heap_state.region_arrays.keys().copied().collect(),
        };
        for obj_id in objs {
            if self.heap_state.region_arrays.contains_key(&obj_id) {
                self.note_region_divergence(obj_id);
                self.note_object_view_store(obj_id, true);
            }
        }
    }

    /// Attempt to load from a region array for the given address.
    ///
    /// If the address contains an extractable obj_id with a matching or
    /// upgradeable region array, returns `Some(loaded_value)`. Otherwise
    /// returns `None` to fall through to the type-indexed array path.
    ///
    /// Part of #1443, #1446, #1453, #3685.
    pub(in crate::codegen_ay::chc) fn try_load_from_region(
        &mut self,
        addr: &Expr,
        elem_sort: &Sort,
        pointee_sort: Option<&Sort>,
        type_key: &str,
    ) -> Option<Expr> {
        let obj_id = Self::try_extract_obj_id(addr)?;
        let (region_in_arc, region_out, region_sort) = self.heap_state.get_region_array(obj_id)?;

        let region_is_bv8 = region_sort.bitvec_width() == Some(8);
        let needs_upgrade = region_is_bv8 && *elem_sort != bv8_sort();

        if needs_upgrade
            && self.heap_state.is_heap_obj_zeroed(obj_id)
            && !self.heap_state.write_used_type_arrays.contains_key(&region_in_arc)
            && let Some(zero_value) = Self::zero_value_for_sort(elem_sort)
        {
            debug!(
                obj_id,
                elem_sort = ?elem_sort,
                "CHC: load_from_memory - zeroed allocation typed load uses zero default (#3685)"
            );
            // F4 (docs/chc-hole-fix-designs-2026-09-24.md section 2): this
            // answer, like the region select below, misses a store of another
            // sort that went to the type array only (`try_store_to_region`).
            self.note_region_read(obj_id);
            self.note_view_read(addr, super::heap_view_ledger::REGION_VIEW_KEY, elem_sort, None);
            return Some(Self::coerce_loaded_value_for_pointee(zero_value, pointee_sort));
        }

        if needs_upgrade && self.heap_state.heap_obj_prefers_type_overlay(obj_id, type_key) {
            debug!(
                obj_id,
                type_key,
                elem_sort = ?elem_sort,
                "CHC: load_from_memory - preferring typed overlay for realloc-copied object (#3677)"
            );
            return None;
        }

        // Determine effective region params: upgrade bv8→typed, or use existing.
        let effective_region = if needs_upgrade {
            let (r_in, r_out) = self.assign_region_array_to_relation(obj_id, elem_sort.clone());
            Some((r_in, r_out, elem_sort.clone()))
        } else if region_sort == *elem_sort {
            let out_arc: Arc<str> = region_out.into();
            Some((region_in_arc, out_arc, region_sort.clone()))
        } else {
            None
        };

        if let Some((eff_in, eff_out, eff_sort)) = effective_region {
            let arr_sort = ptr_array_sort(eff_sort);
            let region_key = crate::codegen_ay::names::region_key(obj_id);
            let (arr_expr, region_label): (Expr, &str) =
                if let Some(accumulated) = self.heap_state.get_store_chain(&region_key) {
                    (accumulated.clone(), "<store_chain>")
                } else {
                    (Expr::var(&*eff_in, arr_sort), &eff_out)
                };
            let result = arr_expr.select(addr.clone());

            if needs_upgrade {
                debug!(
                    obj_id,
                    region = region_label,
                    elem_sort = ?elem_sort,
                    "CHC: load_from_memory - upgraded region from bv8 to typed (#1453)"
                );
            } else {
                debug!(
                    obj_id,
                    region = region_label,
                    "CHC: load_from_memory - region array select"
                );
            }

            self.heap_state.mark_type_array_read(&eff_in, self.current_encode_bb);
            self.note_region_read(obj_id);
            self.note_view_read(
                addr,
                super::heap_view_ledger::REGION_VIEW_KEY,
                elem_sort,
                Some(&result),
            );
            return Some(Self::coerce_loaded_value_for_pointee(result, pointee_sort));
        }

        // Different non-bv8 sorts — fall back to type array.
        debug!(
            obj_id,
            region_sort = ?region_sort,
            elem_sort = ?elem_sort,
            "CHC: load_from_memory - region sort mismatch, using type array (#1446)"
        );
        None
    }

    /// Attempt to store to a region array for the given address.
    ///
    /// If the address contains an extractable obj_id with a matching or
    /// upgradeable region array, writes to the region array. Always falls
    /// through to the type-indexed store path (Part of #3184: dual store).
    ///
    /// Part of #1443, #1446, #1453, #3184.
    pub(in crate::codegen_ay::chc) fn try_store_to_region(
        &mut self,
        addr: &Expr,
        value: &Expr,
        elem_sort: &Sort,
        signed: bool,
    ) {
        let Some(obj_id) = Self::try_extract_obj_id(addr) else { return };
        let Some((region_in, region_out, region_sort)) = self.heap_state.get_region_array(obj_id)
        else {
            return;
        };

        let region_is_bv8 = region_sort.bitvec_width() == Some(8);
        let needs_upgrade = region_is_bv8 && *elem_sort != bv8_sort();

        if !needs_upgrade && region_sort != *elem_sort {
            // F4: the TRUE mismatch branch (not the fall-through every region
            // store reaches): only the type-indexed array takes this store.
            self.note_region_divergence(obj_id);
            self.note_object_view_store(obj_id, true);
        } else {
            self.note_object_view_store(obj_id, false);
        }

        if needs_upgrade {
            let (eff_in, eff_out) = self.assign_region_array_to_relation(obj_id, elem_sort.clone());
            let region_state_idx = self.state_var_index_by_name(&eff_in);
            let arr_sort = ptr_array_sort(elem_sort.clone());
            let region_key = crate::codegen_ay::names::region_key(obj_id);
            // Reuse the accumulated store chain only if it already targets the
            // post-upgrade region sort. A bv8->typed upgrade replaces the region's
            // element sort, so a chain accumulated before the upgrade is nested over
            // the OLD byte-region base (`_bv8`) and has an incompatible, shallower
            // sort. Reusing it would tag a mis-nested store_expr with the NEW `_arr`
            // `__out` name, which drain_store_chains then drops as a sort mismatch —
            // leaving the region universally quantified and yielding a spurious
            // reachable CTREX. When the sorts diverge, start from the fresh region
            // input var so the store carries the exact value at the correct nesting.
            let arr_base = match self.heap_state.get_store_chain(&region_key) {
                Some(accumulated) if *accumulated.sort() == arr_sort => accumulated.clone(),
                _ => Expr::var(&*eff_in, arr_sort.clone()),
            };
            let coerced_value =
                Self::coerce_store_value(arr_base.sort(), value.clone(), signed, &self.diagnostics);
            let store_expr = arr_base.store(addr.clone(), coerced_value);

            debug!(
                obj_id,
                region = %eff_out,
                elem_sort = ?elem_sort,
                "CHC: build_memory_store - upgraded region from bv8 to typed (#1453)"
            );

            self.heap_state.accumulate_store(&region_key, eff_out, store_expr);
            self.heap_state.mark_array_modified(&region_key);
            self.heap_state.mark_type_array_written(&eff_in, self.current_encode_bb);
            if let Some(idx) = region_state_idx {
                self.mark_state_var_modified(idx);
            }
            self.note_view_write(addr, value, super::heap_view_ledger::REGION_VIEW_KEY, elem_sort);
        } else if region_sort == *elem_sort {
            let region_state_idx = self.state_var_index_by_name(&region_in);
            let arr_sort = ptr_array_sort(region_sort.clone());
            let region_key = crate::codegen_ay::names::region_key(obj_id);
            // See the needs_upgrade branch: only reuse an accumulated chain whose sort
            // matches this region's array sort; otherwise a stale (mis-nested) chain
            // would be tagged with this region's `__out` name and dropped at drain.
            let arr_base = match self.heap_state.get_store_chain(&region_key) {
                Some(accumulated) if *accumulated.sort() == arr_sort => accumulated.clone(),
                _ => Expr::var(&*region_in, arr_sort.clone()),
            };
            let coerced_value =
                Self::coerce_store_value(arr_base.sort(), value.clone(), signed, &self.diagnostics);
            let store_expr = arr_base.store(addr.clone(), coerced_value);

            debug!(
                obj_id,
                region = %region_out,
                "CHC: build_memory_store - region array store (accumulated, #1447)"
            );

            self.heap_state.accumulate_store(&region_key, region_out, store_expr);
            self.heap_state.mark_array_modified(&region_key);
            self.heap_state.mark_type_array_written(&region_in, self.current_encode_bb);
            if let Some(idx) = region_state_idx {
                self.mark_state_var_modified(idx);
            }
            self.note_view_write(addr, value, super::heap_view_ledger::REGION_VIEW_KEY, elem_sort);
        }

        // Different non-bv8 sorts — fall back to type array.
        debug!(
            obj_id,
            region_sort = ?region_sort,
            elem_sort = ?elem_sort,
            "CHC: build_memory_store - region sort mismatch, using type array (#1446)"
        );
        // Always fall through to type-indexed store (Part of #3184)
    }
}
