// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CHC abstract heap model: memory load/store, region arrays, object ID extraction.
//!
//! Decomposed from codegen.rs per #1353/#2246. Address translation, layout helpers,
//! and type key mapping are in memory_impl_addr.rs, memory_impl_layout.rs,
//! memory_impl_type_keys.rs respectively. Region array load/store helpers are
//! in memory_impl_region.rs per #3053.

use std::borrow::Cow;
use std::sync::Arc;
use std::sync::atomic::Ordering;

use ay_bindings::{Expr, Sort};
use tracing::{debug, warn};

use super::codegen_ctx::diagnostics::CellCounter;
use super::codegen_types::CodegenTypes;
use super::memory_impl_region::ptr_array_sort;
use super::types::{POINTER_WIDTH, SignExtension, coerce_bitvec_width_safe};
use super::{ChcCtx, UNDEF_COUNTER, declare_pending_var, dyn_coercion};
use crate::codegen_ay::chc::call::canonical_zst_expr_for_sort;
use crate::codegen_ay::chc::call::codegen_call_kani_model_dst::is_zst_ty;
use crate::codegen_ay::shared::ty_signedness_shallow;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    // =========================================================================
    // Phase 3: Memory load/store operations (Part of #892)
    // =========================================================================
    // Object ID extraction + load coercion moved to memory_impl_addr.rs per #3199.

    /// Normalize a type's dyn-trait tail to its unique concrete implementation.
    ///
    /// Delegates to `dyn_coercion::normalize_unique_dyn_tail_ty` — the single
    /// source of truth for dyn-tail normalization policy (Part of #3975).
    pub(in crate::codegen_ay::chc) fn normalize_unique_dyn_tail_ty(
        &self,
        ty: rustc_public::ty::Ty,
    ) -> rustc_public::ty::Ty {
        dyn_coercion::normalize_unique_dyn_tail_ty(self, ty)
    }

    /// Loads a value from memory at the given address.
    ///
    /// Uses region arrays for heap allocations when the obj_id can be statically
    /// determined, falling back to type-indexed arrays otherwise.
    ///
    /// Part of #1443: Region-aware memory operations.
    pub(in crate::codegen_ay::chc) fn load_from_memory(
        &mut self,
        addr: Expr,
        pointee_ty: rustc_public::ty::Ty,
    ) -> Option<Expr> {
        let pointee_ty = self.resolve_body_ty(pointee_ty);
        // BigInt uses value semantics - the address IS the value (#545 audit)
        if Self::type_name_contains_bigint(&pointee_ty) {
            debug!(
                ty = ?pointee_ty,
                "CHC: load_from_memory - BigInt uses value semantics, returning addr"
            );
            return Some(addr);
        }

        // Part of #2875: Coerce Int addresses to BV before pointer arithmetic.
        let addr = if addr.sort().is_int() { addr.int2bv(POINTER_WIDTH) } else { addr };
        let addr = coerce_bitvec_width_safe(addr, POINTER_WIDTH, SignExtension::ZeroExtend);
        if addr.sort().bitvec_width().is_none() {
            warn!(?addr, "CHC: load_from_memory address is not a bitvec");
            return None;
        }

        // Record heap validity/bounds checks for this deref.
        let checks = self.heap_access_checks(addr.clone(), pointee_ty);
        if !checks.is_empty() {
            self.mark_heap_metadata_read();
        }
        self.heap_state.pending_checks.extend(checks);

        // Part of #3974: Normalize dyn-tail types so loads use the same
        // type key as the corresponding Box::new / alloc stores.
        // Guard: skip normalization when it would change the translate_ty sort
        // (e.g., Box<dyn Trait> BV128 → Box<Concrete> BV64 loses vtable metadata).
        let normalized_ty = self.normalize_unique_dyn_tail_ty(pointee_ty);
        let pointee_ty = if normalized_ty != pointee_ty
            && Self::translate_ty(normalized_ty) != Self::translate_ty(pointee_ty)
        {
            pointee_ty
        } else {
            normalized_ty
        };

        let type_key = self.type_key_for_body_ty(pointee_ty);
        let elem_sort = self.elem_sort_for_memory_array(pointee_ty);
        let pointee_sort = Self::translate_ty(pointee_ty);

        if is_zst_ty(pointee_ty)
            && let Some(sort) = pointee_sort.as_ref()
            && let Some(canonical) = canonical_zst_expr_for_sort(pointee_ty, sort)
        {
            debug!(
                ty = ?pointee_ty,
                sort = ?sort,
                "CHC: load_from_memory - canonical ZST value"
            );
            return Some(canonical);
        }

        // Part of #3608: Compile-time store-to-load forwarding.
        if let Some((fwd_obj_id, fwd_offset)) = Self::try_extract_constant_addr(&addr) {
            let fwd_key = ((fwd_obj_id as u64) << 32) | (fwd_offset as u64);
            if let Some((store_bb, forwarded_value)) =
                self.heap_state.store_forward_map.get(&fwd_key).cloned()
                && store_bb == self.current_encode_bb
            {
                debug!(
                    obj_id = fwd_obj_id,
                    offset = fwd_offset,
                    "CHC: load_from_memory - store-to-load forwarding (#3608)"
                );
                return Some(Self::coerce_loaded_value_for_pointee(
                    forwarded_value,
                    pointee_sort.as_ref(),
                ));
            }
        }

        // Part of #1443: Try region array first for heap allocations.
        // Part of #4099: Skip region shortcut when pointee is [T; N] and elem_sort
        // is scalar T. The region stores flat T elements via per-element decomposition,
        // so a single select(addr) returns one T, not the full Array(BV64, T). Fall
        // through to the multi-element reconstruction path below.
        let needs_array_reconstruction =
            pointee_sort.as_ref().is_some_and(|ps| ps.is_array()) && !elem_sort.is_array();
        if !needs_array_reconstruction {
            if let Some(result) = self.try_load_from_region(
                &addr,
                &elem_sort,
                pointee_sort.as_ref(),
                type_key.as_ref(),
            ) {
                return Some(result);
            }
        }

        // Part of #4086: For SIMD ADT types (e.g., i64x2) whose translate_ty is
        // Array(BV64, BV64) but whose typed heap stores flat BV64 elements, load
        // all N elements from consecutive addresses and reconstruct the full array.
        if let Some(ref ps) = pointee_sort
            && ps.is_array()
            && let Some(array_len) = self.get_array_length(pointee_ty)
            && array_len > 0
            && let Some(elem_size) =
                self.get_array_element_ty(pointee_ty).and_then(|et| self.get_type_size(et))
            && elem_size > 0
            && array_len <= 64
        {
            let arr = ps.array_sort().expect("invariant: pending store must have array sort");
            let default_elem = if arr.element_sort.is_bool() {
                Expr::bool_const(false)
            } else {
                Expr::bitvec_const(0u64, arr.element_sort.bitvec_width().unwrap_or(64))
            };
            let mut result = Expr::const_array(arr.index_sort.clone(), default_elem);
            let idx_width = arr.index_sort.bitvec_width().unwrap_or(POINTER_WIDTH);
            for i in 0..array_len {
                let elem_addr = if i == 0 {
                    addr.clone()
                } else {
                    addr.clone().bvadd(Expr::bitvec_const((i * elem_size) as u128, POINTER_WIDTH))
                };
                let raw =
                    self.load_from_type_array(elem_addr, &type_key, elem_sort.clone(), None)?;
                let idx = Expr::bitvec_const(i as u128, idx_width);
                result = result.store(idx, raw);
            }
            debug!(
                array_len,
                elem_size,
                "CHC: load_from_memory - reconstructed multi-element array from flat memory (#4086)"
            );
            return Some(result);
        }

        // Fallback: use type-indexed array partitioning.
        self.load_from_type_array(addr, &type_key, elem_sort, pointee_sort.as_ref())
    }

    /// Type-indexed array load fallback.
    pub(in crate::codegen_ay::chc) fn load_from_type_array(
        &mut self,
        addr: Expr,
        type_key: &str,
        elem_sort: Sort,
        pointee_sort: Option<&Sort>,
    ) -> Option<Expr> {
        if self.should_stub_spawn_type_array(type_key) {
            let sym_name = format!(
                "__spawn_stub_load_{}_{}",
                type_key,
                UNDEF_COUNTER.fetch_add(1, Ordering::Relaxed)
            );
            let fresh = declare_pending_var(sym_name, elem_sort);
            self.record_sound_fallback_reason("spawn_type_array_load_stub");
            return Some(Self::coerce_loaded_value_for_pointee(fresh, pointee_sort));
        }

        let (arr_name, arr_out_name, declared_elem_sort, is_new) =
            self.heap_state.get_or_create_type_array(type_key, elem_sort.clone(), &self.fn_name);
        self.heap_state.mark_type_array_read(&arr_name, self.current_encode_bb);
        if is_new {
            let arr_sort = ptr_array_sort(declared_elem_sort.clone());
            self.push_late_state_var_pair(Arc::clone(&arr_name), &arr_out_name, arr_sort);
        }

        // Read through the CURRENT (possibly fragment-mid-renamed) input name.
        let (cur_in_name, _, _) = self.current_array_state_names(&arr_name, &arr_out_name);

        let arr_sort = ptr_array_sort(declared_elem_sort.clone());
        let (arr_expr, use_arr_name): (Expr, Cow<'_, str>) =
            if let Some(accumulated) = self.heap_state.get_store_chain(type_key) {
                (accumulated.clone(), Cow::Borrowed("<store_chain>"))
            } else {
                (Expr::var(&*cur_in_name, arr_sort), Cow::Borrowed(type_key))
            };
        let result = arr_expr.select(addr);

        debug!(
            type_key = %type_key,
            requested_elem_sort = ?elem_sort,
            declared_elem_sort = ?declared_elem_sort,
            modified = self.heap_state.is_array_modified(type_key),
            source = %use_arr_name,
            "CHC: load_from_memory - type-indexed select (fallback)"
        );

        Some(Self::coerce_loaded_value_for_pointee(result, pointee_sort))
    }

    /// Replace a dropped memory-store target with a fresh symbolic array.
    ///
    /// This keeps subsequent same-block loads off the stale input array and
    /// makes the eventual output universally quantified instead of identity-copied.
    #[allow(dead_code)]
    pub(in crate::codegen_ay::chc) fn overapproximate_memory_store_target(
        &mut self,
        pointee_ty: rustc_public::ty::Ty,
        addr: Option<&Expr>,
    ) {
        let pointee_ty = self.resolve_body_ty(pointee_ty);
        let elem_sort = self.elem_sort_for_memory_array(pointee_ty);

        if let Some(addr) = addr
            && let Some(obj_id) = Self::try_extract_obj_id(addr)
            && let Some((region_in, region_out, region_sort)) =
                self.heap_state.get_region_array(obj_id)
        {
            let region_is_bv8 = region_sort.bitvec_width() == Some(8);
            let needs_upgrade = region_is_bv8 && elem_sort != super::types::bv8_sort();
            if needs_upgrade {
                let (eff_in, eff_out) =
                    self.assign_region_array_to_relation(obj_id, elem_sort.clone());
                let sym_name = format!(
                    "__store_drop_region_{obj_id}_{}",
                    UNDEF_COUNTER.fetch_add(1, Ordering::Relaxed)
                );
                let region_key = crate::codegen_ay::names::region_key(obj_id);
                let arr_sort = ptr_array_sort(elem_sort.clone());
                let fresh = declare_pending_var(sym_name, arr_sort);
                self.heap_state.accumulate_store(&region_key, eff_out, fresh);
                self.heap_state.mark_array_modified(&region_key);
                self.heap_state.mark_type_array_written(&eff_in, self.current_encode_bb);
                if let Some(idx) = self.state_var_index_by_name(&eff_in) {
                    self.mark_state_var_modified(idx);
                }
            } else if region_sort == elem_sort {
                let sym_name = format!(
                    "__store_drop_region_{obj_id}_{}",
                    UNDEF_COUNTER.fetch_add(1, Ordering::Relaxed)
                );
                let region_key = crate::codegen_ay::names::region_key(obj_id);
                let arr_sort = ptr_array_sort(region_sort);
                let fresh = declare_pending_var(sym_name, arr_sort);
                self.heap_state.accumulate_store(&region_key, region_out, fresh);
                self.heap_state.mark_array_modified(&region_key);
                self.heap_state.mark_type_array_written(&region_in, self.current_encode_bb);
                if let Some(idx) = self.state_var_index_by_name(&region_in) {
                    self.mark_state_var_modified(idx);
                }
            }
        }

        let type_key = self.type_key_for_body_ty(pointee_ty);
        let (arr_name, arr_out_name, declared_elem_sort, is_new) =
            self.heap_state.get_or_create_type_array(&type_key, elem_sort, &self.fn_name);
        self.heap_state.mark_type_array_written(&arr_name, self.current_encode_bb);
        if is_new {
            let arr_sort = ptr_array_sort(declared_elem_sort.clone());
            self.push_late_state_var_pair(Arc::clone(&arr_name), &arr_out_name, arr_sort);
        }
        let sym_name = format!(
            "__store_drop_mem_{}_{}",
            type_key,
            UNDEF_COUNTER.fetch_add(1, Ordering::Relaxed)
        );
        let arr_sort = ptr_array_sort(declared_elem_sort);
        let fresh = declare_pending_var(sym_name, arr_sort);
        let (_, cur_out_name, state_idx) = self.current_array_state_names(&arr_name, &arr_out_name);
        self.heap_state.accumulate_store(&type_key, cur_out_name, fresh);
        self.heap_state.mark_array_modified(&type_key);
        if let Some(idx) = state_idx {
            self.mark_state_var_modified(idx);
        }
    }

    /// Builds a memory store constraint.
    ///
    /// Returns None — constraint will be emitted by drain_store_chains() at block end.
    ///
    /// Uses region arrays for heap allocations when the obj_id can be statically
    /// determined, falling back to type-indexed arrays otherwise.
    ///
    /// Part of #1443: Region-aware memory operations.
    pub(in crate::codegen_ay::chc) fn build_memory_store(
        &mut self,
        addr: Expr,
        value: Expr,
        pointee_ty: rustc_public::ty::Ty,
    ) -> Option<Expr> {
        let pointee_ty = self.resolve_body_ty(pointee_ty);
        let signed = ty_signedness_shallow(pointee_ty).unwrap_or(false);
        // Part of #2875: Coerce Int addresses to BV before pointer arithmetic.
        let addr = if addr.sort().is_int() { addr.int2bv(POINTER_WIDTH) } else { addr };
        let addr = coerce_bitvec_width_safe(addr, POINTER_WIDTH, SignExtension::ZeroExtend);
        if addr.sort().bitvec_width().is_none() {
            warn!(?addr, "CHC: build_memory_store address is not a bitvec");
            return None;
        }

        if !self.suppress_heap_store_checks {
            let checks = self.heap_access_checks(addr.clone(), pointee_ty);
            if !checks.is_empty() {
                self.mark_heap_metadata_read();
            }
            self.heap_state.pending_checks.extend(checks);
        }

        let type_key = self.type_key_for_body_ty(pointee_ty);
        let elem_sort = self.elem_sort_for_memory_array(pointee_ty);

        if is_zst_ty(pointee_ty) {
            debug!(
                type_key = %type_key,
                ty = ?pointee_ty,
                "CHC: build_memory_store - skipped ZST store"
            );
            return None;
        }

        // FC-06: modifies frame-condition check. Stores executed inside a
        // contract-checked function's extent must target the declared
        // footprint. Fresh-allocation stores (suppress_heap_store_checks,
        // e.g. Box::new initialization) are exempt per DFCC freshness.
        if !self.suppress_heap_store_checks {
            self.modifies_frame_store_check(&addr, pointee_ty);
        }

        // Part of #4099: Decompose [T; N] array stores into N per-element stores.
        // elem_sort_for_memory_array unwraps Array(BV64, T) -> T (#4152), so when
        // the value has Array sort but elem_sort is scalar T, the value would be
        // replaced by an unconstrained symbolic in coerce_store_value (data lost).
        // Instead, extract each element via AY select and store at consecutive
        // byte addresses. The load side (#4086 reconstruction) rebuilds the array.
        let is_plain_array = matches!(
            pointee_ty.kind(),
            rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::Array(..))
        );
        if is_plain_array
            && value.sort().is_array()
            && !elem_sort.is_array()
            && let Some(array_len) = self.get_array_length(pointee_ty)
            && array_len > 0
            && array_len <= 64
            && let Some(elem_size) =
                self.get_array_element_ty(pointee_ty).and_then(|et| self.get_type_size(et))
            && elem_size > 0
        {
            for i in 0..array_len {
                let idx = Expr::bitvec_const(i as u128, POINTER_WIDTH);
                let elem_val = value.clone().select(idx);
                let elem_addr = if i == 0 {
                    addr.clone()
                } else {
                    addr.clone().bvadd(Expr::bitvec_const((i * elem_size) as u128, POINTER_WIDTH))
                };
                self.try_store_to_region(&elem_addr, &elem_val, &elem_sort, signed);
                self.store_to_type_array(elem_addr, elem_val, &type_key, elem_sort.clone(), signed);
            }
            debug!(
                array_len,
                elem_size,
                type_key = %type_key,
                "CHC: build_memory_store - decomposed [T; N] into per-element stores (Part of #4099)"
            );
            return None;
        }

        // Part of #1443: Try region array first (always falls through to type store).
        self.try_store_to_region(&addr, &value, &elem_sort, signed);

        // Fallback: type-indexed array store.
        self.store_to_type_array(addr, value, &type_key, elem_sort, signed)
    }

    /// Type-indexed array store with coercion, forwarding, and alias mirroring.
    pub(in crate::codegen_ay::chc) fn store_to_type_array(
        &mut self,
        addr: Expr,
        value: Expr,
        type_key: &str,
        elem_sort: Sort,
        signed: bool,
    ) -> Option<Expr> {
        if self.should_stub_spawn_type_array(type_key) {
            self.record_sound_fallback_reason("spawn_type_array_store_stub");
            return None;
        }

        let (arr_name, arr_out_name, declared_elem_sort, is_new) =
            self.heap_state.get_or_create_type_array(type_key, elem_sort, &self.fn_name);
        self.heap_state.mark_type_array_written(&arr_name, self.current_encode_bb);
        if is_new {
            let arr_sort = ptr_array_sort(declared_elem_sort.clone());
            self.push_late_state_var_pair(Arc::clone(&arr_name), &arr_out_name, arr_sort);
        }

        // Resolve the CURRENT (possibly fragment-mid-renamed) variable names;
        // binding the original `__out` name from a non-last composed block
        // yields contradictory duplicate bindings (see current_array_state_names).
        let (cur_in_name, cur_out_name, type_arr_state_idx) =
            self.current_array_state_names(&arr_name, &arr_out_name);

        let arr_sort = ptr_array_sort(declared_elem_sort.clone());
        let arr_base = if let Some(accumulated) = self.heap_state.get_store_chain(type_key) {
            accumulated.clone()
        } else {
            Expr::var(&*cur_in_name, arr_sort)
        };

        let value = Self::coerce_store_value(arr_base.sort(), value, signed, &self.diagnostics);
        let Some(array_sort) = arr_base.sort().array_sort() else {
            warn!(
                type_key = %type_key,
                "CHC: dropped type-indexed store - base expression is not an array (Part of #2244)"
            );
            self.diagnostics.store_dropped_transition.inc();
            if let Some(idx) = type_arr_state_idx {
                self.mark_state_var_modified(idx);
            }
            return None;
        };

        let expected_elem_sort = &array_sort.element_sort;
        let value = if value.sort() != expected_elem_sort {
            let sym_id = UNDEF_COUNTER.fetch_add(1, Ordering::Relaxed);
            let sym_name = crate::codegen_ay::names::store_coerce_name(type_key, sym_id);
            debug!(
                type_key = %type_key,
                expected_sort = ?expected_elem_sort,
                actual_sort = ?value.sort(),
                sym_name = %sym_name,
                "CHC: coerced type-indexed store value via fresh symbolic (Part of #2244)"
            );
            self.record_aggregate_gap("memory_type_indexed_store_sort_mismatch");
            declare_pending_var(sym_name, expected_elem_sort.clone())
        } else {
            value
        };

        // Part of #3608: Record constant-address store for compile-time forwarding.
        if let Some((fwd_obj_id, fwd_offset)) = Self::try_extract_constant_addr(&addr) {
            let fwd_key = ((fwd_obj_id as u64) << 32) | (fwd_offset as u64);
            debug!(
                obj_id = fwd_obj_id,
                offset = fwd_offset,
                type_key = %type_key,
                "CHC: build_memory_store - recording store-to-load forwarding (#3608)"
            );
            self.heap_state
                .store_forward_map
                .insert(fwd_key, (self.current_encode_bb, value.clone()));
        } else {
            // Part of #3664: symbolic-address store invalidates all forwards.
            self.heap_state.invalidate_store_forwards();
        }

        let store_expr = arr_base.store(addr.clone(), value.clone());

        self.heap_state.accumulate_store(type_key, cur_out_name, store_expr);
        self.heap_state.mark_array_modified(type_key);
        if let Some(idx) = type_arr_state_idx {
            self.mark_state_var_modified(idx);
        }

        self.mirror_pointer_wrapper_store_aliases(
            &addr,
            &value,
            type_key,
            &declared_elem_sort,
            signed,
        );

        debug!(
            type_key = %type_key,
            "CHC: build_memory_store - type-indexed store (accumulated, #1447)"
        );

        // Return None - constraint will be emitted by drain_store_chains() at block end
        None
    }

    /// Assigns a region array for a heap allocation and adds it to relation signatures.
    ///
    /// Part of #1448: Fix region arrays not added to CHC relation signatures.
    ///
    /// Returns (input_array_name, output_array_name) for the region.
    #[must_use]
    pub(in crate::codegen_ay::chc) fn assign_region_array_to_relation(
        &mut self,
        obj_id: u32,
        elem_sort: Sort,
    ) -> (Arc<str>, Arc<str>) {
        let (arr_name_arc, out_name) =
            self.heap_state.assign_region_array(obj_id, elem_sort.clone(), &self.fn_name);
        let effective_sort =
            self.heap_state.get_region_array(obj_id).map(|(_, _, sort)| sort).unwrap_or(elem_sort);

        let out_arc: Arc<str> =
            if self.state_var_mgr.declared_state_var_names.insert(Arc::clone(&arr_name_arc)) {
                let arr_sort = ptr_array_sort(effective_sort);
                let out_arc: Arc<str> = Arc::from(out_name.as_str());
                self.push_late_state_var_pair(Arc::clone(&arr_name_arc), &out_name, arr_sort);

                tracing::debug!(
                    obj_id,
                    arr_name = %arr_name_arc,
                    "CHC: added region array to relation signatures (#1448)"
                );
                out_arc
            } else {
                out_name.into()
            };

        (arr_name_arc, out_arc)
    }
}
