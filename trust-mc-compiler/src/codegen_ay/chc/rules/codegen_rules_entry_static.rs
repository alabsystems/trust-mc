// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Static memory constraint helpers for the CHC entry rule.
//!
//! Extracted from `codegen_rules_entry.rs` to keep file size under 500 lines.
//! Contains:
//! - `collect_static_alloc_size_constraints`: obj_size for static allocations
//! - `ensure_static_memory_type_arrays`: pre-register type arrays for static inits
//! - `collect_static_memory_constraints`: Mem_T[addr] = init_value constraints

use ay_bindings::{Expr, Sort};
use tracing::{debug, warn};

use crate::codegen_ay::chc::ChcCtx;
use crate::codegen_ay::chc::codegen_ctx::diagnostics::CellCounter;
use crate::codegen_ay::chc::codegen_ctx::record_translation_drop_site_reason_for_fn;
use crate::codegen_ay::chc::codegen_expr_heap::obj_size_in;
use crate::codegen_ay::types::POINTER_WIDTH;

/// Extension trait for static memory constraint methods on `ChcCtx`.
pub(in crate::codegen_ay::chc) trait CodegenRulesEntryStatic<'tcx, 'body> {
    fn collect_static_alloc_size_constraints(&self, constraints: &mut Vec<Expr>);
    fn collect_null_obj_size_constraint(&self, constraints: &mut Vec<Expr>);
    fn ensure_static_memory_type_arrays(&mut self);
    fn collect_static_memory_constraints(&self, constraints: &mut Vec<Expr>);
    fn collect_const_ref_memory_constraints(&self, constraints: &mut Vec<Expr>);
}

impl<'tcx, 'body> CodegenRulesEntryStatic<'tcx, 'body> for ChcCtx<'tcx, 'body> {
    /// Part of #3793: Static allocations get obj_ids for address distinctness
    /// but were missing obj_size entries. Inline drop body dealloc safety checks
    /// (from D2 vtable dispatch) test `obj_size[obj_id] >= sizeof(T)`, and
    /// without this constraint the size is unconstrained, causing spurious CTREX.
    ///
    /// Family 3 additionally makes the static base-address alignment explicit
    /// in the entry rule. The addresses are synthesized as `(obj_id << 32) | 0`;
    /// recording the requested alignment here keeps downstream kani_mem checks
    /// from having to rely on implicit reasoning about that encoding.
    fn collect_static_alloc_size_constraints(&self, constraints: &mut Vec<Expr>) {
        if self.ref_resolution.static_alloc_sizes.is_empty() {
            return;
        }
        let obj_size = obj_size_in();
        for &(obj_id, size_bytes, align_bytes) in &self.ref_resolution.static_alloc_sizes {
            let obj_id_expr = Expr::bitvec_const(obj_id as i128, 32);
            let size_expr = Expr::bitvec_const(size_bytes as i128, 32);
            constraints.push(obj_size.clone().select(obj_id_expr).eq(size_expr));
            // Alignment constraints removed: static addresses use encoding
            // concat(BV32(obj_id), BV32(0)), so low 32 bits are always zero.
            // Any power-of-2 alignment ≤ 2^32 is trivially satisfied.
            debug!(obj_id, size_bytes, align_bytes, "entry_rule: static alloc layout (#3793)");
        }
    }

    /// Part of #4067: Constrain null object (obj_id=0) size to 0.
    ///
    /// obj_id 0 is reserved for null and never legitimately allocated (alloc IDs
    /// start at 2). Without this, `obj_size[0]` is unconstrained in the SMT
    /// model, and bounds checks on pointers that resolve to obj_id=0 (e.g.,
    /// during unsized coercion of `Arc<Mutex<dyn T>>`) produce spurious CTREX
    /// because the solver picks `obj_size[0]` too small. Setting size=0
    /// triggers the zero-size exemption (`obj_size==0 || end<=obj_size`).
    fn collect_null_obj_size_constraint(&self, constraints: &mut Vec<Expr>) {
        if self.int_lift {
            return;
        }
        let obj_size = obj_size_in();
        let null_id = Expr::bitvec_const(0i128, 32);
        let zero_size = Expr::bitvec_const(0i128, 32);
        constraints.push(obj_size.select(null_id).eq(zero_size));
        debug!("entry_rule: obj_size[0] = 0 for null object (#4067)");
    }

    /// Part of #4023: Pre-register type arrays for all static memory inits.
    ///
    /// Static memory inits are collected during `collect_static_state_vars` and
    /// stored into `ref_resolution.static_memory_inits`. The entry rule constrains
    /// them as `Mem_T[addr] = init_value`. But `collect_static_memory_constraints`
    /// skips entries whose type key has no registered type array.
    ///
    /// For types like `AtomicUsize` (which has no Deref in MIR — atomics go through
    /// intrinsic Call terminators, not Deref), the type array is never created during
    /// the deref analysis pass. This function ensures every static memory init has
    /// a corresponding type array before the entry rule constrains them.
    fn ensure_static_memory_type_arrays(&mut self) {
        let missing: Vec<_> = self
            .ref_resolution
            .static_memory_inits
            .iter()
            .filter(|(tk, _, _, _)| {
                !self.heap_state.type_arrays.contains_key(tk.as_ref())
                    && !crate::codegen_ay::chc::decl::codegen_decl_static::is_uninit_shadow_type_key(tk)
            })
            .map(|(tk, es, _, _)| (tk.clone(), es.clone()))
            .collect();
        for (type_key, elem_sort) in missing {
            let (arr_name, arr_out_name, _, is_new) = self.heap_state.get_or_create_type_array(
                &type_key,
                elem_sort.clone(),
                &self.fn_name,
            );
            if is_new {
                let arr_sort = Sort::array(crate::codegen_ay::types::ptr_sort(), elem_sort);
                self.push_late_state_var_pair(
                    std::sync::Arc::clone(&arr_name),
                    &arr_out_name,
                    arr_sort,
                );
                debug!(
                    type_key = type_key.as_ref(),
                    "entry_rule: pre-registered type array for static memory init (#4023)"
                );
            }
        }

        // Part of #4023: Mark ALL static memory init arrays as "written" at entry
        // (bb_idx=0) so that load_from_memory recognizes them as initialized.
        // Without this, the entry rule constrains the array but loads skip it
        // because write_used_type_arrays doesn't include it.
        for (type_key, _, _, _) in &self.ref_resolution.static_memory_inits {
            if let Some((arr_name, _)) = self.heap_state.type_arrays.get(type_key.as_ref()) {
                self.heap_state.mark_type_array_written(&arr_name.clone(), 0);
            }
        }
    }

    fn collect_static_memory_constraints(&self, constraints: &mut Vec<Expr>) {
        use crate::codegen_ay::names;
        use crate::codegen_ay::types::ptr_sort;

        if self.ref_resolution.static_memory_inits.is_empty() {
            return;
        }

        for (type_key, elem_sort, init_value, addr_expr) in &self.ref_resolution.static_memory_inits
        {
            if !self.heap_state.type_arrays.contains_key(type_key.as_ref()) {
                // Part of #4066: uninit-check shadow types are intentionally
                // filtered from type array registration. Do not count them as
                // translation drops — they are dead state, not encoding gaps.
                if !crate::codegen_ay::chc::decl::codegen_decl_static::is_uninit_shadow_type_key(
                    type_key,
                ) {
                    warn!(
                        type_key = &**type_key,
                        "static memory mirror: array not registered for type key (#3496, #3854)"
                    );
                    self.diagnostics.place_translation_drop.inc();
                    record_translation_drop_site_reason_for_fn(
                        &self.fn_name,
                        "static_memory_array_unregistered",
                    );
                }
                continue;
            }

            let arr_name = names::mem_array_name(&self.fn_name, type_key);
            let arr_sort = Sort::array(ptr_sort(), elem_sort.clone());
            let arr = Expr::var(&*arr_name, arr_sort);
            constraints.push(arr.select(addr_expr.clone()).eq(init_value.clone()));
            debug!(
                type_key = type_key.as_ref(),
                "entry_rule constraining static memory mirror (#3496 Phase 5)"
            );
        }
    }

    /// Constrains typed memory arrays at promoted constant addresses (#2958).
    /// Part of #2958: promoted constant region obj_valid/obj_size + memory values.
    fn collect_const_ref_memory_constraints(&self, constraints: &mut Vec<Expr>) {
        use crate::codegen_ay::names;
        use crate::codegen_ay::types::ptr_sort;

        if self.ref_resolution.const_ref_memory_inits.is_empty() {
            return;
        }

        self.collect_promoted_validity_constraints(constraints);

        for (type_key, elem_sort, value, promoted_obj_id, byte_offset) in
            &self.ref_resolution.const_ref_memory_inits
        {
            if !self.heap_state.type_arrays.contains_key(&**type_key) {
                // Part of #4066: uninit-check shadow types are intentionally
                // filtered from type array registration.
                if !crate::codegen_ay::chc::decl::codegen_decl_static::is_uninit_shadow_type_key(
                    type_key,
                ) {
                    warn!(
                        type_key = &**type_key,
                        "skipping const_ref memory init: array not registered (#3222)"
                    );
                    self.diagnostics.place_translation_drop.inc();
                    record_translation_drop_site_reason_for_fn(
                        &self.fn_name,
                        "const_ref_array_unregistered",
                    );
                }
                continue;
            }
            let arr_name = names::mem_array_name(&self.fn_name, type_key);
            // Part of #4086: Skip when value sort mismatches registered cell sort.
            let reg_sort = self.heap_state.type_arrays.get(&**type_key).map(|(_, s)| s);
            let eff_sort = reg_sort.unwrap_or(elem_sort);
            if value.sort() != eff_sort {
                continue;
            }
            let arr_sort = Sort::array(ptr_sort(), eff_sort.clone());
            let arr = Expr::var(&*arr_name, arr_sort);
            let promoted_addr = self.heap_state.promoted_const_address_for(*promoted_obj_id);
            let addr = if *byte_offset == 0 {
                promoted_addr.clone()
            } else {
                promoted_addr.clone().bvadd(Expr::bitvec_const(*byte_offset, POINTER_WIDTH))
            };
            constraints.push(arr.select(addr).eq(value.clone()));
            debug!(
                type_key = &**type_key,
                byte_offset, "entry_rule constraining promoted constant memory (#2958/#2986)"
            );
        }
    }
}

/// Private helpers for promoted constant validity constraints.
impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Set generous size for each promoted constant region.
    /// obj_valid is NOT set per-entry — subsumed by `obj_valid = const_array(true)`.
    /// Part of #112: Skip when int_lift is active (arrays not declared).
    fn collect_promoted_validity_constraints(&self, constraints: &mut Vec<Expr>) {
        if self.int_lift {
            return;
        }
        let obj_size = obj_size_in();
        let promoted_obj_ids: std::collections::BTreeSet<u32> = self
            .ref_resolution
            .const_ref_memory_inits
            .iter()
            .map(|(_, _, _, promoted_obj_id, _)| *promoted_obj_id)
            .collect();
        for promoted_obj_id in promoted_obj_ids {
            let id_expr = Expr::bitvec_const(promoted_obj_id as i128, 32);
            constraints.push(obj_size.clone().select(id_expr).eq(Expr::bitvec_const(4096i128, 32)));
        }
    }
}
