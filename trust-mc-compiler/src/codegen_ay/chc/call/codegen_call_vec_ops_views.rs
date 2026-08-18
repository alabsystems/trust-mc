// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Vec view operation helpers.
//!
//! Extracted from `codegen_call_vec_ops.rs` per #2923 (500 LOC threshold).

use std::collections::HashSet;

use crate::codegen_ay::chc::call::call_accumulator::CallAccumulator;
use ay_bindings::{Expr, Sort};
use rustc_public::mir::ProjectionElem;
use tracing::debug;

use crate::codegen_ay::names::{self, struct_sort, vec_layout};
use crate::codegen_ay::types::ptr_sort;

use super::ChcCtx;
use super::codegen_call_coerce::CallCoerce;
use super::codegen_ctx::types::CollectionProjectionKind;
use super::codegen_decl_flatten::collect_leaf_sorts;
use super::codegen_types::CodegenTypes; // W1 incomplete: needed for translate_ty
use super::{UnknownProjectionPolicy, collect_field_projections};

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// VecCapacity: dest = tracked cap (sidecar → projected → Datatype).
    ///
    /// Fix #2877: sidecar cap variable is the authoritative source after
    /// mutations (push/reserve/shrink_to_fit), matching `vec_op_len`'s
    /// sidecar-first pattern. Datatype fld_cap is the fallback.
    pub(in crate::codegen_ay::chc) fn vec_op_capacity(
        &mut self,
        modified_locals: &HashSet<usize>,
        collection_local: Option<usize>,
        dest_local: usize,
        acc: &mut CallAccumulator<'_>,
    ) {
        // Path A: sidecar cap variable (primary — matches vec_op_len pattern).
        if let Some(coll_local) = collection_local
            && let Some(cap_var_name) = self.collections.len_state.get_cap_var(coll_local).cloned()
        {
            let cap_expr = self.collection_current_cap(&cap_var_name);
            if let Some((_, dest_var)) = self.resolve_destination(dest_local) {
                if let Some(eq) = self.make_coerced_eq_constraint(
                    &dest_var,
                    cap_expr,
                    dest_var.sort(),
                    dest_local,
                    "codegen_call_vec_core::VecCapacity",
                ) {
                    acc.constraints.push(eq);
                }
                acc.dests.push(dest_local);
            }
            return;
        }
        // Path B/C: projected field or Datatype fld_cap (fallback).
        let cap_resolved = collection_local.and_then(|coll_local| {
            let vec_idx = self.state_var_mgr.local_to_state_idx.get(&coll_local).copied()?;
            if self.collections.projection_locals.get(&coll_local).copied()
                == Some(CollectionProjectionKind::Vec)
            {
                return self.flattened_local_field_expr(coll_local, 2, modified_locals);
            }
            let (name, sort) = if modified_locals.contains(&coll_local) {
                self.state_var_mgr.output_state_vars.get(vec_idx)?
            } else {
                self.state_var_mgr.state_vars.get(vec_idx)?
            };
            let vec = Expr::var(&**name, sort.clone());
            // Clone Sort (O(1) Arc) to borrow dt_name as &str. Part of #2267.
            let sort_ref = vec.sort().clone();
            let dt_name = sort_ref.datatype_name()?;
            let cap_sort = Self::get_dt_field_sort(&vec, "fld_cap")?;
            Some(vec.field_select(dt_name, "fld_cap", cap_sort))
        });
        if let Some(cap_expr) = cap_resolved {
            if let Some((_, dest_var)) = self.resolve_destination(dest_local) {
                if let Some(eq) = self.make_coerced_eq_constraint(
                    &dest_var,
                    cap_expr,
                    dest_var.sort(),
                    dest_local,
                    "codegen_call_vec_core::VecCapacity",
                ) {
                    acc.constraints.push(eq);
                }
                acc.dests.push(dest_local);
            }
        } else {
            acc.dests.push(dest_local);
        }
    }

    /// VecAsPtr/VecAsMutPtr: dest = fld_ptr from tracked Vec state.
    /// Part of #3783: avoid treating `&Vec<T>` / `&mut Vec<T>` receiver shells
    /// as the data pointer when the real `fld_ptr` must be recovered first.
    pub(in crate::codegen_ay::chc) fn vec_op_as_ptr(
        &mut self,
        modified_locals: &HashSet<usize>,
        collection_local: Option<usize>,
        dest_local: usize,
        acc: &mut CallAccumulator<'_>,
    ) {
        let ptr_resolved = collection_local
            .and_then(|coll_local| self.resolve_vec_ptr_expr(coll_local, modified_locals));
        if let Some(ptr_expr) = ptr_resolved {
            if let Some((_, dest_var)) = self.resolve_destination(dest_local) {
                if let Some(eq) = self.make_coerced_eq_constraint(
                    &dest_var,
                    ptr_expr,
                    dest_var.sort(),
                    dest_local,
                    "codegen_call_vec_ops_views::VecAsPtr",
                ) {
                    acc.constraints.push(eq);
                }
                acc.dests.push(dest_local);
            }
        } else {
            // Fallback: leave unconstrained (collection_local not resolved).
            acc.dests.push(dest_local);
        }
    }

    fn resolve_vec_ptr_expr(
        &mut self,
        coll_local: usize,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        if self.collections.projection_locals.get(&coll_local).copied()
            == Some(CollectionProjectionKind::Vec)
        {
            return self.flattened_local_field_expr(
                coll_local,
                vec_layout::IDX_PTR,
                modified_locals,
            );
        }
        let vec_idx = self
            .ref_resolution
            .ref_arg_pointee_idx
            .get(&coll_local)
            .copied()
            .or_else(|| self.state_var_mgr.local_to_state_idx.get(&coll_local).copied());
        if let Some(vec_idx) = vec_idx {
            let (name, sort) = if modified_locals.contains(&coll_local) {
                self.state_var_mgr.output_state_vars.get(vec_idx)?
            } else {
                self.state_var_mgr.state_vars.get(vec_idx)?
            };
            let vec_expr = Expr::var(&**name, sort.clone());
            if let Some(dt_name) = sort.datatype_name() {
                let ptr_sort = Self::get_dt_field_sort(&vec_expr, "fld_ptr")
                    .unwrap_or_else(crate::codegen_ay::types::ptr_sort);
                return Some(vec_expr.field_select(dt_name, "fld_ptr", ptr_sort));
            }
        }

        if let Some((ptr, _, _, _)) =
            self.try_resolve_vec_fields_fallback(coll_local, modified_locals)
        {
            return Some(ptr);
        }
        self.try_resolve_vec_via_memory_load(coll_local, modified_locals).map(|(ptr, _, _, _)| ptr)
    }

    /// VecAsSlice: dest = Slice(fld_ptr, fld_len, fld_data).
    pub(in crate::codegen_ay::chc) fn vec_op_as_slice(
        &mut self,
        modified_locals: &HashSet<usize>,
        collection_local: Option<usize>,
        dest_local: usize,
        field_projections: &[rustc_public::mir::ProjectionElem],
        acc: &mut CallAccumulator<'_>,
    ) {
        let vec_fields: Option<(Expr, Expr, Expr, Sort)> =
            collection_local.and_then(|coll_local| {
                let vec_idx = self.state_var_mgr.local_to_state_idx.get(&coll_local).copied()?;
                if self.collections.projection_locals.get(&coll_local).copied()
                    == Some(CollectionProjectionKind::Vec)
                {
                    let ptr = self.flattened_local_field_expr(coll_local, 0, modified_locals)?;
                    let len = self.flattened_local_field_expr(coll_local, 1, modified_locals)?;
                    let data = self.flattened_local_field_expr(coll_local, 3, modified_locals)?;
                    let data_sort = data.sort().clone();
                    return Some((ptr, len, data, data_sort));
                }
                let (name, sort) = if modified_locals.contains(&coll_local) {
                    self.state_var_mgr.output_state_vars.get(vec_idx)?
                } else {
                    self.state_var_mgr.state_vars.get(vec_idx)?
                };
                let vec = Expr::var(&**name, sort.clone());
                Self::extract_vec_dt_fields(&vec)
            });

        // Part of #3348: Struct-embedded Vec (e.g., `m.data` where Marks has
        // two Vecs). When field_projections are present and collection_local
        // is a struct, resolve the specific Vec field using C1/C2 pattern.
        let vec_fields = if vec_fields.is_none() && !field_projections.is_empty() {
            collection_local.and_then(|coll_local| {
                self.vec_as_slice_struct_embedded(coll_local, field_projections, modified_locals)
            })
        } else {
            vec_fields
        };

        // Part of #3348: BV64 memory load fallback for parameter-derived Vecs.
        // When the primary resolution fails because the state var is BV64
        // (pointer to Vec in memory, e.g., `(*self).0` in `Bits::concat`),
        // load the Vec Datatype from memory and extract its fields.
        let vec_fields = if vec_fields.is_none() {
            if let Some(coll_local) = collection_local {
                self.try_resolve_vec_via_memory_load(coll_local, modified_locals)
            } else {
                None
            }
        } else {
            vec_fields
        };

        // Part of #3348: Fallback for parameter-derived Vecs (e.g., `(*self).0`).
        // When the primary resolution fails because collection_local has no
        // local_to_state_idx entry, try resolving through ref_targets and
        // flattened projection locals.
        let vec_fields = if vec_fields.is_none() {
            collection_local.and_then(|coll_local| {
                self.try_resolve_vec_fields_fallback(coll_local, modified_locals)
            })
        } else {
            vec_fields
        };

        // Part of #3348: Record slice→Vec mapping for downstream IndexMut store propagation.
        if let Some(coll_local) = collection_local {
            self.ref_resolution.slice_to_vec_local.insert(dest_local, coll_local);
        }

        if let Some((ptr, len, data, data_sort)) = vec_fields {
            if let Some((_, dest_var)) = self.resolve_destination(dest_local) {
                let out_sort = dest_var.sort().clone();
                let result_expr = if out_sort.is_array() {
                    // Destination is Array sort (bare `[T]` via translate_ty) —
                    // return backing data directly.
                    data
                } else if out_sort.is_bitvec() {
                    // Destination is BitVec(64) (reference `&[T]` via translate_ty).
                    // Return fld_ptr to satisfy the pointer sort, and register
                    // fld_data in const_ref_values so downstream SliceIndex can
                    // resolve the backing array via resolve_ref_or_const_referent
                    // Tier 2. Part of #2876: fixes VecAsSlice Slice_bv32→BV64
                    // sort mismatch that dropped constraints on 3 heap_realloc
                    // harnesses.
                    self.ref_resolution.const_ref_values.insert(dest_local, data.clone());
                    // Part of #3012: Also store the full Slice view so that downstream
                    // VecIter/VecIterMut handlers can reconstruct the Slice for
                    // make_vec_into_iter_chc when the iter() argument is a bv64
                    // reference that came from this deref call.
                    let elem_sort = data_sort
                        .array_sort()
                        .map_or_else(ptr_sort, |arr| arr.element_sort.clone());
                    let slice_name = names::slice_sort_name(&names::sort_short_name(&elem_sort));
                    let ctor_name = names::cons_name(&slice_name);
                    let slice_sort = struct_sort(
                        slice_name.clone(),
                        [("fld_ptr", ptr_sort()), ("fld_len", ptr_sort()), ("fld_data", data_sort)],
                    );
                    let slice_view = Expr::datatype_constructor(
                        slice_name,
                        ctor_name,
                        vec![ptr.clone(), len, data],
                        slice_sort,
                    );
                    self.ref_resolution.const_ref_slice_views.insert(dest_local, slice_view);
                    ptr
                } else {
                    let elem_sort = data_sort
                        .array_sort()
                        .map_or_else(ptr_sort, |arr| arr.element_sort.clone());
                    let slice_name = names::slice_sort_name(&names::sort_short_name(&elem_sort));
                    let ctor_name = names::cons_name(&slice_name);
                    let slice_sort = struct_sort(
                        slice_name.clone(),
                        [("fld_ptr", ptr_sort()), ("fld_len", ptr_sort()), ("fld_data", data_sort)],
                    );
                    Expr::datatype_constructor(
                        slice_name,
                        ctor_name,
                        vec![ptr, len, data],
                        slice_sort,
                    )
                };
                if let Some(eq) = self.make_coerced_eq_constraint(
                    &dest_var,
                    result_expr,
                    &out_sort,
                    dest_local,
                    "codegen_call_vec_core::VecAsSlice",
                ) {
                    acc.constraints.push(eq);
                }
            }
            debug!(
                fn_name = %self.fn_name,
                "VecAsSlice: constructed Slice with fld_data from Vec state var"
            );
        } else {
            debug!(
                fn_name = %self.fn_name,
                "VecAsSlice: Vec state var not resolved; symbolic fallback"
            );
            self.record_sound_fallback_reason("vec_as_slice_unresolved");
        }
        acc.dests.push(dest_local);
    }

    /// Extract (fld_ptr, fld_len, fld_data, data_sort) from a Vec Datatype expression.
    fn extract_vec_dt_fields(vec: &Expr) -> Option<(Expr, Expr, Expr, Sort)> {
        let sort_ref = vec.sort().clone();
        let dt_name = sort_ref.datatype_name()?;
        let ptr_s = Self::get_dt_field_sort(vec, "fld_ptr")?;
        let len_s = Self::get_dt_field_sort(vec, "fld_len")?;
        let data_s = Self::get_dt_field_sort(vec, "fld_data")?;
        let ptr = vec.clone().field_select(dt_name, "fld_ptr", ptr_s);
        let len = vec.clone().field_select(dt_name, "fld_len", len_s);
        let data = vec.clone().field_select(dt_name, "fld_data", data_s.clone());
        Some((ptr, len, data, data_s))
    }

    /// Struct-embedded Vec resolution for VecAsSlice.
    ///
    /// When collection_local is a struct with field_projections pointing to a
    /// Vec field, extract (ptr, len, data) using the C1/C2 pattern from
    /// VecLen/VecPush struct-embedded handlers.
    ///
    /// Part of #3348: VecAsSlice on struct-embedded Vec.
    fn vec_as_slice_struct_embedded(
        &self,
        coll_local: usize,
        field_projections: &[ProjectionElem],
        modified_locals: &HashSet<usize>,
    ) -> Option<(Expr, Expr, Expr, Sort)> {
        let field_projs =
            collect_field_projections(field_projections, UnknownProjectionPolicy::Skip);
        if field_projs.is_empty() {
            return None;
        }

        // Try C1: Datatype struct — navigate selectors to Vec field.
        let struct_state_idx = self
            .ref_resolution
            .ref_arg_pointee_idx
            .get(&coll_local)
            .copied()
            .or_else(|| self.state_var_mgr.local_to_state_idx.get(&coll_local).copied())?;
        let (in_name, in_sort) = self.state_var_mgr.state_vars.get(struct_state_idx)?.clone();

        if in_sort.datatype_name().is_some() {
            let struct_in = Expr::var(&*in_name, in_sort);
            let vec_expr = Self::apply_field_selections(struct_in, &field_projs)?;
            return Self::extract_vec_dt_fields(&vec_expr);
        }

        // C2: Flattened struct — compute flat base offset, read Vec's leaf fields.
        if field_projs.len() != 1 {
            return None;
        }
        let target_field_idx = field_projs[0].field_idx;

        let owner_ty = self.struct_embedded_owner_ty(coll_local)?;
        let struct_sort_val = Self::translate_ty(owner_ty)?;
        let dt = struct_sort_val.datatype_sort()?;
        if dt.constructors.len() != 1 || target_field_idx >= dt.constructors[0].fields.len() {
            return None;
        }
        let cons = &dt.constructors[0];

        let mut flat_base = 0;
        for f in &cons.fields[..target_field_idx] {
            flat_base += collect_leaf_sorts(&f.sort, 0).len();
        }

        let target_sort = &cons.fields[target_field_idx].sort;
        let target_leaves = collect_leaf_sorts(target_sort, 0);
        if target_leaves.len() != vec_layout::FIELD_COUNT
            || !target_leaves[vec_layout::IDX_DATA].is_array()
        {
            return None;
        }

        let ptr = self.flattened_local_field_expr(
            coll_local,
            flat_base + vec_layout::IDX_PTR,
            modified_locals,
        )?;
        let len = self.flattened_local_field_expr(
            coll_local,
            flat_base + vec_layout::IDX_LEN,
            modified_locals,
        )?;
        let data = self.flattened_local_field_expr(
            coll_local,
            flat_base + vec_layout::IDX_DATA,
            modified_locals,
        )?;
        let data_sort = data.sort().clone();

        debug!(
            fn_name = %self.fn_name,
            coll_local,
            target_field_idx,
            flat_base,
            "VecAsSlice: struct-embedded C2 — resolved Vec fields (#3348)"
        );
        Some((ptr, len, data, data_sort))
    }

    /// Fallback Vec field resolution for parameter-derived Vecs.
    ///
    /// When the primary resolution in `vec_op_as_slice` fails (no
    /// `local_to_state_idx` entry for collection_local), this tries:
    /// 1. Trace through ref_targets to find the actual Vec local
    /// 2. Check if the traced local is a flattened Vec (projection_locals)
    /// 3. Resolve the traced local's state var as a Datatype and extract fields
    ///
    /// Part of #3348: enables VecAsSlice for `(*self).0` in `Bits::concat`.
    fn try_resolve_vec_fields_fallback(
        &self,
        coll_local: usize,
        modified_locals: &HashSet<usize>,
    ) -> Option<(Expr, Expr, Expr, Sort)> {
        // Try coll_local first, then trace through ref_targets.
        let ref_target = self.ref_resolution.ref_targets.get(&coll_local).map(|rt| rt.local);
        let candidates = [Some(coll_local), ref_target];
        for candidate in candidates.into_iter().flatten() {
            // Flattened Vec path
            if self.collections.projection_locals.get(&candidate).copied()
                == Some(CollectionProjectionKind::Vec)
            {
                let ptr = self.flattened_local_field_expr(candidate, 0, modified_locals)?;
                let len = self.flattened_local_field_expr(candidate, 1, modified_locals)?;
                let data = self.flattened_local_field_expr(candidate, 3, modified_locals)?;
                let data_sort = data.sort().clone();
                return Some((ptr, len, data, data_sort));
            }
            // Non-flattened Datatype path
            if let Some(vec_expr) = self.try_resolve_local_expr(candidate, modified_locals) {
                if let Some(fields) = Self::extract_vec_dt_fields(&vec_expr) {
                    return Some(fields);
                }
            }
        }
        None
    }

    /// BV64 memory load fallback for VecAsSlice.
    ///
    /// When the collection local's state var is BV64 (a pointer to a
    /// Vec in memory, typical for parameter-derived Vecs like `(*self).0`),
    /// load the Vec Datatype from the heap model and extract its fields.
    ///
    /// Part of #3348: unblocks bv_concat_width_sum harness.
    fn try_resolve_vec_via_memory_load(
        &mut self,
        coll_local: usize,
        modified_locals: &HashSet<usize>,
    ) -> Option<(Expr, Expr, Expr, Sort)> {
        let vec_idx = self.state_var_mgr.local_to_state_idx.get(&coll_local).copied()?;
        let (name, sort) = if modified_locals.contains(&coll_local) {
            self.state_var_mgr.output_state_vars.get(vec_idx)?
        } else {
            self.state_var_mgr.state_vars.get(vec_idx)?
        };
        // Only applies when state var is a BV pointer, not a Datatype.
        if !sort.is_bitvec() {
            return None;
        }
        let addr = Expr::var(&**name, sort.clone());

        // Get the MIR type for this local and determine the pointee type.
        // For `&Vec<T>`, pointee is `Vec<T>`. For `Vec<T>` stored as BV64
        // (memory-backed), use the type directly.
        let local_ty = self.body.locals().get(coll_local)?.ty;
        let pointee_ty = Self::deref_pointee_ty(local_ty).unwrap_or(local_ty);

        debug!(
            fn_name = %self.fn_name,
            coll_local,
            ?pointee_ty,
            "VecAsSlice: BV64 state var → memory load fallback"
        );

        let loaded = self.load_from_memory_untyped(addr, pointee_ty)?;
        Self::extract_vec_dt_fields(&loaded)
    }
}
