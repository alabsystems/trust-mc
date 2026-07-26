// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Deref store propagation through IndexMut-returned `&mut T` to Vec fld_data.
//!
//! When `*dest = val` and `dest` was returned by `IndexMut::index_mut`,
//! the store propagates to the Vec's backing array: `data' = store(data, idx, val)`.
//!
//! Extracted from codegen_stmt_store_ref.rs per #3348 (file size limit).

use ay_bindings::Expr;
use tracing::{debug, warn};

use super::codegen_ctx::diagnostics::CellCounter;
use super::codegen_decl_flatten::collect_leaf_sorts;
use super::codegen_types::CodegenTypes;
use super::stmt_accumulator::StmtAccumulator;
use super::{ChcCtx, UnknownProjectionPolicy, collect_field_projections};

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Handle deref store through an IndexMut-returned `&mut T`.
    ///
    /// When `*dest = val` and `dest` was returned by `IndexMut::index_mut`,
    /// propagate the store to the Vec's backing array:
    ///   `data' = store(data, idx, val)`
    ///
    /// Supports both projected Vec (scalar state vars) and Datatype Vec paths.
    ///
    /// Part of #3348: Vec IndexMut CHC stub.
    pub(in crate::codegen_ay::chc) fn handle_collection_mut_ref_store(
        &mut self,
        rhs_expr: Expr,
        cmr: &super::codegen_ctx::types::CollectionMutRef,
        acc: &mut StmtAccumulator<'_>,
    ) -> bool {
        use super::codegen_ctx::types::CollectionProjectionKind;

        let coll_local = cmr.collection_local;
        let idx = &cmr.index_expr;
        self.invalidate_vec_adapter_source_data(coll_local);

        // Path A: Projected Vec (scalar state vars for ptr/len/cap/data).
        if self.collections.projection_locals.get(&coll_local).copied()
            == Some(CollectionProjectionKind::Vec)
        {
            let data_field = self.flattened_local_field_expr(coll_local, 3, acc.modified);
            if let Some(old_data) = data_field
                && old_data.sort().is_array()
            {
                let coerced_rhs = Self::coerce_store_value(
                    old_data.sort(),
                    rhs_expr.clone(),
                    false,
                    &self.diagnostics,
                );
                let new_data = old_data.store(idx.clone(), coerced_rhs);
                // Constrain all 4 Vec fields: only data changes, rest preserved.
                let ptr_field = self.flattened_local_field_expr(coll_local, 0, acc.modified);
                let len_field = self.flattened_local_field_expr(coll_local, 1, acc.modified);
                let cap_field = self.flattened_local_field_expr(coll_local, 2, acc.modified);
                self.constrain_flattened_fields(
                    coll_local,
                    &[ptr_field, len_field, cap_field, Some(new_data)],
                    acc,
                );
                debug!(
                    coll_local,
                    "CHC: IndexMut deref store via projected Vec — data[idx] updated (#3348)"
                );
                return true;
            }
        }

        // Path B: Datatype Vec (single state var with fld_ptr/fld_len/fld_cap/fld_data).
        let vec_idx = self
            .ref_resolution
            .ref_arg_pointee_idx
            .get(&coll_local)
            .copied()
            .or_else(|| self.state_var_mgr.local_to_state_idx.get(&coll_local).copied());
        if let Some(vec_idx) = vec_idx {
            let vec_input = self
                .state_var_mgr
                .state_vars
                .get(vec_idx)
                .map(|(name, sort)| Expr::var(&**name, sort.clone()));
            if let Some(vec_in) = vec_input
                && vec_in.sort().datatype_name().is_some()
                && Self::get_dt_field_sort(&vec_in, "fld_data").is_some_and(|s| s.is_array())
            {
                if let Some((ptr, len, cap, data)) =
                    super::codegen_call_vec::ChcVecFields::extract_without_name(vec_in)
                {
                    let coerced_rhs = Self::coerce_store_value(
                        data.sort(),
                        rhs_expr.clone(),
                        false,
                        &self.diagnostics,
                    );
                    let new_data = data.store(idx.clone(), coerced_rhs);
                    if let Some((out_name, out_sort)) =
                        self.state_var_mgr.output_state_vars.get(vec_idx).cloned()
                    {
                        let sort_ref = out_sort.clone();
                        let dt_name = sort_ref
                            .datatype_name()
                            .expect("invariant: matched datatype_name().is_some() above");
                        let constraint = Self::build_vec_datatype_eq(
                            dt_name,
                            vec![ptr, len, cap, new_data],
                            &out_name,
                            &out_sort,
                        );
                        acc.replace_constraint(coll_local, constraint);
                        self.mark_state_var_modified(vec_idx);
                        acc.modified.insert(coll_local);
                        debug!(
                            coll_local,
                            vec_idx,
                            "CHC: IndexMut deref store via Datatype Vec — data[idx] updated (#3348)"
                        );
                        return true;
                    }
                }
            }
        }

        // Path C: Struct-embedded Vec (Vec accessed through struct field projection).
        // Part of #3439: When coll_local is a struct containing a Vec field,
        // field_projections carries the Field projection from struct to Vec.
        // Supports two sub-cases:
        //   C1: Datatype struct — navigate Datatype selectors to Vec field
        //   C2: Flattened struct — compute flat leaf offset to Vec's data Array
        if !cmr.field_projections.is_empty() {
            if let Some(result) = self.handle_struct_embedded_vec_store(rhs_expr, cmr, acc) {
                return result;
            }
        }

        // Fallback: could not resolve Vec backing array.
        warn!(
            coll_local,
            "CHC: IndexMut deref store — could not resolve Vec; constraint dropped (#3348)"
        );
        self.diagnostics.store_dropped_transition.inc();
        // Part of #3138: mark collection local modified-unconstrained (universally quantified)
        acc.modified.insert(coll_local);
        true
    }

    /// Handle store through struct-projected Vec (e.g., `self.marks[var] = val`).
    ///
    /// When a Vec is accessed through a struct field projection, the
    /// `collection_local` points to the struct, and `field_projections`
    /// describes the path from struct to Vec. This method:
    /// 1. Gets the struct's state var
    /// 2. Navigates field projections to extract the Vec sub-expression
    /// 3. Extracts fld_data from the Vec
    /// 4. Stores `rhs_expr` at the index
    /// 5. Reconstructs Vec with updated fld_data
    /// 6. Reconstructs struct with updated Vec field
    /// 7. Emits constraint equating output state var to reconstructed struct
    ///
    /// Part of #3439: struct-projected collection IndexMut.
    fn handle_struct_embedded_vec_store(
        &mut self,
        rhs_expr: Expr,
        cmr: &super::codegen_ctx::types::CollectionMutRef,
        acc: &mut StmtAccumulator<'_>,
    ) -> Option<bool> {
        let coll_local = cmr.collection_local;
        let idx = &cmr.index_expr;

        // Resolve struct state var.
        let struct_state_idx = self
            .ref_resolution
            .ref_arg_pointee_idx
            .get(&coll_local)
            .copied()
            .or_else(|| self.state_var_mgr.local_to_state_idx.get(&coll_local).copied())?;

        let (_, in_sort) = self.state_var_mgr.state_vars.get(struct_state_idx)?;
        let is_datatype = in_sort.datatype_name().is_some();

        // Convert ProjectionElem to FieldProjection for the projection APIs.
        let field_projs =
            collect_field_projections(&cmr.field_projections, UnknownProjectionPolicy::Skip);
        if field_projs.is_empty() {
            return None;
        }

        // Check if the struct state var is a Datatype (non-flattened) or BV/scalar (flattened).
        // Flattened structs have their fields projected into individual leaf state vars.
        if is_datatype {
            // Sub-case C1: Datatype struct — use selector/update operations.
            self.handle_struct_embedded_vec_store_datatype(
                rhs_expr,
                coll_local,
                idx,
                struct_state_idx,
                &field_projs,
                acc,
            )
        } else {
            // Sub-case C2: Flattened struct — compute flat leaf offset.
            self.handle_struct_embedded_vec_store_flattened(
                rhs_expr,
                coll_local,
                idx,
                &field_projs,
                acc,
            )
        }
    }

    /// C1: Datatype struct path — navigate Datatype selectors to the Vec field,
    /// extract fld_data, store, reconstruct Vec then struct.
    fn handle_struct_embedded_vec_store_datatype(
        &mut self,
        rhs_expr: Expr,
        coll_local: usize,
        idx: &Expr,
        struct_state_idx: usize,
        field_projs: &[super::FieldProjection],
        acc: &mut StmtAccumulator<'_>,
    ) -> Option<bool> {
        let (in_name, in_sort) = self.state_var_mgr.state_vars.get(struct_state_idx)?;
        let struct_in = Expr::var(&**in_name, in_sort.clone());

        // Navigate field projections to extract the Vec sub-expression.
        let vec_expr = Self::apply_field_selections(struct_in.clone(), field_projs)?;

        // Verify it's a Vec-like datatype with fld_data.
        if vec_expr.sort().datatype_name().is_none()
            || !Self::get_dt_field_sort(&vec_expr, "fld_data").is_some_and(|s| s.is_array())
        {
            debug!(
                coll_local,
                "CHC: struct-embedded Vec store C1 — field is not a Vec datatype (#3439)"
            );
            return None;
        }

        // Extract Vec fields.
        let (ptr, len, cap, data) =
            super::codegen_call_vec::ChcVecFields::extract_without_name(vec_expr.clone())?;

        // Store new value into fld_data.
        let coerced_rhs = Self::coerce_store_value(data.sort(), rhs_expr, false, &self.diagnostics);
        let new_data = data.store(idx.clone(), coerced_rhs);

        // Reconstruct Vec with updated fld_data.
        let vec_sort = vec_expr.sort().clone();
        let vec_dt_name_owned = vec_sort.datatype_name().map(|s| s.to_owned())?;
        let vec_cons_name = crate::codegen_ay::names::cons_name(&vec_dt_name_owned);
        let new_vec = Expr::datatype_constructor(
            &vec_dt_name_owned,
            vec_cons_name,
            vec![ptr, len, cap, new_data],
            vec_sort,
        );

        // Reconstruct struct with updated Vec field using functional update.
        let new_struct = Self::apply_projection_update(&struct_in, field_projs, new_vec)?;

        // Emit constraint: output_struct = new_struct.
        let (out_name, out_sort) =
            self.state_var_mgr.output_state_vars.get(struct_state_idx)?.clone();
        let out_var = Expr::var(&*out_name, out_sort);
        let constraint = out_var.eq(new_struct);

        acc.replace_constraint(coll_local, constraint);
        self.mark_state_var_modified(struct_state_idx);
        acc.modified.insert(coll_local);

        debug!(
            coll_local,
            struct_state_idx,
            field_projections_len = field_projs.len(),
            "CHC: IndexMut deref store via struct-embedded Vec (Datatype) — data[idx] updated (#3439)"
        );

        Some(true)
    }

    /// C2: Flattened struct path — the struct has been recursively flattened into
    /// leaf state vars. Compute the flat base offset for the target Vec field,
    /// then directly update the data Array at `flat_base + 3`.
    ///
    /// Part of #3439: handles structs like `Marks { data: Vec<bool>, indices: Vec<usize> }`
    /// where the struct is flattened to 8 leaf state vars (4 per Vec).
    fn handle_struct_embedded_vec_store_flattened(
        &mut self,
        rhs_expr: Expr,
        coll_local: usize,
        idx: &Expr,
        field_projs: &[super::FieldProjection],
        acc: &mut StmtAccumulator<'_>,
    ) -> Option<bool> {
        // Only single-level field projections supported for flattened structs.
        if field_projs.len() != 1 {
            return None;
        }
        let target_field_idx = field_projs[0].field_idx;

        // Recover the struct's original Datatype sort from the MIR type.
        // The state var is already flattened (BV64 etc.), so we need the
        // pre-flattening sort to compute field offsets.
        let local_ty = self.body.locals().get(coll_local).map(|l| l.ty)?;
        let struct_sort = Self::translate_ty(local_ty)?;
        let dt = struct_sort.datatype_sort()?;
        if dt.constructors.len() != 1 {
            return None;
        }
        let cons = &dt.constructors[0];
        if target_field_idx >= cons.fields.len() {
            return None;
        }

        // Compute the flat base offset: sum of leaf counts for all preceding fields.
        let mut flat_base = 0;
        for f in &cons.fields[..target_field_idx] {
            flat_base += collect_leaf_sorts(&f.sort, 0).len();
        }

        // The target field should be a Vec-like type with 4 leaf fields (ptr, len, cap, data).
        let target_sort = &cons.fields[target_field_idx].sort;
        let target_leaves = collect_leaf_sorts(target_sort, 0);
        if target_leaves.len() != 4 {
            debug!(
                coll_local,
                target_field_idx,
                leaf_count = target_leaves.len(),
                "CHC: struct-embedded Vec store C2 — target field not a 4-field Vec (#3439)"
            );
            return None;
        }
        // Verify the 4th leaf (data) is an Array.
        if !target_leaves[3].is_array() {
            debug!(coll_local, "CHC: struct-embedded Vec store C2 — 4th leaf is not Array (#3439)");
            return None;
        }

        // Part of #3348 soundness fix (Direction 1): bypass flattened_field_env
        // for the data field read. The env may contain a stale VecFromElem
        // initialization (e.g., const_array(false)) instead of the current
        // state variable. Reading the input state var directly ensures the
        // store produces store(_8_fld3, idx, val), not store(const_array(false), idx, val).
        let base_idx = self.try_state_idx_for_local(coll_local)?;
        let data_slot = base_idx + flat_base + 3;
        let old_data = self
            .state_var_mgr
            .state_vars
            .get(data_slot)
            .map(|(name, sort)| Expr::var(&**name, sort.clone()))?;
        if !old_data.sort().is_array() {
            return None;
        }

        let coerced_rhs =
            Self::coerce_store_value(old_data.sort(), rhs_expr, false, &self.diagnostics);
        let new_data = old_data.store(idx.clone(), coerced_rhs);

        // Part of #3348: Populate env for ALL fields so later handlers (e.g.,
        // VecPush in the same block's call terminator) read correct values via
        // `flattened_local_field_expr`. Only CONSTRAIN the target Vec's 4 fields
        // to avoid Phase 1/Phase 2 conflict — if a Call terminator handler also
        // constrains non-target fields, the constraints would contradict.
        let total_leaves: usize =
            cons.fields.iter().map(|f| collect_leaf_sorts(&f.sort, 0).len()).sum();
        // Part of #3348: populate env from input state vars for the target Vec's
        // fields (flat_base..flat_base+4) to prevent stale VecFromElem values from
        // propagating. Non-target fields still use env-first lookup since they are
        // not affected by the IndexMut store.
        for i in 0..total_leaves {
            let in_target_vec = i >= flat_base && i < flat_base + 4;
            let val = if in_target_vec {
                let slot = base_idx + i;
                self.state_var_mgr
                    .state_vars
                    .get(slot)
                    .map(|(name, sort)| Expr::var(&**name, sort.clone()))
            } else {
                self.flattened_local_field_expr(coll_local, i, acc.modified)
            };
            if let Some(v) = val {
                self.encode.flattened_field_env.insert((coll_local, i), v);
            }
        }
        // Override env for the modified data field with the new stored value.
        self.encode.flattened_field_env.insert((coll_local, flat_base + 3), new_data.clone());

        // Only constrain the TARGET Vec's 4 fields (ptr/len/cap carry-forward
        // + data update). Non-target fields are left unconstrained here;
        // `build_block_output_args` uses per-field granularity (#3348) to emit
        // INPUT vars for unconstrained fields (Goto terminators), and Call
        // terminator handlers constrain them in Phase 2.
        //
        // Part of #3348: read target Vec fields from input state vars directly,
        // bypassing env (same rationale as Direction 1 data fix above). This
        // ensures carry-forward fields (ptr/len/cap) use symbolic input vars
        // even when the env contains stale VecFromElem initialization values.
        let mut values: Vec<Option<Expr>> = vec![None; total_leaves];
        for i in 0..4 {
            let slot = base_idx + flat_base + i;
            values[flat_base + i] = self
                .state_var_mgr
                .state_vars
                .get(slot)
                .map(|(name, sort)| Expr::var(&**name, sort.clone()));
        }
        values[flat_base + 3] = Some(new_data);

        self.constrain_flattened_fields(coll_local, &values, acc);

        debug!(
            coll_local,
            target_field_idx,
            flat_base,
            "CHC: IndexMut deref store via struct-embedded Vec (flattened) — data[idx] updated (#3348/#3439)"
        );

        Some(true)
    }
}
