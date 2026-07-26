// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Collection projection helpers for CHC stub call sites.
//!
//! Bridges between flattened scalar state vars (used in CHC relation signatures)
//! and Datatype values (expected by stub logic). Part of #2874.
//!
//! - **Reconstruct**: flattened fields → Datatype (at stub inputs)
//! - **Decompose**: Datatype → flattened fields (at stub outputs)
//! - **get_collection_arg**: unified entry point for stub call sites

use std::collections::HashSet;

use ay_bindings::{Expr, ExprValue, Sort};
use rustc_public::mir::Operand;
use tracing::warn;

use super::ChcCtx;
use super::codegen_ctx::CollectionProjectionKind;
use super::codegen_types::CodegenTypes;
use super::stubs_option_helpers::OptionHelpers;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Resolve projected flattened slots for a local from input/output state vars.
    fn projected_local_field_exprs(
        &self,
        local_idx: usize,
        field_count: usize,
        modified_locals: &HashSet<usize>,
    ) -> Option<Vec<Expr>> {
        (0..field_count)
            .map(|field_idx| self.flattened_local_field_expr(local_idx, field_idx, modified_locals))
            .collect()
    }

    /// Count the deep-flattened leaf slots for a sort.
    ///
    /// Scalar and Array sorts occupy 1 slot. Datatype sorts are the sum of their
    /// constructor fields' deep flat counts. This matches the deep flattening
    /// performed during state variable declaration.
    ///
    /// Returns 1 for non-Datatype sorts. For Datatypes with no constructors or
    /// fields, returns 0 (defensive — shouldn't happen in practice).
    fn deep_flat_count(sort: &Sort) -> usize {
        if let Some(dt) = sort.datatype_sort() {
            if let Some(ctor) = dt.constructors.first() {
                ctor.fields.iter().map(|f| Self::deep_flat_count(&f.sort)).sum()
            } else {
                0
            }
        } else {
            1
        }
    }

    /// Rebuild a datatype value from deep-flattened field expressions.
    ///
    /// Handles nested Datatypes by recursively reconstructing inner Datatypes
    /// from contiguous ranges of flattened leaf expressions. Part of #3348.
    ///
    /// The `field_exprs` slice must contain exactly `deep_flat_count(datatype_sort)`
    /// elements. For scalar/Array fields, one expression is consumed. For nested
    /// Datatype fields, the appropriate number of expressions is consumed and the
    /// inner Datatype is recursively reconstructed.
    fn reconstruct_datatype_from_deep_flattened(
        &mut self,
        datatype_sort: &Sort,
        field_exprs: &[Expr],
    ) -> Option<Expr> {
        let dt = datatype_sort.datatype_sort()?;
        let ctor = dt.constructors.first()?;

        let expected_count: usize =
            ctor.fields.iter().map(|f| Self::deep_flat_count(&f.sort)).sum();
        if field_exprs.len() != expected_count {
            return None;
        }

        let mut ctor_args = Vec::with_capacity(ctor.fields.len());
        let mut offset = 0;
        for field in &ctor.fields {
            let field_flat_count = Self::deep_flat_count(&field.sort);
            if field.sort.datatype_sort().is_some() {
                // Nested Datatype: recursively reconstruct from the next N leaves.
                let inner_exprs = &field_exprs[offset..offset + field_flat_count];
                let inner =
                    self.reconstruct_datatype_from_deep_flattened(&field.sort, inner_exprs)?;
                ctor_args.push(inner);
            } else {
                // Scalar/Array: single expression, coerce if needed.
                let expr = field_exprs[offset].clone();
                ctor_args.push(self.coerce_value_to_sort(expr, &field.sort, false)?);
            }
            offset += field_flat_count;
        }

        // Part of #2917: ensure the reconstructed sort is declared in the CHC
        // preamble — flattened locals' original sorts are not in state variables.
        self.declare_datatype_sort_if_needed(datatype_sort);

        Some(Expr::datatype_constructor(&*dt.name, &*ctor.name, ctor_args, datatype_sort.clone()))
    }

    /// Reconstruct a deep-flattened `VecIntoIter<T>` (or similar 2-field iterator)
    /// from projected scalar/array slots.
    ///
    /// Handles arbitrary nesting depth: VecIntoIter wraps Vec (2 levels),
    /// Map/Filter adapters wrap SliceIter which wraps Slice (3 levels), etc.
    /// Uses `deep_flat_count` to determine the correct number of leaf slots.
    ///
    /// Layout: first field's deep-flat leaves, then second field's deep-flat leaves.
    fn reconstruct_projected_vec_into_iter_arg(
        &mut self,
        local_idx: usize,
        iter_sort: Sort,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        let total_deep_count = Self::deep_flat_count(&iter_sort);
        let projected_fields =
            self.projected_local_field_exprs(local_idx, total_deep_count, modified_locals)?;
        self.reconstruct_datatype_from_deep_flattened(&iter_sort, &projected_fields)
    }

    /// Decompose a Datatype expression into flattened field values for a
    /// projected collection/iterator local.
    ///
    /// Part of #2874 Step 3: inverse of `reconstruct_projected_collection_arg`.
    /// Used when an iterator adapter produces an updated Datatype iterator value
    /// that must be written back to flattened scalar state vars at emission.
    ///
    /// For `VecIntoIter`: deep-decomposes through the nested Vec carrier,
    /// producing `[vec.fld0, vec.fld1, ..., vec.fldN-1, iter.fld_pos]`.
    /// For other types: simple field_select for each top-level field.
    pub(in crate::codegen_ay::chc) fn decompose_projected_iterator_to_fields(
        &self,
        iter_expr: &Expr,
        kind: CollectionProjectionKind,
    ) -> Option<Vec<Option<Expr>>> {
        let dt = iter_expr.sort().datatype_sort()?;
        let ctor = dt.constructors.first()?;

        match kind {
            CollectionProjectionKind::VecIntoIter => {
                if let ExprValue::DatatypeConstructor { .. } = iter_expr.value() {
                    let mut fields = Vec::new();
                    super::super::stmt::codegen_stmt_flatten::collect_leaf_exprs(
                        iter_expr,
                        &mut fields,
                    );
                    return Some(fields);
                }
                // Deep decomposition: Vec carrier inner fields + iterator pos.
                // Layout: [vec.fld0, vec.fld1, ..., vec.fldN-1, iter.fld_pos]
                if ctor.fields.len() < 2 {
                    return None;
                }
                let vec_field = &ctor.fields[0];
                let pos_field = &ctor.fields[1];

                let vec_expr = iter_expr.clone().field_select(
                    &*dt.name,
                    &*vec_field.name,
                    vec_field.sort.clone(),
                );

                // Recursively decompose the inner field if it's a Datatype.
                let mut fields = self.deep_decompose_to_leaves(&vec_expr)?;

                // Append the iterator position field.
                fields.push(Some(iter_expr.clone().field_select(
                    &*dt.name,
                    &*pos_field.name,
                    pos_field.sort.clone(),
                )));
                Some(fields)
            }
            CollectionProjectionKind::ArrayIntoIter | CollectionProjectionKind::IteratorWrapper => {
                // Part of #3711: Array IntoIter deep decomposition.
                // Part of #4114: IteratorWrapper uses same generic deep decomposition.
                // Deep-flatten to leaves through all single-constructor nesting.
                self.deep_decompose_to_leaves(iter_expr)
            }
            CollectionProjectionKind::Vec
            | CollectionProjectionKind::HashMapIntoIter
            | CollectionProjectionKind::HashSetIntoIter => {
                let fields: Vec<Option<Expr>> = ctor
                    .fields
                    .iter()
                    .map(|f| {
                        Some(iter_expr.clone().field_select(&*dt.name, &*f.name, f.sort.clone()))
                    })
                    .collect();
                Some(fields)
            }
        }
    }

    /// Deep-decompose a Datatype expression into leaf field expressions.
    ///
    /// For scalar/Array fields, produces the field_select expression directly.
    /// For nested Datatype fields, recursively decomposes into leaf fields.
    /// Part of #3348: supports arbitrary nesting (Map wraps SliceIter wraps Slice).
    fn deep_decompose_to_leaves(&self, expr: &Expr) -> Option<Vec<Option<Expr>>> {
        let dt = expr.sort().datatype_sort()?;
        let ctor = dt.constructors.first()?;

        let mut leaves = Vec::new();
        for field in &ctor.fields {
            let field_expr = expr.clone().field_select(&*dt.name, &*field.name, field.sort.clone());
            if field.sort.datatype_sort().is_some() {
                // Nested Datatype: recursively decompose.
                leaves.extend(self.deep_decompose_to_leaves(&field_expr)?);
            } else {
                // Scalar/Array leaf.
                leaves.push(Some(field_expr));
            }
        }
        Some(leaves)
    }

    /// Reconstruct an ephemeral datatype value for projected collection/iterator locals.
    ///
    /// Part of #2874 Step 2: bridge flattened CHC state vars back into datatype
    /// terms at stub call sites that expect datatype collection arguments.
    pub(in crate::codegen_ay::chc) fn reconstruct_projected_collection_arg(
        &mut self,
        local_idx: usize,
        kind: CollectionProjectionKind,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        let local_sort = Self::translate_ty(self.body.locals().get(local_idx)?.ty)?;
        match kind {
            CollectionProjectionKind::VecIntoIter => {
                self.reconstruct_projected_vec_into_iter_arg(local_idx, local_sort, modified_locals)
            }
            CollectionProjectionKind::ArrayIntoIter | CollectionProjectionKind::IteratorWrapper => {
                // Part of #3711: Array IntoIter reconstruction from deep-flattened leaves.
                // Part of #4114: IteratorWrapper uses same generic deep reconstruction.
                let deep_count = Self::deep_flat_count(&local_sort);
                let field_exprs =
                    self.projected_local_field_exprs(local_idx, deep_count, modified_locals)?;
                self.reconstruct_datatype_from_deep_flattened(&local_sort, &field_exprs)
            }
            CollectionProjectionKind::Vec
            | CollectionProjectionKind::HashMapIntoIter
            | CollectionProjectionKind::HashSetIntoIter => {
                let deep_count = Self::deep_flat_count(&local_sort);
                let field_exprs =
                    self.projected_local_field_exprs(local_idx, deep_count, modified_locals)?;
                self.reconstruct_datatype_from_deep_flattened(&local_sort, &field_exprs)
            }
        }
    }

    /// Gets a collection-related argument value, resolving references if needed.
    ///
    /// Used for Vec, VecIntoIter, and other collection arguments that may be
    /// passed by reference or value. Consolidated from get_vec_arg/get_vec_iter_arg.
    pub(in crate::codegen_ay::chc) fn get_collection_arg(
        &mut self,
        operand: &Operand,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        if let Operand::Copy(place) | Operand::Move(place) = operand {
            if !place.projection.is_empty() {
                return self.translate_operand_with_modified(operand, modified_locals);
            }
            let ref_local: usize = place.local;
            let target_local =
                self.ref_resolution.ref_targets.get(&ref_local).map_or(ref_local, |rt| rt.local);

            if let Some(kind) = self.collections.projection_locals.get(&target_local).copied() {
                if let Some(expr) =
                    self.reconstruct_projected_collection_arg(target_local, kind, modified_locals)
                {
                    return Some(expr);
                }
                warn!(
                    target_local,
                    ?kind,
                    "CHC: projected collection local reconstruction failed; falling back"
                );
                return self.translate_operand_with_modified(operand, modified_locals);
            }

            // Fix #2241: Use local_to_state_idx mapping for correct vector index.
            // After tuple/struct flattening, MIR local indices no longer match
            // state_vars vector indices 1:1.
            let Some(vec_idx) = self.try_state_idx_for_local(target_local) else {
                return self.translate_operand_with_modified(operand, modified_locals);
            };

            if modified_locals.contains(&target_local)
                && let Some((out_name, out_sort)) =
                    self.state_var_mgr.output_state_vars.get(vec_idx)
            {
                return Some(Expr::var(&**out_name, out_sort.clone()));
            }
            if let Some((in_name, in_sort)) = self.state_var_mgr.state_vars.get(vec_idx) {
                return Some(Expr::var(&**in_name, in_sort.clone()));
            }
        }
        self.translate_operand_with_modified(operand, modified_locals)
    }
}
