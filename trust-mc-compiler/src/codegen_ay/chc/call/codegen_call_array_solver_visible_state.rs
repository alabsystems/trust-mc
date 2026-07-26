// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Visible receiver-shape updates for `ArraySolver` shadow dispatch.
//!
//! Shadow arrays carry the proof-critical semantics, but a subset of the tier3
//! arrays harnesses still read `scopes`, trail lengths, and `dirty` directly
//! from the visible `ArraySolver` struct. These helpers keep those fields
//! aligned with the shadow model without re-entering the loop-heavy method
//! bodies that originally caused the PDR regressions.

// These helpers are called from the shadow dispatch methods submodule
// (codegen_call_array_solver_shadow/methods.rs) which is not yet wired
// into the module root. Allow dead code until the submodule split lands.
#![allow(dead_code)]

use std::collections::HashSet;

use ay_bindings::{Expr, Sort};

use super::ChcCtx;
use super::FieldProjection;
use super::codegen_call_vec::ChcVecFields;
use super::codegen_call_vec_element_pop_struct_array_solver::{
    ARRAYSOLVER_FIELD_SCOPES, ARRAYSOLVER_FIELD_TRAIL_PREV_PRESENT,
    ARRAYSOLVER_FIELD_TRAIL_PREV_VALUES, ARRAYSOLVER_FIELD_TRAIL_TERMS,
};
use super::codegen_ctx::types::CollectionProjectionKind;
use super::codegen_decl_flatten::collect_leaf_sorts;
use crate::codegen_ay::names::vec_layout;
use crate::codegen_ay::types::POINTER_WIDTH;

const ARRAYSOLVER_FIELD_DIRTY: usize = 6;

mod mutations;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    fn array_solver_field_projection(field_idx: usize) -> [FieldProjection; 1] {
        [FieldProjection { field_idx, cons_idx: None, field_ty: None }]
    }

    fn constrain_array_solver_field_sidecars(
        &mut self,
        struct_local: usize,
        field_idx: usize,
        new_len: Expr,
        new_cap: Option<Expr>,
        constraints: &mut Vec<Expr>,
    ) {
        let mut seen_len_vars = HashSet::new();
        let mut seen_cap_vars = HashSet::new();
        for proj_local in
            self.find_struct_field_projection_locals_for_field(struct_local, field_idx)
        {
            if let Some(len_var) = self.collections.len_state.get_len_var(proj_local).cloned()
                && seen_len_vars.insert(len_var.clone())
                && let Some(idx) = self.state_var_index_by_name(&len_var)
            {
                let (out_name, out_sort) = self.state_var_mgr.output_state_vars[idx].clone();
                let Some(value) = Self::coerce_flatten_slot_value(&out_sort, new_len.clone())
                else {
                    continue;
                };
                constraints.push(Expr::var(&*out_name, out_sort).eq(value));
                self.mark_collection_len_modified(&len_var);
            }
            if let Some(cap_expr) = new_cap.clone()
                && let Some(cap_var) = self.collections.len_state.get_cap_var(proj_local).cloned()
                && seen_cap_vars.insert(cap_var.clone())
                && let Some(idx) = self.state_var_index_by_name(&cap_var)
            {
                let (out_name, out_sort) = self.state_var_mgr.output_state_vars[idx].clone();
                let Some(value) = Self::coerce_flatten_slot_value(&out_sort, cap_expr) else {
                    continue;
                };
                constraints.push(Expr::var(&*out_name, out_sort).eq(value));
                self.mark_collection_cap_modified(&cap_var);
            }
        }
    }

    fn constrain_array_solver_projected_vec_field(
        &mut self,
        struct_local: usize,
        field_idx: usize,
        values: &[Option<Expr>],
        base: usize,
        constraints: &mut Vec<Expr>,
    ) {
        let projected_values = [
            values.get(base + vec_layout::IDX_PTR).cloned().flatten(),
            values.get(base + vec_layout::IDX_LEN).cloned().flatten(),
            values.get(base + vec_layout::IDX_CAP).cloned().flatten(),
            values.get(base + vec_layout::IDX_DATA).cloned().flatten(),
        ];
        if projected_values.iter().all(Option::is_none) {
            return;
        }

        let mut seen = HashSet::new();
        for proj_local in
            self.find_struct_field_projection_locals_for_field(struct_local, field_idx)
        {
            if !seen.insert(proj_local) {
                continue;
            }
            if self.collections.projection_locals.get(&proj_local).copied()
                != Some(CollectionProjectionKind::Vec)
            {
                continue;
            }
            if let Some(vec_idx) = self.try_state_idx_for_local(proj_local) {
                for (offset, value) in projected_values.iter().enumerate() {
                    if value.is_some() {
                        self.mark_state_var_modified(vec_idx + offset);
                    }
                }
            }
            let _ = self.constrain_flattened_fields_for_call(
                proj_local,
                &projected_values,
                constraints,
            );
        }
    }

    fn flattened_array_solver_state_var_fields(
        &self,
        receiver_local: usize,
        total_leaves: usize,
    ) -> Option<Vec<Option<Expr>>> {
        let base_idx = self.try_state_idx_for_local(receiver_local)?;
        Some(
            (0..total_leaves)
                .map(|idx| {
                    self.state_var_mgr
                        .state_vars
                        .get(base_idx + idx)
                        .map(|(name, sort)| Expr::var(&**name, sort.clone()))
                })
                .collect(),
        )
    }

    fn rebuild_vec_expr(
        vec_sort: Sort,
        ptr: Expr,
        len: Expr,
        cap: Expr,
        data: Expr,
    ) -> Option<Expr> {
        let dt_name = vec_sort.datatype_name()?.to_owned();
        let ctor_name = crate::codegen_ay::names::cons_name(&dt_name);
        Some(Expr::datatype_constructor(&dt_name, ctor_name, vec![ptr, len, cap, data], vec_sort))
    }

    fn rebuild_vec_with_len(vec_expr: Expr, new_len: Expr) -> Option<Expr> {
        let ChcVecFields { vec_sort, ptr, cap, data, .. } = ChcVecFields::extract(vec_expr)?;
        Self::rebuild_vec_expr(vec_sort, ptr, new_len, cap, data)
    }

    fn constrain_array_solver_receiver_output_expr(
        &mut self,
        receiver_local: usize,
        new_expr: Expr,
        constraints: &mut Vec<Expr>,
    ) -> bool {
        let state_idx = match self.try_state_idx_for_local(receiver_local) {
            Some(idx) => idx,
            None => return false,
        };
        self.mark_state_var_modified(state_idx);
        let (out_name, out_sort) =
            match self.state_var_mgr.output_state_vars.get(state_idx).cloned() {
                Some(pair) => pair,
                None => return false,
            };
        constraints.push(Expr::var(&*out_name, out_sort).eq(new_expr));
        true
    }

    fn constrain_array_solver_alias_output_from_flattened(
        &mut self,
        receiver_local: usize,
        visible_local: usize,
        values: &[Option<Expr>],
        modified_locals: &HashSet<usize>,
        constraints: &mut Vec<Expr>,
    ) -> bool {
        if receiver_local == visible_local {
            return true;
        }
        if self.flatten.flattened_tuple_locals.contains(&receiver_local) {
            if let Some(vec_idx) = self.try_state_idx_for_local(receiver_local) {
                for (offset, value) in values.iter().enumerate() {
                    if value.is_some() {
                        self.mark_state_var_modified(vec_idx + offset);
                    }
                }
            }
            return self.constrain_flattened_fields_for_call(receiver_local, values, constraints);
        }
        let Some(state_idx) = self.try_state_idx_for_local(receiver_local) else {
            return true;
        };
        let Some((_, receiver_sort)) = self.state_var_mgr.state_vars.get(state_idx) else {
            return true;
        };
        if !receiver_sort.is_datatype() {
            return true;
        }
        let updated_struct = match self.reconstruct_flattened_root(visible_local, modified_locals) {
            Some(expr) => expr,
            None => return false,
        };
        self.constrain_array_solver_receiver_output_expr(
            receiver_local,
            updated_struct,
            constraints,
        )
    }

    pub(in crate::codegen_ay::chc::call) fn constrain_visible_array_solver_dirty(
        &mut self,
        receiver_local: usize,
        modified_locals: &HashSet<usize>,
        dirty_value: Expr,
        constraints: &mut Vec<Expr>,
    ) -> bool {
        let visible_local = self.resolve_flattened_array_solver_local(receiver_local);
        if self.flatten.flattened_tuple_locals.contains(&visible_local) {
            // Part of #4050: use the narrow dirty-field-only constraint instead
            // of full constrain_flattened_fields_for_call. The full path reads ALL
            // flattened state var fields (including Array-sorted shadow vars) and
            // pairs them with output slots that may be BV-packed, causing sort
            // mismatches. The narrow path only touches the dirty output var.
            let dirty_bool = dirty_value == Expr::bool_const(true);
            if let Some(constraint) = self.constrain_receiver_dirty_field(visible_local, dirty_bool)
            {
                constraints.push(constraint);
                if receiver_local == visible_local {
                    return true;
                }
                if self.flatten.flattened_tuple_locals.contains(&receiver_local) {
                    if let Some(alias_constraint) =
                        self.constrain_receiver_dirty_field(receiver_local, dirty_bool)
                    {
                        constraints.push(alias_constraint);
                        return true;
                    }
                    return false;
                }
                let dirty_field_idx = self.flattened_field_count(visible_local).saturating_sub(1);
                let mut values = vec![None; self.flattened_field_count(visible_local)];
                if let Some(slot) = values.get_mut(dirty_field_idx) {
                    *slot = Some(if dirty_bool {
                        Expr::bool_const(true)
                    } else {
                        Expr::bool_const(false)
                    });
                }
                return self.constrain_array_solver_alias_output_from_flattened(
                    receiver_local,
                    visible_local,
                    &values,
                    modified_locals,
                    constraints,
                );
            }
            return false;
        }

        let struct_in = match self.try_resolve_local_expr(receiver_local, modified_locals) {
            Some(expr) => expr,
            None => return false,
        };
        let dirty_proj = Self::array_solver_field_projection(ARRAYSOLVER_FIELD_DIRTY);
        let new_struct = match Self::apply_projection_update(&struct_in, &dirty_proj, dirty_value) {
            Some(expr) => expr,
            None => return false,
        };
        self.constrain_array_solver_receiver_output_expr(receiver_local, new_struct, constraints)
    }

    /// Constrain visible (flattened struct) output fields to their input values.
    /// Used by shadow dispatch methods that modify only shadow state but not
    /// the receiver's visible struct. When `skip_last` is true, the last field
    /// (dirty) is excluded — use this when dirty is explicitly constrained elsewhere.
    pub(in crate::codegen_ay::chc::call) fn constrain_receiver_visible_identity(
        &mut self,
        receiver_local: usize,
        skip_last: bool,
        constraints: &mut Vec<Expr>,
    ) -> bool {
        let Some(base_idx) = self.try_state_idx_for_local(receiver_local) else { return false };
        let field_count = self.flattened_field_count(receiver_local);
        if field_count == 0 {
            return false;
        }
        let limit = if skip_last { field_count.saturating_sub(1) } else { field_count };
        for offset in 0..limit {
            let idx = base_idx + offset;
            let Some((in_name, in_sort)) = self.state_var_mgr.state_vars.get(idx).cloned() else {
                continue;
            };
            let Some((out_name, out_sort)) = self.state_var_mgr.output_state_vars.get(idx).cloned()
            else {
                continue;
            };
            if in_sort != out_sort {
                continue;
            }
            constraints.push(Expr::var(&*out_name, out_sort).eq(Expr::var(&*in_name, in_sort)));
            self.mark_state_var_modified(idx);
        }
        true
    }

    /// Find locals that are field projections from `struct_local` in the MIR.
    pub(in crate::codegen_ay::chc::call) fn find_struct_field_projection_locals(
        &self,
        struct_local: usize,
    ) -> Vec<usize> {
        use rustc_public::mir::{Operand, ProjectionElem, Rvalue, StatementKind};
        let mut result = Vec::new();
        let mut ref_locals = std::collections::HashSet::new();

        for block in &self.body.blocks {
            for stmt in &block.statements {
                let StatementKind::Assign(dest, rvalue) = &stmt.kind else { continue };
                if !dest.projection.is_empty() {
                    continue;
                }
                match rvalue {
                    Rvalue::Use(Operand::Copy(src) | Operand::Move(src))
                        if src.local == struct_local
                            && src.projection.len() == 1
                            && matches!(src.projection[0], ProjectionElem::Field(..)) =>
                    {
                        result.push(dest.local);
                    }
                    Rvalue::Ref(_, _, src)
                        if src.local == struct_local
                            && src.projection.len() == 1
                            && matches!(src.projection[0], ProjectionElem::Field(..)) =>
                    {
                        ref_locals.insert(dest.local);
                    }
                    Rvalue::Use(Operand::Copy(src) | Operand::Move(src))
                        if ref_locals.contains(&src.local)
                            && src.projection.len() == 1
                            && matches!(src.projection[0], ProjectionElem::Deref) =>
                    {
                        result.push(dest.local);
                    }
                    _ => {}
                }
            }
        }

        // Include ref locals that have sidecar vars.
        for &ref_local in &ref_locals {
            if self.collections.len_state.get_len_var(ref_local).is_some() {
                result.push(ref_local);
            }
        }

        result
    }

    pub(in crate::codegen_ay::chc) fn find_struct_field_projection_locals_for_field(
        &self,
        struct_local: usize,
        field_idx: usize,
    ) -> Vec<usize> {
        use rustc_public::mir::{
            CastKind, Operand, PointerCoercion, ProjectionElem, Rvalue, StatementKind,
        };
        let mut aliases = std::collections::HashMap::new();
        let mut reverse_aliases = std::collections::HashMap::<usize, Vec<usize>>::new();
        for block in &self.body.blocks {
            for stmt in &block.statements {
                let StatementKind::Assign(dest, rvalue) = &stmt.kind else { continue };
                if !dest.projection.is_empty() {
                    continue;
                }
                match rvalue {
                    Rvalue::Use(Operand::Copy(src) | Operand::Move(src))
                        if src.projection.is_empty() =>
                    {
                        aliases.insert(dest.local, src.local);
                        reverse_aliases.entry(src.local).or_default().push(dest.local);
                    }
                    Rvalue::Cast(
                        CastKind::PointerCoercion(PointerCoercion::Unsize),
                        Operand::Copy(src) | Operand::Move(src),
                        _,
                    ) if src.projection.is_empty() => {
                        aliases.insert(dest.local, src.local);
                        reverse_aliases.entry(src.local).or_default().push(dest.local);
                    }
                    _ => {}
                }
            }
        }
        let mut struct_roots = std::collections::HashSet::from([struct_local]);
        let mut pending = vec![struct_local];
        while let Some(current) = pending.pop() {
            for next_local in aliases
                .get(&current)
                .copied()
                .into_iter()
                .chain(reverse_aliases.get(&current).into_iter().flatten().copied())
                .chain(self.ref_resolution.ref_targets.get(&current).map(|target| target.local))
                .chain(self.resolve_ref_chain_for_array_solver(current))
            {
                if struct_roots.insert(next_local) {
                    pending.push(next_local);
                }
            }
        }
        let mut result = std::collections::HashSet::new();
        let mut ref_locals = std::collections::HashSet::new();
        for block in &self.body.blocks {
            for stmt in &block.statements {
                let StatementKind::Assign(dest, rvalue) = &stmt.kind else { continue };
                if !dest.projection.is_empty() {
                    continue;
                }
                match rvalue {
                    Rvalue::Use(Operand::Copy(src) | Operand::Move(src))
                        if struct_roots.contains(&src.local)
                            && src.projection.len() == 1
                            && matches!(
                                src.projection[0],
                                ProjectionElem::Field(idx, _) if idx == field_idx
                            ) =>
                    {
                        result.insert(dest.local);
                    }
                    Rvalue::Ref(_, _, src)
                        if struct_roots.contains(&src.local)
                            && src.projection.len() == 1
                            && matches!(
                                src.projection[0],
                                ProjectionElem::Field(idx, _) if idx == field_idx
                            ) =>
                    {
                        ref_locals.insert(dest.local);
                    }
                    Rvalue::Use(Operand::Copy(src) | Operand::Move(src))
                        if ref_locals.contains(&src.local)
                            && src.projection.len() == 1
                            && matches!(src.projection[0], ProjectionElem::Deref) =>
                    {
                        result.insert(dest.local);
                    }
                    _ => {}
                }
            }
        }
        for (&ref_local, target) in &self.ref_resolution.ref_targets {
            if struct_roots.contains(&target.local)
                && target.projections.len() == 1
                && matches!(
                    target.projections[0],
                    ProjectionElem::Field(idx, _) if idx == field_idx
                )
            {
                ref_locals.insert(ref_local);
            }
        }
        for &alias_local in aliases.keys() {
            let mut current = alias_local;
            let mut visited = std::collections::HashSet::new();
            while visited.insert(current) {
                if result.contains(&current) || ref_locals.contains(&current) {
                    result.insert(alias_local);
                    break;
                }
                let Some(next_local) = aliases.get(&current).copied() else { break };
                current = next_local;
            }
        }
        for &ref_local in &ref_locals {
            if self.collections.len_state.get_len_var(ref_local).is_some() {
                result.insert(ref_local);
            }
        }
        result.into_iter().collect()
    }
}
