// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! `ArraySolver`-specific collection auxiliary state declarations.
//!
//! Split from `codegen_decl_state_vars_collections.rs` to keep the collection
//! declaration packet under file/function size limits.

use std::sync::Arc;

use ay_bindings::Sort;
use rustc_public::CrateDef;
use rustc_public::ty::{RigidTy, TyKind};
use tracing::debug;

use super::ChcCtx;
use super::codegen_ctx::types::ArraySolverAuxState;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    fn register_array_solver_aux_state_var(&mut self, name: Arc<str>, sort: Sort) -> Arc<str> {
        let out_name = crate::codegen_ay::names::out_name(&name);
        self.push_state_var_pair_arc(Arc::clone(&name), &out_name, sort);
        name
    }

    fn declare_array_solver_aux_vars_for_local(
        &mut self,
        local_idx: usize,
        assign_array_sort: &Sort,
        scope_snap_sort: &Sort,
    ) {
        let fn_name = self.fn_name.clone();

        let assign_present = self.register_array_solver_aux_state_var(
            Arc::from(format!("arraysolver_{fn_name}_assign_present_{local_idx}")),
            assign_array_sort.clone(),
        );
        let assign_value = self.register_array_solver_aux_state_var(
            Arc::from(format!("arraysolver_{fn_name}_assign_value_{local_idx}")),
            assign_array_sort.clone(),
        );
        let scope_snap_present = self.register_array_solver_aux_state_var(
            Arc::from(format!("arraysolver_{fn_name}_scope_snap_present_{local_idx}")),
            scope_snap_sort.clone(),
        );
        let scope_snap_value = self.register_array_solver_aux_state_var(
            Arc::from(format!("arraysolver_{fn_name}_scope_snap_value_{local_idx}")),
            scope_snap_sort.clone(),
        );
        // scope_snap_assign_terms and scope_snap_assign_values are NOT registered
        // as CHC state vars. Shadow dispatch handles all ArraySolver methods using
        // the shadow assign_present/assign_value arrays, so these visible-snapshot
        // vars are never constrained and would increase relation arity needlessly,
        // making PDR's invariant synthesis harder. The names are kept in
        // ArraySolverAuxState for Vec element handlers that gracefully handle
        // missing state vars via state_var_index_by_name() returning None.
        let scope_snap_assign_terms =
            Arc::from(format!("arraysolver_{fn_name}_scope_snap_assign_terms_{local_idx}"));
        let scope_snap_assign_values =
            Arc::from(format!("arraysolver_{fn_name}_scope_snap_assign_values_{local_idx}"));
        let dirty = self.register_array_solver_aux_state_var(
            Arc::from(format!("arraysolver_{fn_name}_dirty_{local_idx}")),
            Sort::bool(),
        );
        let scope_depth = self.register_array_solver_aux_state_var(
            Arc::from(format!("arraysolver_{fn_name}_scope_depth_{local_idx}")),
            Sort::bitvec(64),
        );

        debug!(
            local_idx,
            assign_present = %assign_present,
            assign_value = %assign_value,
            scope_depth = %scope_depth,
            "CHC: declared ArraySolver shadow aux vars (#4050)"
        );

        self.collections.array_solver_aux.insert(
            local_idx,
            ArraySolverAuxState {
                assign_present_var: assign_present,
                assign_value_var: assign_value,
                scope_snap_present_var: scope_snap_present,
                scope_snap_value_var: scope_snap_value,
                scope_snap_assign_terms_var: scope_snap_assign_terms,
                scope_snap_assign_values_var: scope_snap_assign_values,
                dirty_var: dirty,
                scope_depth_var: scope_depth,
            },
        );
    }

    /// Declare shadow auxiliary state variables for `ArraySolver` locals (Part of #4050).
    ///
    /// Declares ONE set of shadow vars for the first ArraySolver local found,
    /// then aliases all other ArraySolver locals to the same aux state.
    /// Harnesses without ArraySolver locals are unaffected (type-based scan
    /// finds no matching locals).
    pub(super) fn declare_array_solver_aux_vars(&mut self) {
        let assign_array_sort = Sort::array(Sort::bitvec(32), Sort::bool());
        let scope_depth_sort = Sort::bitvec(64);
        let scope_snap_sort = Sort::array(scope_depth_sort, assign_array_sort.clone());

        let mut primary_local: Option<usize> = None;

        for (local_idx, local_decl) in self.body.local_decls() {
            let TyKind::RigidTy(RigidTy::Adt(def, _)) = local_decl.ty.kind() else {
                continue;
            };
            if def.trimmed_name() != "ArraySolver" {
                continue;
            }

            if let Some(primary) = primary_local {
                // Alias this local to the primary's aux state.
                if let Some(aux) = self.collections.array_solver_aux.get(&primary).cloned() {
                    debug!(local_idx, primary, "CHC: aliased ArraySolver aux to primary (#4050)");
                    self.collections.array_solver_aux.insert(local_idx, aux);
                }
                continue;
            }

            self.declare_array_solver_aux_vars_for_local(
                local_idx,
                &assign_array_sort,
                &scope_snap_sort,
            );
            primary_local = Some(local_idx);
        }
    }
}
