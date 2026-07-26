// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Shared shadow-state helpers for `ArraySolver` call dispatch.
//!
//! Split out of `codegen_call_array_solver_shadow.rs` to keep the dispatcher
//! packet under the file-size limit while preserving the same helper surface.

use ay_bindings::{Expr, Sort};

use super::ChcCtx;
use crate::codegen_ay::chc::codegen_ctx::types::ArraySolverAuxState;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Mark all shadow auxiliary state variables as modified so `build_output_args`
    /// uses `__out` vars in the successor relation head.
    pub(in crate::codegen_ay::chc::call) fn mark_array_solver_shadow_modified(
        &mut self,
        aux: &ArraySolverAuxState,
    ) {
        for name in [
            &aux.assign_present_var,
            &aux.assign_value_var,
            &aux.scope_snap_present_var,
            &aux.scope_snap_value_var,
            &aux.dirty_var,
            &aux.scope_depth_var,
        ] {
            if let Some(idx) = self.state_var_index_by_name(name) {
                self.mark_state_var_modified(idx);
            }
        }
    }

    pub(in crate::codegen_ay::chc::call) fn shadow_assign_present(
        &self,
        aux: &ArraySolverAuxState,
    ) -> Expr {
        Expr::var(&*aux.assign_present_var, Sort::array(Sort::bitvec(32), Sort::bool()))
    }

    pub(in crate::codegen_ay::chc::call) fn shadow_assign_value(
        &self,
        aux: &ArraySolverAuxState,
    ) -> Expr {
        Expr::var(&*aux.assign_value_var, Sort::array(Sort::bitvec(32), Sort::bool()))
    }

    pub(in crate::codegen_ay::chc::call) fn shadow_scope_snap_present(
        &self,
        aux: &ArraySolverAuxState,
    ) -> Expr {
        let inner = Sort::array(Sort::bitvec(32), Sort::bool());
        Expr::var(&*aux.scope_snap_present_var, Sort::array(Sort::bitvec(64), inner))
    }

    pub(in crate::codegen_ay::chc::call) fn shadow_scope_snap_value(
        &self,
        aux: &ArraySolverAuxState,
    ) -> Expr {
        let inner = Sort::array(Sort::bitvec(32), Sort::bool());
        Expr::var(&*aux.scope_snap_value_var, Sort::array(Sort::bitvec(64), inner))
    }

    pub(in crate::codegen_ay::chc::call) fn shadow_assign_present_out(
        &self,
        aux: &ArraySolverAuxState,
    ) -> Expr {
        let out = crate::codegen_ay::names::out_name(&aux.assign_present_var);
        Expr::var(&*out, Sort::array(Sort::bitvec(32), Sort::bool()))
    }

    pub(in crate::codegen_ay::chc::call) fn shadow_assign_value_out(
        &self,
        aux: &ArraySolverAuxState,
    ) -> Expr {
        let out = crate::codegen_ay::names::out_name(&aux.assign_value_var);
        Expr::var(&*out, Sort::array(Sort::bitvec(32), Sort::bool()))
    }

    pub(in crate::codegen_ay::chc::call) fn shadow_scope_snap_present_out(
        &self,
        aux: &ArraySolverAuxState,
    ) -> Expr {
        let inner = Sort::array(Sort::bitvec(32), Sort::bool());
        let out = crate::codegen_ay::names::out_name(&aux.scope_snap_present_var);
        Expr::var(&*out, Sort::array(Sort::bitvec(64), inner))
    }

    pub(in crate::codegen_ay::chc::call) fn shadow_scope_snap_value_out(
        &self,
        aux: &ArraySolverAuxState,
    ) -> Expr {
        let inner = Sort::array(Sort::bitvec(32), Sort::bool());
        let out = crate::codegen_ay::names::out_name(&aux.scope_snap_value_var);
        Expr::var(&*out, Sort::array(Sort::bitvec(64), inner))
    }

    pub(in crate::codegen_ay::chc::call) fn shadow_dirty(&self, aux: &ArraySolverAuxState) -> Expr {
        Expr::var(&*aux.dirty_var, Sort::bool())
    }

    pub(in crate::codegen_ay::chc::call) fn shadow_dirty_out(
        &self,
        aux: &ArraySolverAuxState,
    ) -> Expr {
        let out = crate::codegen_ay::names::out_name(&aux.dirty_var);
        Expr::var(&*out, Sort::bool())
    }

    pub(in crate::codegen_ay::chc::call) fn shadow_scope_depth(
        &self,
        aux: &ArraySolverAuxState,
    ) -> Expr {
        Expr::var(&*aux.scope_depth_var, Sort::bitvec(64))
    }

    pub(in crate::codegen_ay::chc::call) fn shadow_scope_depth_out(
        &self,
        aux: &ArraySolverAuxState,
    ) -> Expr {
        let out = crate::codegen_ay::names::out_name(&aux.scope_depth_var);
        Expr::var(&*out, Sort::bitvec(64))
    }

    /// Emit shadow identity constraints (all shadow vars unchanged).
    pub(in crate::codegen_ay::chc::call) fn shadow_identity_constraints(
        &self,
        aux: &ArraySolverAuxState,
    ) -> Vec<Expr> {
        vec![
            self.shadow_assign_present_out(aux).eq(self.shadow_assign_present(aux)),
            self.shadow_assign_value_out(aux).eq(self.shadow_assign_value(aux)),
            self.shadow_scope_snap_present_out(aux).eq(self.shadow_scope_snap_present(aux)),
            self.shadow_scope_snap_value_out(aux).eq(self.shadow_scope_snap_value(aux)),
            self.shadow_dirty_out(aux).eq(self.shadow_dirty(aux)),
            self.shadow_scope_depth_out(aux).eq(self.shadow_scope_depth(aux)),
        ]
    }

    /// Shadow identity for assign/snapshot arrays only (dirty handled separately).
    pub(in crate::codegen_ay::chc::call) fn shadow_array_identity_constraints(
        &self,
        aux: &ArraySolverAuxState,
    ) -> Vec<Expr> {
        vec![
            self.shadow_assign_present_out(aux).eq(self.shadow_assign_present(aux)),
            self.shadow_assign_value_out(aux).eq(self.shadow_assign_value(aux)),
            self.shadow_scope_snap_present_out(aux).eq(self.shadow_scope_snap_present(aux)),
            self.shadow_scope_snap_value_out(aux).eq(self.shadow_scope_snap_value(aux)),
        ]
    }

    /// Narrow constraint: set only the receiver's flattened `dirty` output field.
    ///
    /// The dirty field is the LAST leaf in the flattened ArraySolver struct.
    /// This avoids over-constraining all flattened fields (which the broad
    /// `constrain_visible_*` functions do and which causes CTREX regressions).
    pub(in crate::codegen_ay::chc::call) fn constrain_receiver_dirty_field(
        &mut self,
        receiver_local: usize,
        value: bool,
    ) -> Option<Expr> {
        let vec_idx = self.try_state_idx_for_local(receiver_local)?;
        let field_count = self.flattened_field_count(receiver_local);
        if field_count < 2 {
            return None;
        }

        let dirty_idx = vec_idx + field_count - 1;
        let (out_name, out_sort) = self.state_var_mgr.output_state_vars.get(dirty_idx).cloned()?;
        // Guard: the dirty field must be Bool or small BV (not Array/Datatype).
        // Shadow auxiliary state vars may extend the flattened field count, causing
        // dirty_idx to land on an Array-sorted shadow var instead of the actual
        // dirty field. Bail gracefully if the sort is incompatible.
        if out_sort.is_array() || out_sort.is_datatype() {
            return None;
        }
        self.mark_state_var_modified(dirty_idx);
        let out_var = Expr::var(&*out_name, out_sort.clone());
        let val_expr = if out_sort == Sort::bool() {
            Expr::bool_const(value)
        } else {
            Expr::bitvec_const(
                if value { 1u64 } else { 0u64 },
                out_sort.bitvec_width().unwrap_or(8),
            )
        };
        self.encode.flattened_field_env.insert((receiver_local, field_count - 1), val_expr.clone());
        Some(out_var.eq(val_expr))
    }

    /// Collect entry-rule constraints that initialize all ArraySolver shadow
    /// state vars to "empty" values (Part of #4050).
    ///
    /// Called from `emit_entry_rule` so that the shadow state is well-defined
    /// before any shadow-dispatched method fires. `new()` is handled by
    /// fn_inline (visible state), so shadow state must be initialized here.
    pub(in crate::codegen_ay::chc) fn collect_array_solver_entry_constraints(
        &mut self,
        constraints: &mut Vec<Expr>,
    ) {
        // Deduplicate: all locals share the same aux state (aliased), so
        // collect unique aux var names to avoid duplicate constraints.
        let mut seen = std::collections::HashSet::new();
        for aux in self.collections.array_solver_aux.values() {
            if !seen.insert(aux.assign_present_var.clone()) {
                continue; // Already emitted for this aux set.
            }

            // Look up each shadow var by name and use its ACTUAL registered sort.
            // The declared sort may differ from the hardcoded Array sort (e.g.,
            // BV128 packing in the state var manager). Sort mismatches cause
            // panics in Expr::eq.
            let emit_init =
                |name: &str,
                 make_value: &dyn Fn(&Sort) -> Option<Expr>,
                 constraints: &mut Vec<Expr>,
                 state_vars: &[(std::sync::Arc<str>, Sort)]| {
                    if let Some(idx) = state_vars.iter().position(|(n, _)| &**n == name) {
                        let (ref n, ref s) = state_vars[idx];
                        if let Some(val) = make_value(s) {
                            constraints.push(Expr::var(&**n, s.clone()).eq(val));
                        }
                    }
                };

            let state_vars = &self.state_var_mgr.state_vars;

            // assign_present = all-false (no assignments)
            emit_init(
                &aux.assign_present_var,
                &|sort| {
                    if sort.is_array() {
                        Some(Expr::const_array(Sort::bitvec(32), Expr::bool_const(false)))
                    } else {
                        // BV-packed representation: zero means all-false
                        sort.bitvec_width().map(|w| Expr::bitvec_const(0u64, w))
                    }
                },
                constraints,
                state_vars,
            );

            // assign_value = all-false (default values)
            emit_init(
                &aux.assign_value_var,
                &|sort| {
                    if sort.is_array() {
                        Some(Expr::const_array(Sort::bitvec(32), Expr::bool_const(false)))
                    } else {
                        sort.bitvec_width().map(|w| Expr::bitvec_const(0u64, w))
                    }
                },
                constraints,
                state_vars,
            );

            // scope_depth = 0 (no scopes pushed)
            emit_init(
                &aux.scope_depth_var,
                &|sort| {
                    if *sort == Sort::bitvec(64) {
                        Some(Expr::bitvec_const(0u64, 64))
                    } else {
                        sort.bitvec_width().map(|w| Expr::bitvec_const(0u64, w))
                    }
                },
                constraints,
                state_vars,
            );

            // dirty = true (ArraySolver::new() sets dirty = true)
            emit_init(
                &aux.dirty_var,
                &|sort| {
                    if *sort == Sort::bool() {
                        Some(Expr::bool_const(true))
                    } else {
                        sort.bitvec_width().map(|w| Expr::bitvec_const(1u64, w))
                    }
                },
                constraints,
                state_vars,
            );
        }

        // Zero Vec sidecar len/cap vars for locals that project from ArraySolver
        // struct locals. fn_inline handles ArraySolver::new() struct construction
        // but doesn't propagate empty-Vec initialization to projection sidecar vars.
        // Part of #4050: fixes constructor probe SAT from unconstrained sidecars.
        let zero = Expr::bitvec_const(0u64, crate::codegen_ay::types::POINTER_WIDTH);
        let mut zeroed_sidecars = std::collections::HashSet::new();
        for &struct_local in self.collections.array_solver_aux.keys() {
            // Find locals that project Vec fields from this ArraySolver struct.
            let projection_locals = self.find_struct_field_projection_locals(struct_local);
            for proj_local in projection_locals {
                if let Some(len_var) = self.collections.len_state.get_len_var(proj_local).cloned() {
                    if zeroed_sidecars.insert(len_var.clone()) {
                        if let Some(idx) = self.state_var_index_by_name(&len_var) {
                            let (name, sort) = &self.state_var_mgr.state_vars[idx];
                            constraints.push(Expr::var(&**name, sort.clone()).eq(zero.clone()));
                        }
                    }
                }
                if let Some(cap_var) = self.collections.len_state.get_cap_var(proj_local).cloned() {
                    if zeroed_sidecars.insert(cap_var.clone()) {
                        if let Some(idx) = self.state_var_index_by_name(&cap_var) {
                            let (name, sort) = &self.state_var_mgr.state_vars[idx];
                            constraints.push(Expr::var(&**name, sort.clone()).eq(zero.clone()));
                        }
                    }
                }
            }
        }
    }

    /// Constrain all flattened output fields of `dest_local` to zero/false values.
    /// The dirty field (last Bool leaf) is set to `true` (matching ArraySolver::new()).
    /// Used by the `new()` constructor shadow dispatch to prevent unconstrained
    /// fld vars from corrupting downstream ghost propagation (#4050).
    pub(in crate::codegen_ay::chc::call) fn constrain_all_flattened_fields_to_zero(
        &mut self,
        dest_local: usize,
        constraints: &mut Vec<Expr>,
    ) -> bool {
        let Some(base_idx) = self.try_state_idx_for_local(dest_local) else { return false };
        let field_count = self.flattened_field_count(dest_local);
        if field_count < 2 {
            return false;
        }
        let dirty_field_offset = field_count.saturating_sub(1);
        for offset in 0..field_count {
            let idx = base_idx + offset;
            let Some((out_name, out_sort)) = self.state_var_mgr.output_state_vars.get(idx).cloned()
            else {
                continue;
            };
            let zero_val = if out_sort.is_bitvec() {
                Expr::bitvec_const(0u64, out_sort.bitvec_width().unwrap_or(64))
            } else if out_sort.is_bool() {
                // dirty field = true (ArraySolver::new() sets dirty = true)
                Expr::bool_const(offset == dirty_field_offset)
            } else if out_sort.is_array() {
                if let Some(arr) = out_sort.array_sort() {
                    let elem = &arr.element_sort;
                    if elem.is_bitvec() {
                        Expr::const_array(
                            arr.index_sort.clone(),
                            Expr::bitvec_const(0u64, elem.bitvec_width().unwrap_or(32)),
                        )
                    } else if elem.is_bool() {
                        Expr::const_array(arr.index_sort.clone(), Expr::bool_const(false))
                    } else {
                        continue;
                    }
                } else {
                    continue;
                }
            } else {
                continue;
            };
            constraints.push(Expr::var(&*out_name, out_sort).eq(zero_val));
            self.mark_state_var_modified(idx);
        }
        true
    }

    /// Zero all Vec sidecar (len/cap) vars for locals that project from `struct_local`.
    /// Complements `constrain_all_flattened_fields_to_zero` which handles the
    /// flattened struct fields but not the separate sidecar tracking vars.
    /// Zero ALL Vec sidecar (len/cap) state vars. Used by `ArraySolver::new()`
    /// to initialize all Vecs to empty. Part of #4050.
    pub(in crate::codegen_ay::chc::call) fn zero_struct_vec_sidecars(
        &mut self,
        _struct_local: usize,
        constraints: &mut Vec<Expr>,
    ) {
        let zero = Expr::bitvec_const(0u64, crate::codegen_ay::types::POINTER_WIDTH);
        let all_sidecar_vars: Vec<_> = self
            .collections
            .len_state
            .len_var_names
            .values()
            .chain(self.collections.len_state.cap_var_names.values())
            .cloned()
            .collect();
        for var_name in &all_sidecar_vars {
            if let Some(idx) = self.state_var_index_by_name(var_name) {
                let (out_name, out_sort) = self.state_var_mgr.output_state_vars[idx].clone();
                constraints.push(Expr::var(&*out_name, out_sort).eq(zero.clone()));
                self.mark_state_var_modified(idx);
            }
        }
    }

    /// Pin ALL Vec sidecar (len/cap) state vars to their input values.
    /// Part of #4050: shadow dispatch fully models ArraySolver methods via
    /// SMT arrays. The underlying Vecs are never modified by these methods,
    /// so ALL sidecar vars must be identity-pinned.
    pub(in crate::codegen_ay::chc::call) fn identity_struct_vec_sidecars(
        &mut self,
        _struct_local: usize,
        constraints: &mut Vec<Expr>,
    ) {
        let all_sidecar_vars: Vec<_> = self
            .collections
            .len_state
            .len_var_names
            .values()
            .chain(self.collections.len_state.cap_var_names.values())
            .cloned()
            .collect();
        for var_name in &all_sidecar_vars {
            if let Some(idx) = self.state_var_index_by_name(var_name) {
                let (in_name, in_sort) = self.state_var_mgr.state_vars[idx].clone();
                let (out_name, out_sort) = self.state_var_mgr.output_state_vars[idx].clone();
                if in_sort == out_sort {
                    constraints
                        .push(Expr::var(&*out_name, out_sort).eq(Expr::var(&*in_name, in_sort)));
                    self.mark_state_var_modified(idx);
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::codegen_ay::chc::ChcConfig;
    use crate::codegen_ay::context::with_test_ay_ctx_for_source;
    use crate::codegen_ay::test_fixtures::find_instance_by_suffix;
    use rustc_public::CrateDef;
    use rustc_public::mir::TerminatorKind;
    use rustc_public::ty::{RigidTy, TyKind};

    const ARRAYSOLVER_TRAIL_TERMS_LEN_FIELD: usize = 9;
    const ARRAYSOLVER_SCOPES_LEN_FIELD: usize = 21;

    const SHADOW_STATE_SOURCE: &str = r#"
        #![allow(dead_code)]
        extern crate alloc;

        use alloc::vec::Vec;

        type TermId = u32;

        struct ArraySolver {
            assign_terms: Vec<TermId>,
            assign_values: Vec<bool>,
            trail_terms: Vec<TermId>,
            trail_prev_present: Vec<bool>,
            trail_prev_values: Vec<bool>,
            scopes: Vec<usize>,
            dirty: bool,
        }

        impl ArraySolver {
            fn new() -> Self {
                Self {
                    assign_terms: Vec::new(),
                    assign_values: Vec::new(),
                    trail_terms: Vec::new(),
                    trail_prev_present: Vec::new(),
                    trail_prev_values: Vec::new(),
                    scopes: Vec::new(),
                    dirty: true,
                }
            }
        }

        pub fn probe_arrays_new_scopes_len_assert() {
            let solver = ArraySolver::new();
            assert_eq!(solver.scopes.len(), 0);
        }

        pub fn probe_arrays_new_preserves_other_vec_len_assert() {
            let mut other: Vec<u8> = Vec::new();
            other.push(7);

            let solver = ArraySolver::new();

            assert_eq!(solver.scopes.len(), 0);
            assert_eq!(other.len(), 1);
        }
    "#;

    fn with_constructor_ctx<T: Send>(
        fn_name: &str,
        f: impl FnOnce(&mut ChcCtx<'_, '_>, &rustc_public::mir::Body, usize) -> T + Send,
    ) -> T {
        let mut result = None;
        with_test_ay_ctx_for_source(SHADOW_STATE_SOURCE, |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, fn_name);
            let body = instance.body().expect("function body");
            let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, ChcConfig::default());
            chc_ctx.declare_block_relations();
            let dest_local = body
                .blocks
                .iter()
                .find_map(|block| {
                    let TerminatorKind::Call { func, destination, .. } = &block.terminator.kind
                    else {
                        return None;
                    };
                    let path = chc_ctx
                        .resolve_callee_path(func)
                        .or_else(|| chc_ctx.resolve_fn_def_name(func))?;
                    path.ends_with("ArraySolver::new").then_some(destination.local)
                })
                .expect("expected ArraySolver::new call");
            result = Some(f(&mut chc_ctx, &body, dest_local));
        });
        result.expect("constructor fixture should produce a value")
    }

    #[test]
    fn test_constrain_all_flattened_fields_to_zero_zeroes_len_slots() {
        with_constructor_ctx("probe_arrays_new_scopes_len_assert", |chc_ctx, _body, dest_local| {
            let base_idx =
                chc_ctx.try_state_idx_for_local(dest_local).expect("constructor destination idx");
            let dirty_offset = chc_ctx.flattened_field_count(dest_local).saturating_sub(1);
            let mut constraints = Vec::new();

            assert!(
                chc_ctx.constrain_all_flattened_fields_to_zero(dest_local, &mut constraints),
                "constructor destination should have flattened fields"
            );

            let zero =
                Expr::bitvec_const(0u64, crate::codegen_ay::types::POINTER_WIDTH).to_string();
            for field_offset in [ARRAYSOLVER_TRAIL_TERMS_LEN_FIELD, ARRAYSOLVER_SCOPES_LEN_FIELD] {
                let out_name = &chc_ctx.state_var_mgr.output_state_vars[base_idx + field_offset].0;
                let expected = format!("(= {out_name} {zero})");
                assert!(
                    constraints.iter().any(|c| c.to_string() == expected),
                    "flattened constructor helper should zero visible len slot {out_name}"
                );
            }

            let dirty_out = &chc_ctx.state_var_mgr.output_state_vars[base_idx + dirty_offset].0;
            let expected_dirty = format!("(= {dirty_out} true)");
            assert!(
                constraints.iter().any(|c| c.to_string() == expected_dirty),
                "flattened constructor helper should set the dirty field true"
            );
        });
    }

    #[test]
    fn test_identity_struct_vec_sidecars_pins_other_vec_to_input() {
        with_constructor_ctx(
            "probe_arrays_new_preserves_other_vec_len_assert",
            |chc_ctx, body, dest_local| {
                let other_vec_local = body
                    .locals()
                    .iter()
                    .enumerate()
                    .find_map(|(local_idx, decl)| {
                        if local_idx == 0
                            || local_idx == dest_local
                            || chc_ctx.collections.array_solver_aux.contains_key(&local_idx)
                        {
                            return None;
                        }
                        match chc_ctx.resolve_body_ty(decl.ty).kind() {
                            TyKind::RigidTy(RigidTy::Adt(def, _))
                                if def.trimmed_name() == "Vec"
                                    && chc_ctx
                                        .collections
                                        .len_state
                                        .get_len_var(local_idx)
                                        .is_some() =>
                            {
                                Some(local_idx)
                            }
                            _ => None,
                        }
                    })
                    .expect("expected standalone Vec local with sidecar vars");

                let len_var = chc_ctx
                    .collections
                    .len_state
                    .get_len_var(other_vec_local)
                    .expect("other Vec len var")
                    .clone();
                let cap_var = chc_ctx
                    .collections
                    .len_state
                    .get_cap_var(other_vec_local)
                    .expect("other Vec cap var")
                    .clone();

                let mut constraints = Vec::new();
                chc_ctx.identity_struct_vec_sidecars(dest_local, &mut constraints);

                for var_name in [len_var, cap_var] {
                    let idx =
                        chc_ctx.state_var_index_by_name(&var_name).expect("sidecar state index");
                    let (in_name, in_sort) = &chc_ctx.state_var_mgr.state_vars[idx];
                    let (out_name, out_sort) = &chc_ctx.state_var_mgr.output_state_vars[idx];
                    let expected = format!(
                        "(= {} {})",
                        Expr::var(&**out_name, out_sort.clone()),
                        Expr::var(&**in_name, in_sort.clone())
                    );
                    assert!(
                        constraints.iter().any(|c| c.to_string() == expected),
                        "identity sidecar helper should pin {var_name} to its input value"
                    );
                }
            },
        );
    }
}
