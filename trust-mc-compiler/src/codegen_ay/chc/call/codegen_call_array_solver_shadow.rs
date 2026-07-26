// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Pre-inline dispatcher for `ArraySolver` methods using shadow auxiliary state.
//!
//! The `ArraySolver` struct uses 6 parallel Vecs to model a push/pop assignment
//! map. Verifying properties like "pop restores assignments" through 25+ chained
//! Vec stub invocations causes constraint-loss compounding. This dispatcher
//! intercepts `ArraySolver` method calls before `fn_inline` and encodes them
//! using shadow SMT array state instead.
//!
//! Part of #4050: parallel-Vec map fusion for arrays tier3.

use ay_bindings::{Expr, Sort};
use tracing::debug;

use super::ChcCtx;
use super::chc_call_context::DispatchCallContext;
use super::codegen_call_coerce::CallCoerce;
use super::codegen_rules::CodegenRules;
use super::stubs_option_helpers::{OptionHelpers, make_option_sort};
use crate::codegen_ay::chc::codegen_ctx::types::ArraySolverAuxState;

/// Extension trait for ArraySolver shadow-state dispatch on `ChcCtx`.
pub(in crate::codegen_ay::chc) trait CallDispatchArraySolverShadow {
    fn try_dispatch_call_array_solver_shadow(&mut self, dcx: &DispatchCallContext<'_>) -> bool;
}

impl<'tcx, 'body> CallDispatchArraySolverShadow for ChcCtx<'tcx, 'body> {
    fn try_dispatch_call_array_solver_shadow(&mut self, dcx: &DispatchCallContext<'_>) -> bool {
        let Some(target) = dcx.target else { return false };

        // Resolve the callee path to check for ArraySolver methods.
        let callee_path = dcx.callee_path.clone().or_else(|| self.resolve_callee_path(dcx.func));
        let Some(ref path) = callee_path else { return false };

        // Match "ArraySolver::" in the callee path.
        let Some(method_start) = path.rfind("ArraySolver::") else { return false };
        let method_name = &path[method_start + "ArraySolver::".len()..];

        // `new()` is a static method — intercept to constrain ALL flattened output
        // fields to zero. Without this, fn_inline partially expands Vec::new() calls
        // leaving fld8+ unconstrained, which corrupts downstream ghost propagation
        // (veclen_N__out = unconstrained fld). Part of #4050.
        if method_name == "new" {
            let dest_local = dcx.destination.local;
            let aux = match self.collections.array_solver_aux.get(&dest_local) {
                Some(aux) => aux.clone(),
                None => return false,
            };
            return self.dispatch_array_solver_new(dcx, *target, dest_local, &aux);
        }

        // All other methods: find the receiver local from the first argument (self reference).
        let receiver_local = match self.resolve_array_solver_receiver(dcx) {
            Some(local) => local,
            None => return false,
        };

        // Look up shadow aux state for this local.
        let aux = match self.collections.array_solver_aux.get(&receiver_local) {
            Some(aux) => aux.clone(),
            None => return false,
        };

        // Resolve the flattened local for visible-state identity constraints.
        // The receiver may be a move/copy alias that is NOT in flattened_tuple_locals;
        // using it directly produces only 1-2 identity constraints instead of ~24.
        // Part of #4050.
        let flat_local = self.resolve_flattened_array_solver_local(receiver_local);
        debug!(
            method = method_name,
            receiver_local, flat_local, "ArraySolver shadow dispatch (#4050)"
        );

        match method_name {
            "get_assignment" => {
                self.dispatch_array_solver_get_assignment(dcx, *target, flat_local, &aux)
            }
            "push" => self.dispatch_array_solver_push(dcx, *target, flat_local, &aux),
            "pop" => self.dispatch_array_solver_pop(dcx, *target, flat_local, &aux),
            "record_assignment" => {
                self.dispatch_array_solver_record_assignment(dcx, *target, flat_local, &aux)
            }
            "set_assignment" => {
                self.dispatch_array_solver_set_assignment(dcx, *target, flat_local, &aux)
            }
            "remove_assignment" => {
                self.dispatch_array_solver_remove_assignment(dcx, *target, flat_local, &aux)
            }
            "reset" => self.dispatch_array_solver_reset(dcx, *target, flat_local, &aux),
            "populate_caches" => {
                self.dispatch_array_solver_populate_caches(dcx, *target, flat_local, &aux)
            }
            "known_equal" | "known_distinct" => {
                // Trivial scalar methods; let fn_inline handle them.
                false
            }
            _ => false,
        }
    }
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    // -- Constructor --

    /// `ArraySolver::new()`: intercept constructor to constrain all flattened
    /// output fields to zero and shadow state to initial values.
    fn dispatch_array_solver_new(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        target: usize,
        dest_local: usize,
        aux: &ArraySolverAuxState,
    ) -> bool {
        self.mark_array_solver_shadow_modified(aux);
        let mut extra = vec![
            self.shadow_assign_present_out(aux)
                .eq(Expr::const_array(Sort::bitvec(32), Expr::bool_const(false))),
            self.shadow_assign_value_out(aux)
                .eq(Expr::const_array(Sort::bitvec(32), Expr::bool_const(false))),
            self.shadow_dirty_out(aux).eq(Expr::bool_const(true)),
            self.shadow_scope_depth_out(aux).eq(Expr::bitvec_const(0u64, 64)),
            self.shadow_scope_snap_present_out(aux).eq(self.shadow_scope_snap_present(aux)),
            self.shadow_scope_snap_value_out(aux).eq(self.shadow_scope_snap_value(aux)),
        ];
        // Constrain ALL flattened struct fields to zero (ptr=0, len=0, cap=0,
        // data=const-array-zero for each Vec, dirty=true).
        if !self.constrain_all_flattened_fields_to_zero(dest_local, &mut extra) {
            return false;
        }
        // Zero all Vec sidecar tracking vars (veclen_N, veccap_N).
        self.zero_struct_vec_sidecars(dest_local, &mut extra);

        let output_args = self.build_output_args(dcx.modified_locals, &[dest_local]);
        self.emit_goto_rule_extra(dcx.from_app, target, &output_args, dcx.stmt_constraints, extra);
        true
    }

    // -- Method dispatchers --

    /// `ArraySolver::get_assignment(term) -> Option<bool>`:
    /// Replace the while-loop linear search with SMT array select.
    fn dispatch_array_solver_get_assignment(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        target: usize,
        receiver_local: usize,
        aux: &ArraySolverAuxState,
    ) -> bool {
        self.mark_array_solver_shadow_modified(aux);
        // arg0 = &self, arg1 = term: TermId (u32)
        let Some(term_arg) = dcx.args.get(1) else { return false };
        let Some(term_expr) = self.translate_operand_with_modified(term_arg, dcx.modified_locals)
        else {
            return false;
        };

        let is_present = self.shadow_assign_present(aux).select(term_expr.clone());
        let value = self.shadow_assign_value(aux).select(term_expr);

        // Build Option<bool> result: ITE(is_present, Some(value), None)
        let opt_sort = make_option_sort(&Sort::bool());
        let some_expr = match self.make_some_expr_for_option(value, &opt_sort) {
            Some(e) => e,
            None => return false,
        };
        let none_expr = self.make_none_expr(&Sort::bool());
        let option_result = Expr::ite(is_present, some_expr, none_expr);

        // Bind result to destination local.
        let dest_local = dcx.destination.local;
        let mut extra: Vec<Expr> = Vec::new();
        if !self.bind_vec_pop_destination(
            dest_local,
            dcx.modified_locals,
            option_result,
            &mut extra,
        ) {
            return false;
        }

        // Shadow state unchanged (read-only method).
        extra.extend(self.shadow_identity_constraints(aux));
        // Pin visible struct fields and sidecar len/cap vars to identity.
        self.constrain_receiver_visible_identity(receiver_local, false, &mut extra);
        self.identity_struct_vec_sidecars(receiver_local, &mut extra);

        let mut modified = dcx.modified_locals.clone();
        modified.insert(dest_local);
        let output_args = self.build_output_args(&modified, &[]);
        self.emit_goto_rule_extra(dcx.from_app, target, &output_args, dcx.stmt_constraints, extra);
        true
    }

    /// `ArraySolver::push()`: save current assign_map snapshot at current depth,
    /// then increment scope_depth.
    fn dispatch_array_solver_push(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        target: usize,
        receiver_local: usize,
        aux: &ArraySolverAuxState,
    ) -> bool {
        self.mark_array_solver_shadow_modified(aux);
        let depth_expr = self.shadow_scope_depth(aux);

        let scope_snap_present = self.shadow_scope_snap_present(aux);
        let scope_snap_value = self.shadow_scope_snap_value(aux);

        let new_snap_present =
            scope_snap_present.store(depth_expr.clone(), self.shadow_assign_present(aux));
        let new_snap_value =
            scope_snap_value.store(depth_expr.clone(), self.shadow_assign_value(aux));

        let one = Expr::bitvec_const(1u64, 64);
        let new_depth = depth_expr.bvadd(one);

        let mut extra = vec![
            // assign_map unchanged during push
            self.shadow_assign_present_out(aux).eq(self.shadow_assign_present(aux)),
            self.shadow_assign_value_out(aux).eq(self.shadow_assign_value(aux)),
            // save snapshots at current depth
            self.shadow_scope_snap_present_out(aux).eq(new_snap_present),
            self.shadow_scope_snap_value_out(aux).eq(new_snap_value),
            // dirty unchanged during push
            self.shadow_dirty_out(aux).eq(self.shadow_dirty(aux)),
            // increment scope depth
            self.shadow_scope_depth_out(aux).eq(new_depth),
        ];
        let receiver_owner_local =
            self.resolve_array_solver_receiver(dcx).unwrap_or(receiver_local);
        if !self.constrain_visible_array_solver_push(
            receiver_owner_local,
            dcx.modified_locals,
            &mut extra,
        ) {
            return false;
        }

        let output_args = self.build_output_args(dcx.modified_locals, &[receiver_local]);
        self.emit_goto_rule_extra(dcx.from_app, target, &output_args, dcx.stmt_constraints, extra);
        true
    }

    /// `ArraySolver::pop()`: restore assign_map from scope_snapshots, decrement
    /// scope_depth. No-op if scope_depth == 0.
    fn dispatch_array_solver_pop(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        target: usize,
        receiver_local: usize,
        aux: &ArraySolverAuxState,
    ) -> bool {
        self.mark_array_solver_shadow_modified(aux);

        let depth_expr = self.shadow_scope_depth(aux);
        let scope_snap_present = self.shadow_scope_snap_present(aux);
        let scope_snap_value = self.shadow_scope_snap_value(aux);

        let zero = Expr::bitvec_const(0u64, 64);
        let one = Expr::bitvec_const(1u64, 64);
        let is_empty = depth_expr.clone().eq(zero);
        let depth_minus_1 = depth_expr.clone().bvsub(one);

        // Restore from snapshot at depth-1 (the last pushed scope).
        let restored_present = scope_snap_present.select(depth_minus_1.clone());
        let restored_value = scope_snap_value.select(depth_minus_1.clone());

        let new_assign_present =
            Expr::ite(is_empty.clone(), self.shadow_assign_present(aux), restored_present);
        let new_assign_value =
            Expr::ite(is_empty.clone(), self.shadow_assign_value(aux), restored_value);
        let new_depth = Expr::ite(is_empty, depth_expr.clone(), depth_minus_1);

        let mut extra = vec![
            self.shadow_assign_present_out(aux).eq(new_assign_present),
            self.shadow_assign_value_out(aux).eq(new_assign_value),
            self.shadow_scope_snap_present_out(aux).eq(self.shadow_scope_snap_present(aux)),
            self.shadow_scope_snap_value_out(aux).eq(self.shadow_scope_snap_value(aux)),
            // pop() sets self.dirty = true (shadow)
            self.shadow_dirty_out(aux).eq(Expr::bool_const(true)),
            // decrement scope depth (or no-op if was 0)
            self.shadow_scope_depth_out(aux).eq(new_depth),
        ];
        let receiver_owner_local =
            self.resolve_array_solver_receiver(dcx).unwrap_or(receiver_local);
        if !self.constrain_visible_array_solver_pop(
            receiver_owner_local,
            dcx.modified_locals,
            depth_expr.eq(Expr::bitvec_const(0u64, 64)),
            &mut extra,
        ) {
            return false;
        }

        let output_args = self.build_output_args(dcx.modified_locals, &[receiver_local]);
        self.emit_goto_rule_extra(dcx.from_app, target, &output_args, dcx.stmt_constraints, extra);
        true
    }

    /// `ArraySolver::record_assignment(term, value)`: update shadow assign_map.
    fn dispatch_array_solver_record_assignment(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        target: usize,
        receiver_local: usize,
        aux: &ArraySolverAuxState,
    ) -> bool {
        self.mark_array_solver_shadow_modified(aux);
        let (term_expr, value_expr) = match (
            dcx.args
                .get(1)
                .and_then(|a| self.translate_operand_with_modified(a, dcx.modified_locals)),
            dcx.args
                .get(2)
                .and_then(|a| self.translate_operand_with_modified(a, dcx.modified_locals)),
        ) {
            (Some(t), Some(v)) => (t, v),
            _ => return false,
        };

        let new_present =
            self.shadow_assign_present(aux).store(term_expr.clone(), Expr::bool_const(true));
        let new_value = self.shadow_assign_value(aux).store(term_expr, value_expr);

        let mut extra = vec![
            self.shadow_assign_present_out(aux).eq(new_present),
            self.shadow_assign_value_out(aux).eq(new_value),
            self.shadow_scope_snap_present_out(aux).eq(self.shadow_scope_snap_present(aux)),
            self.shadow_scope_snap_value_out(aux).eq(self.shadow_scope_snap_value(aux)),
            self.shadow_dirty_out(aux).eq(self.shadow_dirty(aux)),
            self.shadow_scope_depth_out(aux).eq(self.shadow_scope_depth(aux)),
        ];
        // Pin visible struct fields and sidecar len/cap vars to identity.
        self.constrain_receiver_visible_identity(receiver_local, false, &mut extra);
        self.identity_struct_vec_sidecars(receiver_local, &mut extra);

        let output_args = self.build_output_args(dcx.modified_locals, &[]);
        self.emit_goto_rule_extra(dcx.from_app, target, &output_args, dcx.stmt_constraints, extra);
        true
    }

    /// `ArraySolver::set_assignment(term, value)`: update shadow assign_map.
    fn dispatch_array_solver_set_assignment(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        target: usize,
        receiver_local: usize,
        aux: &ArraySolverAuxState,
    ) -> bool {
        self.mark_array_solver_shadow_modified(aux);
        let (term_expr, value_expr) = match (
            dcx.args
                .get(1)
                .and_then(|a| self.translate_operand_with_modified(a, dcx.modified_locals)),
            dcx.args
                .get(2)
                .and_then(|a| self.translate_operand_with_modified(a, dcx.modified_locals)),
        ) {
            (Some(t), Some(v)) => (t, v),
            _ => return false,
        };

        let new_present =
            self.shadow_assign_present(aux).store(term_expr.clone(), Expr::bool_const(true));
        let new_value = self.shadow_assign_value(aux).store(term_expr, value_expr);

        let mut extra = vec![
            self.shadow_assign_present_out(aux).eq(new_present),
            self.shadow_assign_value_out(aux).eq(new_value),
            self.shadow_scope_snap_present_out(aux).eq(self.shadow_scope_snap_present(aux)),
            self.shadow_scope_snap_value_out(aux).eq(self.shadow_scope_snap_value(aux)),
            self.shadow_dirty_out(aux).eq(self.shadow_dirty(aux)),
            self.shadow_scope_depth_out(aux).eq(self.shadow_scope_depth(aux)),
        ];
        // Pin visible struct fields and sidecar len/cap vars to identity.
        self.constrain_receiver_visible_identity(receiver_local, false, &mut extra);
        self.identity_struct_vec_sidecars(receiver_local, &mut extra);

        let output_args = self.build_output_args(dcx.modified_locals, &[]);
        self.emit_goto_rule_extra(dcx.from_app, target, &output_args, dcx.stmt_constraints, extra);
        true
    }

    /// `ArraySolver::remove_assignment(term)`: clear term from shadow assign_map.
    fn dispatch_array_solver_remove_assignment(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        target: usize,
        receiver_local: usize,
        aux: &ArraySolverAuxState,
    ) -> bool {
        self.mark_array_solver_shadow_modified(aux);
        let Some(term_expr) = dcx
            .args
            .get(1)
            .and_then(|a| self.translate_operand_with_modified(a, dcx.modified_locals))
        else {
            return false;
        };

        let new_present = self.shadow_assign_present(aux).store(term_expr, Expr::bool_const(false));

        let mut extra = vec![
            self.shadow_assign_present_out(aux).eq(new_present),
            self.shadow_assign_value_out(aux).eq(self.shadow_assign_value(aux)),
            self.shadow_scope_snap_present_out(aux).eq(self.shadow_scope_snap_present(aux)),
            self.shadow_scope_snap_value_out(aux).eq(self.shadow_scope_snap_value(aux)),
            self.shadow_dirty_out(aux).eq(self.shadow_dirty(aux)),
            self.shadow_scope_depth_out(aux).eq(self.shadow_scope_depth(aux)),
        ];
        // Pin visible struct fields and sidecar len/cap vars to identity.
        self.constrain_receiver_visible_identity(receiver_local, false, &mut extra);
        self.identity_struct_vec_sidecars(receiver_local, &mut extra);

        let output_args = self.build_output_args(dcx.modified_locals, &[]);
        self.emit_goto_rule_extra(dcx.from_app, target, &output_args, dcx.stmt_constraints, extra);
        true
    }

    /// `ArraySolver::reset()`: clear all shadow state, set dirty=true.
    fn dispatch_array_solver_reset(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        target: usize,
        receiver_local: usize,
        aux: &ArraySolverAuxState,
    ) -> bool {
        self.mark_array_solver_shadow_modified(aux);
        let const_false = Expr::const_array(Sort::bitvec(32), Expr::bool_const(false));

        let mut extra = vec![
            self.shadow_assign_present_out(aux).eq(const_false.clone()),
            self.shadow_assign_value_out(aux).eq(const_false),
            self.shadow_dirty_out(aux).eq(Expr::bool_const(true)),
            // reset clears all scopes
            self.shadow_scope_depth_out(aux).eq(Expr::bitvec_const(0u64, 64)),
        ];
        // Dirty field explicitly constrained; pin all OTHER visible fields and sidecars.
        self.constrain_receiver_visible_identity(receiver_local, true, &mut extra);
        self.identity_struct_vec_sidecars(receiver_local, &mut extra);
        let receiver_owner_local =
            self.resolve_array_solver_receiver(dcx).unwrap_or(receiver_local);
        if !self.constrain_visible_array_solver_dirty(
            receiver_owner_local,
            dcx.modified_locals,
            Expr::bool_const(true),
            &mut extra,
        ) {
            return false;
        }

        let output_args = self.build_output_args(dcx.modified_locals, &[]);
        self.emit_goto_rule_extra(dcx.from_app, target, &output_args, dcx.stmt_constraints, extra);
        true
    }

    /// `ArraySolver::populate_caches()`: set dirty=false, all else unchanged.
    fn dispatch_array_solver_populate_caches(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        target: usize,
        receiver_local: usize,
        aux: &ArraySolverAuxState,
    ) -> bool {
        self.mark_array_solver_shadow_modified(aux);
        let mut extra = self.shadow_array_identity_constraints(aux);
        extra.push(self.shadow_dirty_out(aux).eq(Expr::bool_const(false)));
        extra.push(self.shadow_scope_depth_out(aux).eq(self.shadow_scope_depth(aux)));
        // Dirty field explicitly constrained; pin all OTHER visible fields and sidecars.
        self.constrain_receiver_visible_identity(receiver_local, true, &mut extra);
        self.identity_struct_vec_sidecars(receiver_local, &mut extra);
        let receiver_owner_local =
            self.resolve_array_solver_receiver(dcx).unwrap_or(receiver_local);
        if !self.constrain_visible_array_solver_dirty(
            receiver_owner_local,
            dcx.modified_locals,
            Expr::bool_const(false),
            &mut extra,
        ) {
            return false;
        }

        let output_args = self.build_output_args(dcx.modified_locals, &[]);
        self.emit_goto_rule_extra(dcx.from_app, target, &output_args, dcx.stmt_constraints, extra);
        true
    }
}
