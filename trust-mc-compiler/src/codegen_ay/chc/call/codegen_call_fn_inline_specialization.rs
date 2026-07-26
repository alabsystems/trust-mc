// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Specialized inline dispatch handlers for CHC codegen.
//!
//! Contains `any_where` dispatch (nondeterministic value with closure predicate
//! guard) and copy-swap body pattern matching. Extracted from
//! `codegen_call_fn_inline.rs` for module size compliance (#4130).

use ay_bindings::Expr;
use rustc_public::CrateDef;
use rustc_public::mir::mono::Instance;
use rustc_public::mir::{AggregateKind, Operand, Place, Rvalue, StatementKind, TerminatorKind};
use rustc_public::rustc_internal;
use rustc_public::ty::{ClosureKind, RigidTy, TyKind};
use std::collections::{HashMap, HashSet};
use tracing::debug;

use crate::args::ChcTrackLevel;

use super::ChcCtx;
use super::chc_call_context::DispatchCallContext;
use super::codegen_call_coerce::CallCoerce;
use super::codegen_call_misc::CallMisc;
use super::codegen_rules::CodegenRules;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    pub(in crate::codegen_ay::chc) fn try_dispatch_call_any_where(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        target: usize,
    ) -> bool {
        let resolved = dcx.callee_path.clone().or_else(|| self.resolve_callee_path(dcx.func));
        let callee_path = match resolved {
            Some(path) if path.ends_with("::any_where") => path,
            _ => return false,
        };
        let Some(closure_arg) = dcx.args.first() else {
            return false;
        };
        let closure_ty = match closure_arg.ty(self.body.locals()) {
            Ok(ty) => ty,
            Err(_) => return false,
        };
        let (closure_def, closure_args) = match closure_ty.kind() {
            TyKind::RigidTy(RigidTy::Closure(def, args)) => (def, args),
            _ => return false,
        };

        let closure_body = [ClosureKind::Fn, ClosureKind::FnMut, ClosureKind::FnOnce]
            .into_iter()
            .find_map(|kind| {
                Instance::resolve_closure(closure_def, &closure_args, kind)
                    .ok()
                    .and_then(|instance| instance.body())
            });
        let Some(closure_body) = closure_body else {
            return false;
        };

        let captures = self.extract_any_where_captures(closure_arg, dcx.modified_locals);
        let dest_local = dcx.destination.local;
        let mut pred_modified = dcx.modified_locals.clone();
        pred_modified.insert(dest_local);
        let result_expr = if self.flatten.flattened_tuple_locals.contains(&dest_local) {
            let dest_place = Place { local: dest_local, projection: vec![] };
            self.translate_place_with_modified(&dest_place, &pred_modified)
        } else if let Some((name, sort)) = self
            .try_state_idx_for_local(dest_local)
            .and_then(|idx| self.state_var_mgr.output_state_vars.get(idx).cloned())
        {
            Some(Expr::var(&*name, sort))
        } else {
            None
        };
        let Some(result_expr) = result_expr else {
            return false;
        };

        let predicate = match super::inline_body::translate_closure_inline_body(
            self,
            &closure_body,
            std::slice::from_ref(&result_expr),
            &captures,
            dcx.bb_idx,
            0,
        ) {
            Some(expr) => expr,
            None => return false,
        };

        debug!(
            bb_idx = dcx.bb_idx,
            callee = %callee_path,
            capture_count = captures.len(),
            "fn_inline: lowered any_where as nondet + predicate guard"
        );

        let mut extra_constraints = vec![predicate];
        if self.track_level >= ChcTrackLevel::Mem {
            let local_place = Place { local: dest_local, projection: vec![] };
            if let Some(addr_expr) = self.translate_ref_to_address(&local_place, &pred_modified) {
                let local_ty = self.body.locals()[dest_local].ty;
                if let Some(store) =
                    self.build_memory_store(addr_expr, result_expr.clone(), local_ty)
                {
                    extra_constraints.push(store);
                }
                extra_constraints.append(&mut self.heap_state.pending_updates);
                extra_constraints
                    .append(&mut self.heap_state.drain_store_chains(&self.diagnostics));
                let pending_checks: Vec<_> = self.heap_state.pending_checks.drain(..).collect();
                for check in pending_checks {
                    self.emit_error_rule_for_condition(
                        dcx.from_app,
                        check,
                        dcx.stmt_constraints,
                        dcx.bb_idx,
                    );
                }
            }
        }

        extra_constraints.extend(self.int_lift_nondet_bounds(dest_local));
        extra_constraints.extend(self.unit_enum_discriminant_bounds(dest_local));
        extra_constraints.extend(self.char_nondet_bounds(dest_local));

        let new_output_args = self.build_output_args(dcx.modified_locals, &[dest_local]);
        self.emit_goto_rule_extra(
            dcx.from_app,
            target,
            &new_output_args,
            dcx.stmt_constraints,
            extra_constraints,
        );
        true
    }

    pub(in crate::codegen_ay::chc) fn try_dispatch_copy_swap_body(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        body: &rustc_public::mir::Body,
        callee_name: &str,
    ) -> bool {
        if !self.body_matches_copy_swap_pattern(body) || dcx.args.len() < 2 {
            return false;
        }
        let Some(target) = dcx.target else { return false };
        let Some(x_local) = super::ptr_receiver_mem::resolve_ptr_target_local(self, &dcx.args[0])
        else {
            return false;
        };
        let Some(y_local) = super::ptr_receiver_mem::resolve_ptr_target_local(self, &dcx.args[1])
        else {
            return false;
        };
        let Some(x_val) = self.resolve_ref_or_const_referent(&dcx.args[0], dcx.modified_locals)
        else {
            return false;
        };
        let Some(y_val) = self.resolve_ref_or_const_referent(&dcx.args[1], dcx.modified_locals)
        else {
            return false;
        };

        let Some(mut x_constraints) =
            self.build_local_update_constraints(x_local, y_val, "fn_inline_copy_swap_x")
        else {
            return false;
        };
        let Some(mut y_constraints) =
            self.build_local_update_constraints(y_local, x_val, "fn_inline_copy_swap_y")
        else {
            return false;
        };

        let dest_local = dcx.destination.local;
        let mut extra_dests = vec![dest_local, x_local];
        if y_local != x_local {
            extra_dests.push(y_local);
        }

        x_constraints.append(&mut y_constraints);

        // Part of #3932: Clear stale cross-block constant propagation entries for
        // the swapped locals. Without this, subsequent blocks read cached constants
        // (e.g. _1=12) instead of the updated state variables (_1__out=13).
        self.encode.invalidate_local_cache(x_local);
        self.encode.invalidate_local_cache(y_local);
        debug!(
            bb_idx = dcx.bb_idx,
            %callee_name,
            x_local,
            y_local,
            "fn_inline: direct copy-swap body dispatch"
        );
        self.emit_goto_rule_extra(
            dcx.from_app,
            *target,
            &self.build_output_args(dcx.modified_locals, &extra_dests),
            dcx.stmt_constraints,
            x_constraints,
        );
        true
    }

    fn body_matches_copy_swap_pattern(&self, body: &rustc_public::mir::Body) -> bool {
        if body.arg_locals().len() != 2 {
            return false;
        }
        let arg1_is_mut_ref = body.locals().get(1).is_some_and(|decl| {
            matches!(
                decl.ty.kind(),
                TyKind::RigidTy(RigidTy::Ref(_, _, rustc_public::mir::Mutability::Mut))
            )
        });
        let arg2_is_mut_ref = body.locals().get(2).is_some_and(|decl| {
            matches!(
                decl.ty.kind(),
                TyKind::RigidTy(RigidTy::Ref(_, _, rustc_public::mir::Mutability::Mut))
            )
        });
        if !arg1_is_mut_ref || !arg2_is_mut_ref {
            return false;
        }

        let mut copy_calls = 0usize;
        let mut uninitialized_calls = 0usize;
        let mut forget_calls = 0usize;

        for block in &body.blocks {
            let TerminatorKind::Call { func, .. } = &block.terminator.kind else { continue };
            let Some(path) = self.resolve_inline_body_callee_path(body, func) else {
                return false;
            };
            if path.contains("copy_nonoverlapping") {
                copy_calls += 1;
            } else if path.ends_with("::uninitialized") {
                uninitialized_calls += 1;
            } else if path.ends_with("::forget") {
                forget_calls += 1;
            } else {
                return false;
            }
        }

        copy_calls == 3 && uninitialized_calls == 1 && forget_calls == 1
    }

    pub(in crate::codegen_ay::chc) fn resolve_inline_body_callee_path(
        &self,
        body: &rustc_public::mir::Body,
        func: &Operand,
    ) -> Option<String> {
        let func_ty = func.ty(body.locals()).ok()?;
        let (fn_def, fn_substs) = match func_ty.kind() {
            TyKind::RigidTy(RigidTy::FnDef(def, substs)) => (def, substs),
            _ => return None,
        };
        let instance = Instance::resolve(fn_def, &fn_substs).ok()?;
        Some(self.tcx.def_path_str(rustc_internal::internal(self.tcx, instance.def.def_id())))
    }

    fn extract_any_where_captures(
        &mut self,
        closure_ref: &Operand,
        modified_locals: &HashSet<usize>,
    ) -> Vec<Expr> {
        let ref_local = match closure_ref {
            Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                place.local
            }
            _ => return Vec::new(),
        };
        let closure_local =
            self.ref_resolution.ref_targets.get(&ref_local).map_or(ref_local, |rt| rt.local);

        for block in &self.body.blocks {
            for stmt in &block.statements {
                if let StatementKind::Assign(place, rvalue) = &stmt.kind
                    && place.local == closure_local
                    && let Rvalue::Aggregate(AggregateKind::Closure(_, _), fields) = rvalue
                {
                    // Pre-build ref-target map in a single O(B*S) pass to avoid
                    // O(F*B*S) rescanning per capture field.
                    let ref_targets: HashMap<usize, Place> = self
                        .body
                        .blocks
                        .iter()
                        .flat_map(|b| &b.statements)
                        .filter_map(|s| {
                            if let StatementKind::Assign(place, Rvalue::Ref(_, _, inner_place)) =
                                &s.kind
                                && inner_place.projection.is_empty()
                            {
                                Some((place.local, inner_place.clone()))
                            } else {
                                None
                            }
                        })
                        .collect();

                    return fields
                        .iter()
                        .filter_map(|operand| {
                            let inner_local = match operand {
                                Operand::Copy(place) | Operand::Move(place)
                                    if place.projection.is_empty() =>
                                {
                                    Some(place.local)
                                }
                                _ => None,
                            };
                            if let Some(inner_local) = inner_local {
                                if let Some(inner_place) = ref_targets.get(&inner_local) {
                                    let inner_operand = Operand::Copy(inner_place.clone());
                                    return self.translate_operand_with_modified(
                                        &inner_operand,
                                        modified_locals,
                                    );
                                }
                            }
                            self.translate_operand_with_modified(operand, modified_locals)
                        })
                        .collect();
                }
            }
        }

        debug!(?closure_local, "could not find closure aggregate for any_where captures");
        Vec::new()
    }
}
