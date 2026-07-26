// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Dispatch-level regressions for ArraySolver shadow-state routing.

use crate::codegen_ay::chc::ChcCtx;
use crate::codegen_ay::chc::call::chc_call_context::DispatchCallContext;
use crate::codegen_ay::chc::call::codegen_call_array_solver_shadow::CallDispatchArraySolverShadow;
use ay_bindings::Expr;
use rustc_public::mir::{Operand, ProjectionElem, Rvalue, StatementKind};

const ARRAYSOLVER_TRAIL_TERMS_LEN_FIELD: usize = 9;
const ARRAYSOLVER_SCOPES_PTR_FIELD: usize = 20;
const ARRAYSOLVER_SCOPES_LEN_FIELD: usize = 21;
const ARRAYSOLVER_SCOPES_CAP_FIELD: usize = 22;
const ARRAYSOLVER_SCOPES_DATA_FIELD: usize = 23;
const ARRAYSOLVER_DIRTY_FIELD: usize = 24;

fn array_solver_receiver_local(chc_ctx: &ChcCtx<'_, '_>, args: &[Operand]) -> usize {
    let arg_local = match args.first() {
        Some(Operand::Copy(place) | Operand::Move(place)) => place.local,
        other => panic!("expected ArraySolver receiver operand, got {other:?}"),
    };
    chc_ctx.ref_resolution.ref_targets.get(&arg_local).map_or(arg_local, |target| target.local)
}

fn assert_promoted_output_slot(
    chc_ctx: &ChcCtx<'_, '_>,
    rule: &trust_mc_core::chc::Rule,
    idx: usize,
) {
    let out_name = &chc_ctx.state_var_mgr.output_state_vars[idx].0;
    assert!(
        rule.head.args[idx].to_string().contains(out_name.as_ref()),
        "expected state slot {idx} to use output var {out_name}, head args={:?}",
        rule.head.args
    );
}

fn poison_flattened_field_env(
    chc_ctx: &mut ChcCtx<'_, '_>,
    receiver_local: usize,
    field_idx: usize,
    name: &str,
) {
    let state_idx = chc_ctx
        .try_state_idx_for_local(receiver_local)
        .expect("receiver state idx for poisoned env");
    let sort = chc_ctx.state_var_mgr.state_vars[state_idx + field_idx].1.clone();
    chc_ctx.encode.flattened_field_env.insert((receiver_local, field_idx), Expr::var(name, sort));
}

fn shadow_dispatch_constraints_with_poisoned_env(
    method_name: &'static str,
    poisoned_fields: &[(usize, &str)],
) -> String {
    let mut constraints = None;
    super::with_array_solver_method_call(
        "probe_arrays_pop_restores_assignments",
        method_name,
        |_tcx,
         chc_ctx,
         func,
         args,
         destination,
         target,
         from_app,
         stmt_constraints,
         modified_locals,
         bb_idx,
         callee_path| {
            let receiver_local = array_solver_receiver_local(chc_ctx, args);
            assert!(
                chc_ctx.flatten.flattened_tuple_locals.contains(&receiver_local),
                "regression precondition: ArraySolver receiver should be flattened"
            );

            for (field_idx, name) in poisoned_fields {
                poison_flattened_field_env(chc_ctx, receiver_local, *field_idx, name);
            }

            let target_opt = Some(target);
            let dcx = DispatchCallContext {
                bb_idx,
                func,
                args,
                destination,
                target: &target_opt,
                from_app,
                stmt_constraints,
                modified_locals,
                callee_path: Some(callee_path.to_string()),
            };

            let before_rules = chc_ctx.vc.rules.len();
            assert!(
                chc_ctx.try_dispatch_call_array_solver_shadow(&dcx),
                "shadow dispatch should handle {callee_path}"
            );
            constraints = Some(
                chc_ctx.vc.rules[before_rules..]
                    .iter()
                    .flat_map(|rule| rule.body.constraints.iter())
                    .map(|constraint| constraint.to_string())
                    .collect::<Vec<_>>()
                    .join("\n"),
            );
        },
    );
    constraints.expect("captured shadow-dispatch constraints")
}

fn with_array_solver_new_dispatch(
    probe_suffix: &'static str,
    assertions: impl FnOnce(&mut ChcCtx<'_, '_>, &DispatchCallContext<'_>, usize, &str) + Send,
) {
    super::with_array_solver_method_call(
        probe_suffix,
        "ArraySolver::new",
        |_tcx,
         chc_ctx,
         func,
         args,
         destination,
         target,
         from_app,
         stmt_constraints,
         modified_locals,
         bb_idx,
         callee_path| {
            let target_opt = Some(target);
            let dcx = DispatchCallContext {
                bb_idx,
                func,
                args,
                destination,
                target: &target_opt,
                from_app,
                stmt_constraints,
                modified_locals,
                callee_path: Some(callee_path.to_string()),
            };
            assertions(chc_ctx, &dcx, destination.local, callee_path);
        },
    );
}

fn find_constructor_ref_chain_locals(
    body: &rustc_public::mir::Body,
    solver_local: usize,
) -> (usize, Option<usize>) {
    let ref_local = body
        .blocks
        .iter()
        .flat_map(|block| block.statements.iter())
        .find_map(|stmt| {
            let StatementKind::Assign(lhs, Rvalue::Ref(_, _, place)) = &stmt.kind else {
                return None;
            };
            if lhs.projection.is_empty()
                && place.local == solver_local
                && place.projection.len() == 1
                && matches!(place.projection[0], ProjectionElem::Field(..))
            {
                Some(lhs.local)
            } else {
                None
            }
        })
        .expect("expected &solver.<vec_field> ref local in constructor probe");

    // The compiler may optimize away the copy/move alias in some MIR versions.
    let alias_local =
        body.blocks.iter().flat_map(|block| block.statements.iter()).find_map(|stmt| {
            let StatementKind::Assign(
                lhs,
                Rvalue::Use(Operand::Copy(place) | Operand::Move(place)),
            ) = &stmt.kind
            else {
                return None;
            };
            if lhs.projection.is_empty() && place.local == ref_local && place.projection.is_empty()
            {
                Some(lhs.local)
            } else {
                None
            }
        });

    (ref_local, alias_local)
}

fn zero_sidecar_equality(var_name: &str) -> String {
    let out_name = crate::codegen_ay::names::out_name(var_name);
    let zero = Expr::bitvec_const(0u64, crate::codegen_ay::types::POINTER_WIDTH);
    format!("(= {out_name} {zero})")
}

#[test]
fn test_array_solver_new_shadow_dispatch_intercepts_constructor() {
    // ArraySolver::new() IS handled by shadow dispatch (#4050) — constrains all
    // flattened output fields to zero to prevent unconstrained fld vars from
    // corrupting downstream ghost propagation.
    with_array_solver_new_dispatch(
        "probe_arrays_pop_empty_is_safe_assert",
        |chc_ctx, dcx, _dest_local, _callee_path| {
            assert!(
                chc_ctx.try_dispatch_call_array_solver_shadow(dcx),
                "ArraySolver::new should be handled by shadow dispatch (#4050)"
            );
        },
    );
}

#[test]
fn test_array_solver_new_shadow_dispatched_with_other_vec() {
    // ArraySolver::new IS handled by shadow dispatch even when other Vec locals exist.
    with_array_solver_new_dispatch(
        "probe_arrays_new_preserves_other_vec_len_assert",
        |chc_ctx, dcx, _dest_local, _callee_path| {
            assert!(
                chc_ctx.try_dispatch_call_array_solver_shadow(dcx),
                "ArraySolver::new should be handled by shadow dispatch (#4050)"
            );
        },
    );
}

#[test]
fn test_array_solver_new_shadow_dispatch_zeroes_ref_chain_sidecars() {
    with_array_solver_new_dispatch(
        "probe_arrays_new_ref_chain_scopes_len_assert",
        |chc_ctx, dcx, dest_local, callee_path| {
            let (ref_local, alias_local) =
                find_constructor_ref_chain_locals(chc_ctx.body, dest_local);
            let locals_to_check: Vec<usize> =
                std::iter::once(ref_local).chain(alias_local).collect();
            let tracked_sidecars = locals_to_check
                .iter()
                .flat_map(|&local| {
                    [
                        chc_ctx.collections.len_state.get_len_var(local).cloned(),
                        chc_ctx.collections.len_state.get_cap_var(local).cloned(),
                    ]
                })
                .flatten()
                .collect::<Vec<_>>();
            assert!(
                tracked_sidecars.len() >= 2,
                "expected at least len/cap sidecars for the ref local (got {})",
                tracked_sidecars.len()
            );

            let before_rules = chc_ctx.vc.rules.len();
            assert!(
                chc_ctx.try_dispatch_call_array_solver_shadow(dcx),
                "shadow dispatch should handle {callee_path}"
            );
            assert_eq!(chc_ctx.vc.rules.len(), before_rules + 1);

            let rule = chc_ctx.vc.rules.last().expect("constructor rule");
            let constraints = chc_ctx.vc.rules[before_rules..]
                .iter()
                .flat_map(|r| r.body.constraints.iter())
                .map(std::string::ToString::to_string)
                .collect::<Vec<_>>()
                .join("\n");

            for sidecar in tracked_sidecars {
                let idx = chc_ctx
                    .state_var_index_by_name(&sidecar)
                    .expect("tracked ref-chain sidecar should have a state slot");
                assert_promoted_output_slot(chc_ctx, rule, idx);
                let expected_eq = zero_sidecar_equality(&sidecar);
                assert!(
                    constraints.contains(&expected_eq),
                    "constructor ref-chain sidecar {sidecar} should be zeroed, expected {expected_eq} in:\n{constraints}"
                );
            }
        },
    );
}

#[test]
fn test_array_solver_pop_shadow_dispatch_emits_ite_rule() {
    super::with_array_solver_method_call(
        "probe_arrays_pop_restores_assignments",
        "ArraySolver::pop",
        |_tcx,
         chc_ctx,
         func,
         args,
         destination,
         target,
         from_app,
         stmt_constraints,
         modified_locals,
         bb_idx,
         callee_path| {
            let target_opt = Some(target);
            let dcx = DispatchCallContext {
                bb_idx,
                func,
                args,
                destination,
                target: &target_opt,
                from_app,
                stmt_constraints,
                modified_locals,
                callee_path: Some(callee_path.to_string()),
            };

            let before_rules = chc_ctx.vc.rules.len();
            assert!(
                chc_ctx.try_dispatch_call_array_solver_shadow(&dcx),
                "shadow dispatch should handle {callee_path}"
            );

            // Pop uses SMT-level ite for empty/nonempty branches in a single rule.
            assert_eq!(
                chc_ctx.vc.rules.len(),
                before_rules + 1,
                "ArraySolver::pop should emit one rule with ite-based empty/nonempty branching"
            );

            let constraints = chc_ctx.vc.rules[before_rules..]
                .iter()
                .flat_map(|rule| rule.body.constraints.iter())
                .map(|c| c.to_string())
                .collect::<Vec<_>>()
                .join("\n");
            assert!(
                constraints.contains("ite"),
                "pop rule should contain ite for empty/nonempty branching, constraints={constraints}"
            );
        },
    );
}

#[test]
fn test_array_solver_push_shadow_dispatch_promotes_receiver_and_scope_depth() {
    super::with_array_solver_method_call(
        "probe_arrays_pop_restores_assignments",
        "ArraySolver::push",
        |_tcx,
         chc_ctx,
         func,
         args,
         destination,
         target,
         from_app,
         stmt_constraints,
         modified_locals,
         bb_idx,
         callee_path| {
            let target_opt = Some(target);
            let dcx = DispatchCallContext {
                bb_idx,
                func,
                args,
                destination,
                target: &target_opt,
                from_app,
                stmt_constraints,
                modified_locals,
                callee_path: Some(callee_path.to_string()),
            };
            let receiver_local = array_solver_receiver_local(chc_ctx, args);
            let aux = chc_ctx
                .collections
                .array_solver_aux
                .get(&receiver_local)
                .cloned()
                .expect("ArraySolver aux state");

            let before_rules = chc_ctx.vc.rules.len();
            assert!(
                chc_ctx.try_dispatch_call_array_solver_shadow(&dcx),
                "shadow dispatch should handle {callee_path}"
            );
            assert_eq!(chc_ctx.vc.rules.len(), before_rules + 1);

            let rule = chc_ctx.vc.rules.last().expect("push rule");
            // Push promotes shadow state vars (scope_depth, snap arrays, assign arrays).
            // Visible receiver fields are NOT modified — push only manipulates shadow SMT state.
            let scope_depth_idx = chc_ctx
                .state_var_index_by_name(&aux.scope_depth_var)
                .expect("scope_depth state idx");
            assert_promoted_output_slot(chc_ctx, rule, scope_depth_idx);

            let snap_present_idx = chc_ctx
                .state_var_index_by_name(&aux.scope_snap_present_var)
                .expect("scope_snap_present state idx");
            assert_promoted_output_slot(chc_ctx, rule, snap_present_idx);

            let snap_value_idx = chc_ctx
                .state_var_index_by_name(&aux.scope_snap_value_var)
                .expect("scope_snap_value state idx");
            assert_promoted_output_slot(chc_ctx, rule, snap_value_idx);
        },
    );
}

#[test]
fn test_array_solver_push_shadow_dispatch_ignores_cached_flattened_env() {
    let constraints = shadow_dispatch_constraints_with_poisoned_env(
        "ArraySolver::push",
        &[
            (ARRAYSOLVER_SCOPES_PTR_FIELD, "bogus_env_scopes_ptr"),
            (ARRAYSOLVER_SCOPES_LEN_FIELD, "bogus_env_scopes_len"),
            (ARRAYSOLVER_SCOPES_CAP_FIELD, "bogus_env_scopes_cap"),
            (ARRAYSOLVER_SCOPES_DATA_FIELD, "bogus_env_scopes_data"),
            (ARRAYSOLVER_TRAIL_TERMS_LEN_FIELD, "bogus_env_trail_terms_len"),
        ],
    );
    for poisoned in [
        "bogus_env_scopes_ptr",
        "bogus_env_scopes_len",
        "bogus_env_scopes_cap",
        "bogus_env_scopes_data",
        "bogus_env_trail_terms_len",
    ] {
        assert!(
            !constraints.contains(poisoned),
            "push visible-state rewrite should ignore cached flattened env value {poisoned}"
        );
    }
}

#[test]
fn test_array_solver_shadow_dispatch_prefers_ref_chain_flattened_receiver() {
    super::with_array_solver_method_call(
        "probe_arrays_pop_restores_assignments",
        "ArraySolver::push",
        |_tcx,
         chc_ctx,
         _func,
         args,
         _destination,
         _target,
         _from_app,
         _stmt_constraints,
         _modified_locals,
         _bb_idx,
         _callee_path| {
            let receiver_local = array_solver_receiver_local(chc_ctx, args);
            let flattened_local = chc_ctx.resolve_flattened_array_solver_local(receiver_local);
            assert!(
                chc_ctx.flatten.flattened_tuple_locals.contains(&flattened_local),
                "resolved ArraySolver receiver {flattened_local} should be flattened"
            );

            if let Some(source_local) = chc_ctx.resolve_ref_chain_for_array_solver(receiver_local)
                && chc_ctx.flatten.flattened_tuple_locals.contains(&source_local)
            {
                assert_eq!(
                    flattened_local, source_local,
                    "visible-state constraints should follow the receiver's copy/move chain \
                     instead of an arbitrary flattened aux local"
                );
            }
        },
    );
}

#[test]
fn test_array_solver_pop_shadow_dispatch_ignores_cached_flattened_env() {
    let constraints = shadow_dispatch_constraints_with_poisoned_env(
        "ArraySolver::pop",
        &[
            (ARRAYSOLVER_SCOPES_LEN_FIELD, "bogus_env_scopes_len"),
            (ARRAYSOLVER_DIRTY_FIELD, "bogus_env_dirty"),
        ],
    );
    for poisoned in ["bogus_env_scopes_len", "bogus_env_dirty"] {
        assert!(
            !constraints.contains(poisoned),
            "pop visible-state rewrite should ignore cached flattened env value {poisoned}"
        );
    }
}

#[test]
fn test_array_solver_record_assignment_shadow_dispatch_promotes_assign_arrays() {
    super::with_array_solver_method_call(
        "probe_arrays_pop_restores_assignments",
        "ArraySolver::record_assignment",
        |_tcx,
         chc_ctx,
         func,
         args,
         destination,
         target,
         from_app,
         stmt_constraints,
         modified_locals,
         bb_idx,
         callee_path| {
            let target_opt = Some(target);
            let dcx = DispatchCallContext {
                bb_idx,
                func,
                args,
                destination,
                target: &target_opt,
                from_app,
                stmt_constraints,
                modified_locals,
                callee_path: Some(callee_path.to_string()),
            };
            let receiver_local = array_solver_receiver_local(chc_ctx, args);
            let aux = chc_ctx
                .collections
                .array_solver_aux
                .get(&receiver_local)
                .cloned()
                .expect("ArraySolver aux state");

            let before_rules = chc_ctx.vc.rules.len();
            assert!(
                chc_ctx.try_dispatch_call_array_solver_shadow(&dcx),
                "shadow dispatch should handle {callee_path}"
            );
            assert_eq!(chc_ctx.vc.rules.len(), before_rules + 1);

            let rule = chc_ctx.vc.rules.last().expect("record_assignment rule");
            let assign_present_idx = chc_ctx
                .state_var_index_by_name(&aux.assign_present_var)
                .expect("assign_present state idx");
            let assign_value_idx = chc_ctx
                .state_var_index_by_name(&aux.assign_value_var)
                .expect("assign_value state idx");
            assert_promoted_output_slot(chc_ctx, rule, assign_present_idx);
            assert_promoted_output_slot(chc_ctx, rule, assign_value_idx);
        },
    );
}
