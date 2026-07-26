// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! MIR-driven localizer for the current-head arrays replay packet.
//! Part of #4031, #1739, #3768, #134.

use super::super::chc_call_context::ChcCallContext;
use super::super::codegen_call_vec::CallVec;
use super::common::*;
use crate::codegen_ay::chc::call::{UnknownProjectionPolicy, collect_field_projections};
use crate::codegen_ay::chc::codegen_call_vec::ChcVecFields;
use rustc_public::mir::{Operand, TerminatorKind};
use std::collections::HashSet;

#[path = "test_bootstrap_arrays_tier3_residual_localizer.rs"]
mod residual_localizer;
#[path = "test_bootstrap_arrays_tier3_restore_solver.rs"]
mod restore_solver;
#[path = "test_bootstrap_arrays_tier3_shadow_dispatch.rs"]
mod shadow_dispatch;
#[path = "test_bootstrap_arrays_tier3_visible_state.rs"]
mod visible_state;

pub(super) use visible_state::{inline_budget_note_arrays, with_array_solver_method_call};

/// The real committed harness file, loaded verbatim for exact-file unit
/// reproducers (design D1 from `designs/2026-03-20-issue-4050-exact-file-restore-localizer.md`).
const BOOTSTRAP_ARRAYS_TIER3_REAL_FILE: &str =
    include_str!("../../../../../tests/ay/ay_self_verify_bootstrap_tier3_arrays.rs");

/// Strip `#[kani::proof]`, `#[kani::unwind(...)]`, `// kani-expect:` lines and
/// inject a local kani stub module so the real harness source compiles under
/// the CHC unit test harness without the full Kani sysroot.
fn strip_kani_for_unit_ctx(source: &str) -> String {
    let mut result = String::with_capacity(source.len() + 256);
    result.push_str("#![allow(dead_code, unused_assignments)]\n");
    result.push_str("#![feature(register_tool)]\n");
    result.push_str("#![register_tool(kanitool)]\n\n");
    result.push_str("mod kani {\n");
    result.push_str("    #[kanitool::fn_marker = \"AnyModel\"]\n");
    result.push_str("    pub fn any<T>() -> T { panic!(\"model-only\") }\n\n");
    result.push_str("    #[kanitool::fn_marker = \"AssumeHook\"]\n");
    result.push_str("    pub fn assume(_cond: bool) {}\n");
    result.push_str("}\n\n");
    for line in source.lines() {
        let trimmed = line.trim();
        if trimmed.starts_with("#[kani::") {
            continue;
        }
        if trimmed.starts_with("// kani-expect:") {
            continue;
        }
        if trimmed.starts_with("//!") {
            continue;
        }
        // Skip existing crate-level attributes that conflict with our injected ones.
        if trimmed.starts_with("#![") {
            continue;
        }
        result.push_str(line);
        result.push('\n');
    }
    result
}

pub(super) const BOOTSTRAP_ARRAYS_TIER3_SOURCE: &str = r#"
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

        fn get_assignment(&self, term: TermId) -> Option<bool> {
            let mut i = 0;
            while i < self.assign_terms.len() {
                if self.assign_terms[i] == term {
                    return Some(self.assign_values[i]);
                }
                i += 1;
            }
            None
        }

        fn set_assignment(&mut self, term: TermId, value: bool) {
            let mut i = 0;
            while i < self.assign_terms.len() {
                if self.assign_terms[i] == term {
                    self.assign_values[i] = value;
                    return;
                }
                i += 1;
            }
            self.assign_terms.push(term);
            self.assign_values.push(value);
        }

        fn remove_assignment(&mut self, term: TermId) {
            let mut i = 0;
            while i < self.assign_terms.len() {
                if self.assign_terms[i] == term {
                    let mut j = i;
                    while j + 1 < self.assign_terms.len() {
                        self.assign_terms[j] = self.assign_terms[j + 1];
                        self.assign_values[j] = self.assign_values[j + 1];
                        j += 1;
                    }
                    self.assign_terms.pop();
                    self.assign_values.pop();
                    return;
                }
                i += 1;
            }
        }

        fn push(&mut self) {
            self.scopes.push(self.trail_terms.len());
        }

        fn pop(&mut self) {
            let Some(marker) = self.scopes.pop() else {
                return;
            };

            while self.trail_terms.len() > marker {
                let term = self.trail_terms.pop().unwrap();
                let previous_present = self.trail_prev_present.pop().unwrap();
                let previous_value = self.trail_prev_values.pop().unwrap();
                if previous_present {
                    self.set_assignment(term, previous_value);
                } else {
                    self.remove_assignment(term);
                }
            }
            self.dirty = true;
        }

        fn record_assignment(&mut self, term: TermId, value: bool) {
            let previous = self.get_assignment(term);
            if previous == Some(value) {
                return;
            }

            self.trail_terms.push(term);
            self.trail_prev_present.push(previous.is_some());
            self.trail_prev_values.push(previous.unwrap_or(false));
            self.set_assignment(term, value);
        }

        fn populate_caches(&mut self) {
            self.dirty = false;
        }
    }

    pub fn probe_arrays_pop_restores_assignments() -> bool {
        let mut solver = ArraySolver::new();
        let term = 7u32;

        solver.push();
        let initial_value = solver.get_assignment(term);
        solver.record_assignment(term, true);
        solver.pop();

        solver.get_assignment(term) == initial_value
    }

    pub fn probe_arrays_pop_restores_assignments_assert(term: u8, value: bool) {
        let term = (term % 100) as u32;
        let mut solver = ArraySolver::new();

        solver.push();
        let initial_value = solver.get_assignment(term);
        solver.record_assignment(term, value);
        solver.pop();

        assert!(solver.get_assignment(term) == initial_value);
    }

    pub fn probe_arrays_pop_restores_assignments_false_assert(term: u8, value: bool) {
        let term = (term % 100) as u32;
        let mut solver = ArraySolver::new();

        solver.push();
        let initial_value = solver.get_assignment(term);
        solver.record_assignment(term, value);
        solver.pop();

        assert!(solver.get_assignment(term) != initial_value);
    }

    pub fn probe_arrays_push_pop_scope_depth() -> bool {
        let mut scopes: Vec<usize> = Vec::new();
        let initial_depth = scopes.len();

        scopes.push(0);
        let after_first_push = scopes.len() == initial_depth + 1;

        scopes.push(0);
        let after_second_push = scopes.len() == initial_depth + 2;

        let first_pop = scopes.pop() == Some(0);
        let after_first_pop = scopes.len() == initial_depth + 1;

        let second_pop = scopes.pop() == Some(0);
        let after_second_pop = scopes.len() == initial_depth;

        after_first_push
            && after_second_push
            && first_pop
            && after_first_pop
            && second_pop
            && after_second_pop
    }

    pub fn probe_arrays_pop_empty_is_safe() -> bool {
        let mut solver = ArraySolver::new();
        let trail_len_before = solver.trail_terms.len();
        let assigns_len_before = solver.assign_terms.len();

        solver.pop();

        solver.trail_terms.len() == trail_len_before
            && solver.trail_prev_present.len() == trail_len_before
            && solver.trail_prev_values.len() == trail_len_before
            && solver.assign_terms.len() == assigns_len_before
            && solver.assign_values.len() == assigns_len_before
            && solver.scopes.is_empty()
    }

    pub fn probe_arrays_pop_empty_is_safe_assert() {
        let mut solver = ArraySolver::new();
        let trail_len_before = solver.trail_terms.len();
        let assigns_len_before = solver.assign_terms.len();

        solver.pop();

        assert_eq!(solver.trail_terms.len(), trail_len_before);
        assert_eq!(solver.trail_prev_present.len(), trail_len_before);
        assert_eq!(solver.trail_prev_values.len(), trail_len_before);
        assert_eq!(solver.assign_terms.len(), assigns_len_before);
        assert_eq!(solver.assign_values.len(), assigns_len_before);
        assert!(solver.scopes.is_empty());
    }

    pub fn probe_arrays_pop_empty_trail_terms_len_assert() {
        let mut solver = ArraySolver::new();
        let trail_len_before = solver.trail_terms.len();
        solver.pop();
        assert_eq!(solver.trail_terms.len(), trail_len_before);
    }

    pub fn probe_arrays_pop_empty_trail_prev_present_len_assert() {
        let mut solver = ArraySolver::new();
        let trail_len_before = solver.trail_terms.len();
        solver.pop();
        assert_eq!(solver.trail_prev_present.len(), trail_len_before);
    }

    pub fn probe_arrays_pop_empty_trail_prev_values_len_assert() {
        let mut solver = ArraySolver::new();
        let trail_len_before = solver.trail_terms.len();
        solver.pop();
        assert_eq!(solver.trail_prev_values.len(), trail_len_before);
    }

    pub fn probe_arrays_pop_empty_assign_terms_len_assert() {
        let mut solver = ArraySolver::new();
        let assigns_len_before = solver.assign_terms.len();
        solver.pop();
        assert_eq!(solver.assign_terms.len(), assigns_len_before);
    }

    pub fn probe_arrays_pop_empty_assign_values_len_assert() {
        let mut solver = ArraySolver::new();
        let assigns_len_before = solver.assign_terms.len();
        solver.pop();
        assert_eq!(solver.assign_values.len(), assigns_len_before);
    }

    pub fn probe_arrays_pop_empty_scopes_empty_assert() {
        let mut solver = ArraySolver::new();
        solver.pop();
        assert!(solver.scopes.is_empty());
    }

    pub fn probe_arrays_dirty_flag_after_pop() -> bool {
        let mut solver = ArraySolver::new();
        solver.populate_caches();
        solver.push();
        solver.pop();
        solver.dirty
    }

    pub fn probe_arrays_new_trail_terms_len_assert() {
        let solver = ArraySolver::new();
        assert_eq!(solver.trail_terms.len(), 0);
    }

    pub fn probe_arrays_new_trail_prev_present_len_assert() {
        let solver = ArraySolver::new();
        assert_eq!(solver.trail_prev_present.len(), 0);
    }

    pub fn probe_arrays_new_trail_prev_values_len_assert() {
        let solver = ArraySolver::new();
        assert_eq!(solver.trail_prev_values.len(), 0);
    }

    pub fn probe_arrays_new_assign_terms_len_assert() {
        let solver = ArraySolver::new();
        assert_eq!(solver.assign_terms.len(), 0);
    }

    pub fn probe_arrays_new_assign_values_len_assert() {
        let solver = ArraySolver::new();
        assert_eq!(solver.assign_values.len(), 0);
    }

    pub fn probe_arrays_new_preserves_other_vec_len_assert() {
        let mut other: Vec<u8> = Vec::new();
        other.push(7);

        let solver = ArraySolver::new();

        assert_eq!(solver.scopes.len(), 0);
        assert_eq!(other.len(), 1);
    }

    pub fn probe_arrays_new_ref_chain_scopes_len_assert() {
        let solver = ArraySolver::new();
        let scopes_ref = &solver.scopes;
        let scopes_alias = scopes_ref;

        assert_eq!(scopes_alias.len(), 0);
    }

    pub fn probe_arrays_new_scopes_empty_assert() {
        let solver = ArraySolver::new();
        assert!(solver.scopes.is_empty());
    }

    /// Isolated probe: get_assignment on empty solver returns None.
    pub fn probe_array_solver_get_assignment_empty() -> bool {
        let solver = ArraySolver::new();
        solver.get_assignment(42u32).is_none()
    }

    /// Isolated probe: get_assignment after set_assignment returns the value.
    pub fn probe_array_solver_get_assignment_after_set() -> bool {
        let mut solver = ArraySolver::new();
        solver.set_assignment(5u32, true);
        solver.get_assignment(5u32) == Some(true)
    }
"#;

pub(super) fn reset_bootstrap_arrays_tier3_counters() {
    clear_chc_fallback_counts();
    let _ = crate::codegen_ay::take_inferable_predicate_count();
    let _ = crate::codegen_ay::take_unhandled_call_by_fn();
}

pub(super) fn inferable_predicate_artifacts(vc: &trust_mc_core::chc::ChcVc) -> (Vec<String>, bool) {
    let inferable_decls = vc
        .decls
        .iter()
        .filter_map(|decl| match decl {
            trust_mc_core::decl::Decl::Fun { name, .. } if name.starts_with("P_inf_") => {
                Some(name.clone())
            }
            _ => None,
        })
        .collect();
    let has_p_inf_rule = vc.rules.iter().any(|rule| format!("{rule:?}").contains("P_inf_"));
    (inferable_decls, has_p_inf_rule)
}

/// Iterate the four internal `Vec::pop()` calls inside `ArraySolver::pop()`
/// and hand each call terminator to a test closure.
fn with_array_solver_pop_vecpop_calls(
    mut assertions: impl FnMut(
        TyCtxt<'_>,
        &mut ChcCtx<'_, '_>,
        &[Operand],
        &Place,
        usize,
        &RelationApp,
        &[Expr],
        &HashSet<usize>,
        usize,
        &str,
        usize,
    ) + Send,
) {
    with_test_ay_ctx_for_source(BOOTSTRAP_ARRAYS_TIER3_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "ArraySolver::pop");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "ArraySolver::pop", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let mut vec_pop_calls = 0usize;
        for (bb_idx, block) in body.blocks.iter().enumerate() {
            let TerminatorKind::Call { func, args, destination, target: Some(target), .. } =
                &block.terminator.kind
            else {
                continue;
            };
            if !matches!(
                chc_ctx.detect_stub_matching(func, StubKind::is_vec_core),
                Some(StubKind::VecPop)
            ) {
                continue;
            }

            let callee_path = chc_ctx
                .resolve_callee_path(func)
                .or_else(|| chc_ctx.resolve_fn_def_name(func))
                .unwrap_or_else(|| "<unknown>".to_string());
            let from_rel = chc_ctx.block_relations.get(&bb_idx).expect("source relation").clone();
            let output_args: Vec<_> = chc_ctx
                .state_var_mgr
                .state_vars
                .iter()
                .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
                .collect();
            let from_app = RelationApp::new(&from_rel, output_args);
            let stmt_constraints = [Expr::bool_const(true)];
            let modified_locals = HashSet::new();

            assertions(
                ctx.tcx,
                &mut chc_ctx,
                args,
                destination,
                *target,
                &from_app,
                &stmt_constraints,
                &modified_locals,
                bb_idx,
                &callee_path,
                vec_pop_calls,
            );
            vec_pop_calls += 1;
        }

        assert_eq!(
            vec_pop_calls, 4,
            "ArraySolver::pop should contain exactly four internal Vec::pop() calls"
        );
    });
}

/// Iterate the two internal `Vec::pop()` calls inside
/// `ArraySolver::remove_assignment()` and hand each call terminator to a test
/// closure.
fn with_array_solver_remove_assignment_vecpop_calls(
    mut assertions: impl FnMut(
        TyCtxt<'_>,
        &mut ChcCtx<'_, '_>,
        &[Operand],
        &Place,
        usize,
        &RelationApp,
        &[Expr],
        &HashSet<usize>,
        usize,
        &str,
        usize,
    ) + Send,
) {
    with_test_ay_ctx_for_source(BOOTSTRAP_ARRAYS_TIER3_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "ArraySolver::remove_assignment");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "ArraySolver::remove_assignment", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let mut vec_pop_calls = 0usize;
        for (bb_idx, block) in body.blocks.iter().enumerate() {
            let TerminatorKind::Call { func, args, destination, target: Some(target), .. } =
                &block.terminator.kind
            else {
                continue;
            };
            if !matches!(
                chc_ctx.detect_stub_matching(func, StubKind::is_vec_core),
                Some(StubKind::VecPop)
            ) {
                continue;
            }

            let callee_path = chc_ctx
                .resolve_callee_path(func)
                .or_else(|| chc_ctx.resolve_fn_def_name(func))
                .unwrap_or_else(|| "<unknown>".to_string());
            let from_rel = chc_ctx.block_relations.get(&bb_idx).expect("source relation").clone();
            let output_args: Vec<_> = chc_ctx
                .state_var_mgr
                .state_vars
                .iter()
                .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
                .collect();
            let from_app = RelationApp::new(&from_rel, output_args);
            let stmt_constraints = [Expr::bool_const(true)];
            let modified_locals = HashSet::new();

            assertions(
                ctx.tcx,
                &mut chc_ctx,
                args,
                destination,
                *target,
                &from_app,
                &stmt_constraints,
                &modified_locals,
                bb_idx,
                &callee_path,
                vec_pop_calls,
            );
            vec_pop_calls += 1;
        }

        assert_eq!(
            vec_pop_calls, 2,
            "ArraySolver::remove_assignment should contain exactly two internal Vec::pop() calls"
        );
    });
}

fn assert_internal_struct_vecpop_contract(
    chc_ctx: &mut ChcCtx<'_, '_>,
    args: &[Operand],
    destination: &Place,
    target: usize,
    from_app: &RelationApp,
    stmt_constraints: &[Expr],
    modified_locals: &HashSet<usize>,
    callee_path: &str,
    call_idx: usize,
    owner_method: &str,
) {
    let collection_local = chc_ctx
        .resolve_collection_local(args)
        .expect("internal VecPop receiver should resolve to an owning local");
    let field_projections = chc_ctx.resolve_collection_field_projections(args);
    assert!(
        !field_projections.is_empty(),
        "{owner_method} VecPop call #{call_idx} ({callee_path}) should keep struct field projections"
    );
    let converted = collect_field_projections(&field_projections, UnknownProjectionPolicy::Skip);
    assert_eq!(
        converted.len(),
        1,
        "{owner_method} VecPop call #{call_idx} ({callee_path}) should resolve exactly one field projection"
    );

    let struct_state_idx = chc_ctx
        .ref_resolution
        .ref_arg_pointee_idx
        .get(&collection_local)
        .copied()
        .or_else(|| chc_ctx.state_var_mgr.local_to_state_idx.get(&collection_local).copied())
        .expect("internal VecPop receiver should map to a state var");

    let before_rules = chc_ctx.vc.rules.len();
    let cx = ChcCallContext {
        stub: StubKind::VecPop,
        args,
        destination,
        target,
        from_app,
        stmt_constraints,
        modified_locals,
    };
    chc_ctx.codegen_call_vec_core(&cx);

    assert_eq!(
        chc_ctx.vc.rules.len(),
        before_rules + 1,
        "{owner_method} internal VecPop call #{call_idx} should emit exactly one CHC rule"
    );

    let rule = chc_ctx.vc.rules.last().expect("internal VecPop rule");
    let owner_out_name = &chc_ctx.state_var_mgr.output_state_vars[struct_state_idx].0;
    let owner_promoted =
        rule.head.args[struct_state_idx].to_string().contains(owner_out_name.as_ref());
    let owner_bound = rule.body.constraints.iter().any(|constraint| {
        constraint_tree_contains(constraint, &|expr| {
            matches!(expr.value(), ExprValue::Var { name } if name == owner_out_name.as_ref())
        })
    });
    assert!(
        owner_promoted && owner_bound,
        "{owner_method} VecPop call #{call_idx} ({callee_path}) should update and constrain owner state slot {} ({})",
        struct_state_idx,
        owner_out_name
    );

    let dest_local = destination.local;
    let dest_vec_idx =
        chc_ctx.try_state_idx_for_local(dest_local).expect("VecPop destination state index");
    let field_count = if chc_ctx.flatten.flattened_tuple_locals.contains(&dest_local) {
        chc_ctx.flattened_field_count(dest_local)
    } else {
        1
    };

    let promoted = (0..field_count).all(|offset| {
        let out_name = &chc_ctx.state_var_mgr.output_state_vars[dest_vec_idx + offset].0;
        rule.head.args[dest_vec_idx + offset].to_string().contains(out_name.as_ref())
    });
    let bound = (0..field_count).all(|offset| {
        let out_name = &chc_ctx.state_var_mgr.output_state_vars[dest_vec_idx + offset].0;
        rule.body.constraints.iter().any(|constraint| {
            constraint_tree_contains(constraint, &|expr| {
                matches!(expr.value(), ExprValue::Var { name } if name == out_name.as_ref())
            })
        })
    });
    assert!(
        !promoted || bound,
        "{owner_method} VecPop call #{call_idx} ({callee_path}) promoted destination local {} \
         without binding all {} output slot(s)",
        dest_local,
        field_count
    );
}

#[test]
fn test_array_solver_pop_internal_vecpop_calls_bind_promoted_destinations() {
    with_array_solver_pop_vecpop_calls(
        |_tcx,
         chc_ctx,
         args,
         destination,
         target,
         from_app,
         stmt_constraints,
         modified_locals,
         _bb_idx,
         callee_path,
         call_idx| {
            assert_internal_struct_vecpop_contract(
                chc_ctx,
                args,
                destination,
                target,
                from_app,
                stmt_constraints,
                modified_locals,
                callee_path,
                call_idx,
                "ArraySolver::pop",
            );
        },
    );
}

#[test]
fn test_array_solver_remove_assignment_internal_vecpop_calls_update_owner_state() {
    with_array_solver_remove_assignment_vecpop_calls(
        |_tcx,
         chc_ctx,
         args,
         destination,
         target,
         from_app,
         stmt_constraints,
         modified_locals,
         _bb_idx,
         callee_path,
         call_idx| {
            assert_internal_struct_vecpop_contract(
                chc_ctx,
                args,
                destination,
                target,
                from_app,
                stmt_constraints,
                modified_locals,
                callee_path,
                call_idx,
                "ArraySolver::remove_assignment",
            );
        },
    );
}

/// Part of #4038 D1: Direct infrastructure test for `get_assignment` admission.
///
/// Answers the design gate questions:
/// 1. Does `ArraySolver::get_assignment` resolve to a concrete body?
/// 2. Does it fit `chc_inline_effective_block_limit(...)`?
/// 3. Are all inline arguments translatable?
#[test]
fn test_arrays_get_assignment_call_infrastructure() {
    with_array_solver_method_call(
        "probe_array_solver_get_assignment_empty",
        "ArraySolver::get_assignment",
        |tcx,
         chc_ctx,
         func,
         args,
         _destination,
         _target,
         _from_app,
         _stmt_constraints,
         modified_locals,
         _bb_idx,
         callee_path| {
            // Gate 1: Resolve callee to concrete body.
            let func_ty = func.ty(chc_ctx.body.locals()).expect("call callee type");
            let TyKind::RigidTy(RigidTy::FnDef(def, substs)) = func_ty.kind() else {
                panic!("expected FnDef for get_assignment call, got {func_ty:?}");
            };
            let instance = rustc_public::mir::mono::Instance::resolve(def, &substs)
                .expect("get_assignment instance");
            let inline_body = instance.body().expect("get_assignment body");

            // Gate 2: Budget admission.
            let effective = crate::codegen_ay::shared::count_effective_blocks(&inline_body);
            let limit = super::super::inline_budget::chc_inline_effective_block_limit(
                &inline_body,
                effective,
            );
            assert!(
                effective <= limit,
                "{callee_path} should fit the CHC inline budget: effective={effective}, limit={limit}"
            );

            // Budget note for diagnostics.
            let budget_note = inline_budget_note_arrays(tcx, "ArraySolver::get_assignment");
            assert!(
                !budget_note.is_empty(),
                "budget note should be non-empty for diagnostic tracing"
            );

            // Gate 3: Argument resolution — all args should be translatable.
            let params: Vec<_> = args
                .iter()
                .map(|arg| chc_ctx.resolve_ref_or_const_referent(arg, modified_locals))
                .collect();
            assert!(
                params.iter().all(Option::is_some),
                "{callee_path} should have translatable inline arguments, params={params:?}"
            );
        },
    );
}

#[test]
fn test_array_solver_datatype_is_not_accepted_as_vec_fields() {
    const SOURCE: &str = r#"
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

        fn probe_array_solver_param(solver: ArraySolver) -> bool {
            solver.dirty
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_array_solver_param");
        let body = instance.body().expect("function body");
        assert_eq!(body.arg_locals().len(), 1, "expected exactly one ArraySolver arg");

        let _chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_array_solver_param", ChcConfig::default());
        let solver_sort =
            ChcCtx::translate_ty(body.locals()[1].ty).expect("ArraySolver type should translate");
        let solver_expr = Expr::var("solver", solver_sort);

        assert_eq!(
            solver_expr.sort().datatype_name(),
            Some("ArraySolver"),
            "regression precondition: expected ArraySolver datatype expression"
        );
        let dt = solver_expr.sort().datatype_sort().expect("ArraySolver datatype sort");
        let field_names: Vec<_> =
            dt.constructors[0].fields.iter().map(|field| field.name.clone()).collect();
        assert!(
            ChcVecFields::extract_without_name(solver_expr.clone()).is_none(),
            "non-Vec datatypes must not be accepted by ChcVecFields; fields={field_names:?}"
        );
        assert!(
            ChcCtx::select_vec_len_datatype_field(&solver_expr).is_none(),
            "VecLen C1 helper must reject owner datatypes; fields={field_names:?}"
        );
    });
}

/// Part of #4038 D1: Isolated probe — does `get_assignment` produce inferable
/// predicates when translated through `mir_to_chc`?
///
/// This separates "admission" (does the callee fit the budget) from "body
/// precision" (does the admitted body stay precise without falling back to
/// `P_inf_*` summaries). Uses the isolated `probe_array_solver_get_assignment_empty`
/// which only calls `get_assignment` on an empty solver — no nested `push`/`pop`
/// or `record_assignment` calls.
#[test]
fn test_arrays_get_assignment_empty_probe_inferable_count() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    reset_bootstrap_arrays_tier3_counters();

    let fn_name = "probe_array_solver_get_assignment_empty";
    let mut inferable_decls: Vec<String> = Vec::new();
    let mut has_p_inf_rule = false;
    let mut budget_notes: Vec<String> = Vec::new();

    with_test_ay_ctx_for_source(BOOTSTRAP_ARRAYS_TIER3_SOURCE, |ctx| {
        budget_notes = vec![
            inline_budget_note_arrays(ctx.tcx, "ArraySolver::get_assignment"),
            inline_budget_note_arrays(ctx.tcx, "ArraySolver::new"),
        ];

        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());

        assert_vc_structure(&vc, fn_name, body.blocks.len());
        assert_has_nontrivial_transition_constraints(&vc, fn_name);
        (inferable_decls, has_p_inf_rule) = inferable_predicate_artifacts(&vc);
    });

    let fallback_counts = get_chc_fallback_counts();
    let fallback_count = fallback_counts.get(fn_name).copied().unwrap_or(0);
    let inferable_count = crate::codegen_ay::take_inferable_predicate_count();
    let unhandled_calls = crate::codegen_ay::take_unhandled_call_by_fn();
    let unhandled_count = unhandled_calls.get(fn_name).copied().unwrap_or(0);

    // Record the current state for gate classification.
    // If these assertions fail, the failure message tells us exactly which gate
    // is first: admission (budget), body precision (inferable), or nested calls.
    eprintln!(
        "[arrays_get_assignment_empty] inferable_decls={inferable_decls:?}, \
         has_p_inf_rule={has_p_inf_rule}, fallback_count={fallback_count}, \
         inferable_count={inferable_count}, unhandled_count={unhandled_count}, \
         budgets={budget_notes:?}"
    );

    // Gate classification: all three gates pass at the unit-test level.
    // get_assignment effective=11, limit=16 → admission PASS.
    // Zero inferable predicates, zero fallbacks → body precision PASS.
    // The production gap (compiletest P_inf_ArraySolver::get_assignment)
    // must come from MIR transforms, target spec, or stdlib differences
    // not present in the unit-test compilation pipeline.
    assert_eq!(
        inferable_count, 0,
        "{fn_name}: isolated get_assignment probe should emit zero inferable predicates, \
         got {inferable_count}. inferable_decls={inferable_decls:?}, budgets={budget_notes:?}"
    );
    assert_eq!(
        fallback_count, 0,
        "{fn_name}: isolated get_assignment probe should have zero fallbacks, \
         got {fallback_count}. map={fallback_counts:?}, budgets={budget_notes:?}"
    );

    reset_bootstrap_arrays_tier3_counters();
}

/// Part of #4038 D1: Isolated probe — does `get_assignment` after `set_assignment`
/// produce inferable predicates?
///
/// This tests the slightly wider surface: `set_assignment` mutates the solver,
/// then `get_assignment` reads it back. Both are while-loop helpers over Vec
/// fields, so both exercise the inline walker's loop replay.
#[test]
fn test_arrays_get_assignment_after_set_probe_inferable_count() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    reset_bootstrap_arrays_tier3_counters();

    let fn_name = "probe_array_solver_get_assignment_after_set";
    let mut inferable_decls: Vec<String> = Vec::new();
    let mut has_p_inf_rule = false;
    let mut budget_notes: Vec<String> = Vec::new();

    with_test_ay_ctx_for_source(BOOTSTRAP_ARRAYS_TIER3_SOURCE, |ctx| {
        budget_notes = vec![
            inline_budget_note_arrays(ctx.tcx, "ArraySolver::get_assignment"),
            inline_budget_note_arrays(ctx.tcx, "ArraySolver::set_assignment"),
            inline_budget_note_arrays(ctx.tcx, "ArraySolver::new"),
        ];

        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());

        assert_vc_structure(&vc, fn_name, body.blocks.len());
        assert_has_nontrivial_transition_constraints(&vc, fn_name);
        (inferable_decls, has_p_inf_rule) = inferable_predicate_artifacts(&vc);
    });

    let fallback_counts = get_chc_fallback_counts();
    let fallback_count = fallback_counts.get(fn_name).copied().unwrap_or(0);
    let inferable_count = crate::codegen_ay::take_inferable_predicate_count();
    let unhandled_calls = crate::codegen_ay::take_unhandled_call_by_fn();
    let unhandled_count = unhandled_calls.get(fn_name).copied().unwrap_or(0);

    eprintln!(
        "[arrays_get_assignment_after_set] inferable_decls={inferable_decls:?}, \
         has_p_inf_rule={has_p_inf_rule}, fallback_count={fallback_count}, \
         inferable_count={inferable_count}, unhandled_count={unhandled_count}, \
         budgets={budget_notes:?}"
    );

    // Gate classification: both helpers pass all gates at unit-test level.
    // get_assignment effective=11, set_assignment effective=12, both within limit=16.
    // Zero inferable predicates, zero fallbacks for the combined set+get path.
    assert_eq!(
        inferable_count, 0,
        "{fn_name}: set+get probe should emit zero inferable predicates, \
         got {inferable_count}. inferable_decls={inferable_decls:?}, budgets={budget_notes:?}"
    );
    assert_eq!(
        fallback_count, 0,
        "{fn_name}: set+get probe should have zero fallbacks, \
         got {fallback_count}. map={fallback_counts:?}, budgets={budget_notes:?}"
    );

    reset_bootstrap_arrays_tier3_counters();
}
