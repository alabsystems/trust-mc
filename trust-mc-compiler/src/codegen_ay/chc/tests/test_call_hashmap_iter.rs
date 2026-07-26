// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Direct unit tests for `codegen_call_hashmap_iter.rs`.
//! Verifies HashMap iterator-next output routing and fallback behavior by
//! invoking `codegen_call_hashmap_iter` directly from MIR-extracted call sites.
//!
//! Part of #2512 (codegen_ay test coverage gap).

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used)]

use super::super::chc_call_context::ChcCallContext;
use super::super::codegen_call_hashmap_iter::CallHashmapIter;
use super::common::*;
use ay_bindings::{Expr, ExprValue, Sort};

const HASHMAP_ITER_DIRECT_SOURCE: &str = r#"
    #![allow(dead_code)]
    use std::collections::HashMap;

    pub fn probe_hashmap_iter_next_direct() {
        let mut map: HashMap<u8, u16> = HashMap::new();
        map.insert(1, 10);
        let mut iter = map.into_iter();
        let _ = iter.next();
    }
"#;

/// Find the first `HashMapIterNext` call terminator in MIR.
fn find_hashmap_iter_next_call(
    chc_ctx: &ChcCtx<'_, '_>,
    body: &rustc_public::mir::Body,
) -> (usize, Vec<Operand>, Place, rustc_public::mir::BasicBlockIdx) {
    for (bb_idx, block) in body.blocks.iter().enumerate() {
        if let rustc_public::mir::TerminatorKind::Call {
            func,
            args,
            destination,
            target: Some(target),
            ..
        } = &block.terminator.kind
            && chc_ctx.detect_hashmap_iter_stub(func) == Some(StubKind::HashMapIterNext)
        {
            return (bb_idx, args.clone(), destination.clone(), *target);
        }
    }
    unreachable!("expected HashMapIterNext call terminator in body");
}

/// Build a `RelationApp` for the given block index from `chc_ctx`.
fn build_from_app(chc_ctx: &ChcCtx<'_, '_>, bb_idx: usize) -> RelationApp {
    let from_rel =
        chc_ctx.block_relations.get(&bb_idx).expect("source relation for call block").clone();
    let state_args: Vec<_> = chc_ctx
        .state_var_mgr
        .state_vars
        .iter()
        .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
        .collect();
    RelationApp::new(&from_rel, state_args)
}

fn resolve_iter_local(chc_ctx: &ChcCtx<'_, '_>, args: &[Operand]) -> usize {
    let first_arg = args.first().expect("HashMapIterNext should have self arg");
    match first_arg {
        Operand::Copy(place) | Operand::Move(place) => {
            let ref_local = place.local;
            chc_ctx.ref_resolution.ref_targets.get(&ref_local).map_or(ref_local, |rt| rt.local)
        }
        Operand::Constant(_) => {
            unreachable!("HashMapIterNext first arg should be Copy/Move place, not constant")
        }
    }
}

fn is_var_named(expr: &Expr, expected_name: &str) -> bool {
    matches!(expr.value(), ExprValue::Var { name } if name == expected_name)
}

#[test]
fn test_codegen_call_hashmap_iter_next_updates_iter_and_destination_outputs() {
    with_test_ay_ctx_for_source(HASHMAP_ITER_DIRECT_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_hashmap_iter_next_direct");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_hashmap_iter_next_direct", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let (bb_idx, args, destination, target) = find_hashmap_iter_next_call(&chc_ctx, &body);
        let from_app = build_from_app(&chc_ctx, bb_idx);
        let stmt_constraints = [Expr::bool_const(true)];
        let modified_locals: HashSet<usize> = HashSet::new();

        let dest_local = destination.local;
        let dest_vec_idx = chc_ctx.state_idx_for_local(dest_local);
        let dest_out_name = chc_ctx.state_var_mgr.output_state_vars[dest_vec_idx].0.clone();

        let iter_local = resolve_iter_local(&chc_ctx, &args);
        let iter_vec_idx = chc_ctx.state_idx_for_local(iter_local);
        let iter_out_name = chc_ctx.state_var_mgr.output_state_vars[iter_vec_idx].0.clone();

        let before_rules = chc_ctx.vc.rules.len();
        let cx = ChcCallContext {
            stub: StubKind::HashMapIterNext,
            args: &args,
            destination: &destination,
            target,
            from_app: &from_app,
            stmt_constraints: &stmt_constraints,
            modified_locals: &modified_locals,
        };
        chc_ctx.codegen_call_hashmap_iter(&cx);

        assert_eq!(chc_ctx.vc.rules.len(), before_rules + 1, "expected one hashmap-iter rule");
        let rule = chc_ctx.vc.rules.last().expect("HashMapIterNext should emit one rule");

        let iter_head_arg =
            rule.head.args.get(iter_vec_idx).expect("iter local slot should exist in rule head");
        assert!(
            is_var_named(iter_head_arg, &iter_out_name),
            "iterator slot should route through output var {iter_out_name}, got {:?}",
            iter_head_arg.value()
        );

        let dest_head_arg =
            rule.head.args.get(dest_vec_idx).expect("destination slot should exist in rule head");
        assert!(
            is_var_named(dest_head_arg, &dest_out_name),
            "destination slot should route through output var {dest_out_name}, got {:?}",
            dest_head_arg.value()
        );

        assert!(
            rule.body.constraints.iter().any(is_hashmap_iter_membership_constraint),
            "HashMapIterNext should emit membership invariant constraint"
        );
        assert!(
            rule.body.constraints.iter().any(|c| c.to_string().contains(&*iter_out_name)),
            "HashMapIterNext should constrain iterator output var update"
        );
    });
}

#[test]
fn test_codegen_call_hashmap_iter_next_empty_args_keeps_original_constraints() {
    with_test_ay_ctx_for_source(HASHMAP_ITER_DIRECT_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_hashmap_iter_next_direct");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_hashmap_iter_next_direct", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let (bb_idx, args, destination, target) = find_hashmap_iter_next_call(&chc_ctx, &body);
        let from_app = build_from_app(&chc_ctx, bb_idx);
        let stmt_constraints = [Expr::bool_const(true)];
        let modified_locals: HashSet<usize> = HashSet::new();

        let dest_local = destination.local;
        let dest_vec_idx = chc_ctx.state_idx_for_local(dest_local);
        let dest_out_name = chc_ctx.state_var_mgr.output_state_vars[dest_vec_idx].0.clone();

        let iter_local = resolve_iter_local(&chc_ctx, &args);
        let iter_vec_idx = chc_ctx.state_idx_for_local(iter_local);
        let iter_in_name = chc_ctx.state_var_mgr.state_vars[iter_vec_idx].0.clone();

        let before_rules = chc_ctx.vc.rules.len();
        let cx = ChcCallContext {
            stub: StubKind::HashMapIterNext,
            args: &[],
            destination: &destination,
            target,
            from_app: &from_app,
            stmt_constraints: &stmt_constraints,
            modified_locals: &modified_locals,
        };
        chc_ctx.codegen_call_hashmap_iter(&cx);

        assert_eq!(chc_ctx.vc.rules.len(), before_rules + 1, "expected one hashmap-iter rule");
        let rule = chc_ctx.vc.rules.last().expect("HashMapIterNext fallback should emit one rule");

        assert_eq!(
            rule.body.constraints.len(),
            stmt_constraints.len(),
            "missing-args fallback should keep only original stmt constraints"
        );
        assert!(
            rule.body.constraints.iter().all(|c| !is_hashmap_iter_membership_constraint(c)),
            "missing-args fallback must not add membership invariant constraints"
        );

        let dest_head_arg =
            rule.head.args.get(dest_vec_idx).expect("destination slot should exist in rule head");
        assert!(
            is_var_named(dest_head_arg, &dest_out_name),
            "fallback should still route destination through output var {dest_out_name}"
        );

        let iter_head_arg =
            rule.head.args.get(iter_vec_idx).expect("iter slot should exist in rule head");
        assert!(
            is_var_named(iter_head_arg, &iter_in_name),
            "fallback should preserve iterator input var {iter_in_name}"
        );
    });
}

#[test]
fn test_codegen_call_hashmap_iter_untracked_iter_still_emits_destination_rule() {
    with_test_ay_ctx_for_source(HASHMAP_ITER_DIRECT_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_hashmap_iter_next_direct");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_hashmap_iter_next_direct", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let (bb_idx, args, destination, target) = find_hashmap_iter_next_call(&chc_ctx, &body);
        let from_app = build_from_app(&chc_ctx, bb_idx);
        let stmt_constraints = [Expr::bool_const(true)];
        let modified_locals: HashSet<usize> = HashSet::new();

        let dest_local = destination.local;
        let dest_vec_idx = chc_ctx.state_idx_for_local(dest_local);
        let dest_out_name = chc_ctx.state_var_mgr.output_state_vars[dest_vec_idx].0.clone();

        let iter_local = resolve_iter_local(&chc_ctx, &args);
        let iter_vec_idx = chc_ctx.state_idx_for_local(iter_local);
        let iter_in_name = chc_ctx.state_var_mgr.state_vars[iter_vec_idx].0.clone();
        let removed = chc_ctx.state_var_mgr.local_to_state_idx.remove(&iter_local);
        assert!(removed.is_some(), "test setup requires tracked iterator local {iter_local}");

        let before_rules = chc_ctx.vc.rules.len();
        let cx = ChcCallContext {
            stub: StubKind::HashMapIterNext,
            args: &args,
            destination: &destination,
            target,
            from_app: &from_app,
            stmt_constraints: &stmt_constraints,
            modified_locals: &modified_locals,
        };
        chc_ctx.codegen_call_hashmap_iter(&cx);

        assert_eq!(
            chc_ctx.vc.rules.len(),
            before_rules + 1,
            "untracked iterator local should still emit one successor rule"
        );

        let rule =
            chc_ctx.vc.rules.last().expect("HashMapIterNext fallback path should emit one rule");
        let dest_head_arg =
            rule.head.args.get(dest_vec_idx).expect("destination slot should exist in rule head");
        assert!(
            is_var_named(dest_head_arg, &dest_out_name),
            "destination slot should still route through output var {dest_out_name}"
        );

        let iter_head_arg =
            rule.head.args.get(iter_vec_idx).expect("iterator slot should exist in rule head");
        assert!(
            is_var_named(iter_head_arg, &iter_in_name),
            "untracked iterator local should preserve the input var {iter_in_name}"
        );
    });
}

#[test]
fn test_codegen_call_hashmap_iter_non_datatype_iter_emits_error_rule() {
    with_test_ay_ctx_for_source(HASHMAP_ITER_DIRECT_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_hashmap_iter_next_direct");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_hashmap_iter_next_direct", ChcConfig::default());
        chc_ctx.declare_block_relations();
        chc_ctx.declare_error_relation();

        let (bb_idx, args, destination, target) = find_hashmap_iter_next_call(&chc_ctx, &body);
        let from_app = build_from_app(&chc_ctx, bb_idx);
        let stmt_constraints = [Expr::bool_const(true)];
        let modified_locals: HashSet<usize> = HashSet::new();

        let iter_local = resolve_iter_local(&chc_ctx, &args);
        let iter_vec_idx = chc_ctx.state_idx_for_local(iter_local);
        chc_ctx.state_var_mgr.state_vars[iter_vec_idx].1 = Sort::bool();
        chc_ctx.state_var_mgr.output_state_vars[iter_vec_idx].1 = Sort::bool();

        let before_rules = chc_ctx.vc.rules.len();
        let cx = ChcCallContext {
            stub: StubKind::HashMapIterNext,
            args: &args,
            destination: &destination,
            target,
            from_app: &from_app,
            stmt_constraints: &stmt_constraints,
            modified_locals: &modified_locals,
        };
        chc_ctx.codegen_call_hashmap_iter(&cx);

        assert_eq!(
            chc_ctx.vc.rules.len(),
            before_rules + 1,
            "forced-failure hashmap_iter path should emit one fail-closed rule"
        );
        let rule =
            chc_ctx.vc.rules.last().expect("hashmap_iter fail-closed call should emit a rule");
        assert_eq!(rule.head.name, "error", "forced-failure path should emit error()");
        assert_eq!(
            rule.body.constraints.len(),
            stmt_constraints.len(),
            "forced-failure error rule should preserve only the original stmt constraints"
        );
        assert!(
            rule.body
                .constraints
                .iter()
                .all(|constraint| !matches!(constraint.value(), ExprValue::BoolConst(false))),
            "forced-failure path must not encode fail-closed semantics as a dead `false` body"
        );
    });
}

// Note: test_codegen_call_hashmap_iter_without_target_emits_no_rule was removed because
// the target=None path is now handled by codegen_call_dispatch_collections (tested in
// test_call_dispatch tests). The trait method now requires ChcCallContext which always
// has a concrete target: BasicBlockIdx.
