// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Direct unit tests for `codegen_call_hashset` via `ChcCallContext`.
//! Unlike `test_call_collections.rs` (which tests through the full `mir_to_chc`
//! pipeline), these tests call `codegen_call_hashset` directly to verify:
//! - Length output tracking through output state vars
//! - Empty-args fallback behavior
//!
//! Part of #2529 (untested production function coverage).

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used)]

use super::super::chc_call_context::ChcCallContext;
use super::super::codegen_call_collections::CallCollections;
use super::common::*;
use ay_bindings::{Expr, ExprValue, Sort};

const HASHSET_DIRECT_CALL_SOURCE: &str = r#"
    #![allow(dead_code)]
    use std::collections::HashSet;

    pub fn probe_hashset_insert_direct() -> bool {
        let mut s: HashSet<u32> = HashSet::new();
        s.insert(7)
    }
"#;

/// Find the first HashSetInsert call terminator in the given body,
/// returning (bb_idx, args, destination, target).
fn find_hashset_insert_call(
    chc_ctx: &ChcCtx<'_, '_>,
    body: &rustc_public::mir::Body,
) -> (usize, Vec<rustc_public::mir::Operand>, rustc_public::mir::Place, usize) {
    for (bb_idx, block) in body.blocks.iter().enumerate() {
        if let rustc_public::mir::TerminatorKind::Call {
            func,
            args,
            destination,
            target: Some(target),
            ..
        } = &block.terminator.kind
            && chc_ctx.detect_stub(func) == Some(StubKind::HashSetInsert)
        {
            return (bb_idx, args.clone(), destination.clone(), *target);
        }
    }
    unreachable!("expected HashSetInsert call terminator in body");
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

#[test]
fn test_codegen_call_hashset_direct_tracks_len_output() {
    with_test_ay_ctx_for_source(HASHSET_DIRECT_CALL_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_hashset_insert_direct");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_hashset_insert_direct", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let (bb_idx, args, destination, target) = find_hashset_insert_call(&chc_ctx, &body);
        let from_app = build_from_app(&chc_ctx, bb_idx);
        let stmt_constraints = [Expr::bool_const(true)];

        let before_rules = chc_ctx.vc.rules.len();
        let cx = ChcCallContext {
            stub: StubKind::HashSetInsert,
            args: &args,
            destination: &destination,
            target,
            from_app: &from_app,
            stmt_constraints: &stmt_constraints,
            modified_locals: &HashSet::new(),
        };
        chc_ctx.codegen_call_hashset(&cx);

        assert_eq!(chc_ctx.vc.rules.len(), before_rules + 1, "expected one hashset rule");
        let rule = chc_ctx.vc.rules.last().expect("hashset call should emit one rule");

        let modified_len_var = chc_ctx
            .collections
            .len_state
            .modified_len_vars
            .iter()
            .next()
            .cloned()
            .expect("hashset insert should mark a tracked len var as modified");
        let len_out_name = names::out_name(&modified_len_var);
        let len_idx = chc_ctx
            .state_var_mgr
            .output_state_vars
            .iter()
            .position(|(name, _)| &**name == len_out_name.as_str())
            .expect("expected tracked len output variable slot");

        let len_head_arg =
            rule.head.args.get(len_idx).expect("len output slot should exist in rule head");
        assert!(
            matches!(len_head_arg.value(), ExprValue::Var { name } if name == &len_out_name),
            "hashset direct call should route tracked len slot through output var, \
             got {:?}",
            len_head_arg.value(),
        );

        assert!(
            rule.body.constraints.iter().any(|c| c.to_string().contains(&len_out_name)),
            "hashset direct call should emit len-update equality constraint"
        );
    });
}

#[test]
fn test_codegen_call_hashset_direct_empty_args_no_len_update() {
    with_test_ay_ctx_for_source(HASHSET_DIRECT_CALL_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_hashset_insert_direct");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_hashset_insert_direct", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let (bb_idx, _args, destination, target) = find_hashset_insert_call(&chc_ctx, &body);
        let from_app = build_from_app(&chc_ctx, bb_idx);
        let stmt_constraints = [Expr::bool_const(true)];

        let before_rules = chc_ctx.vc.rules.len();
        let cx = ChcCallContext {
            stub: StubKind::HashSetInsert,
            args: &[],
            destination: &destination,
            target,
            from_app: &from_app,
            stmt_constraints: &stmt_constraints,
            modified_locals: &HashSet::new(),
        };
        chc_ctx.codegen_call_hashset(&cx);

        assert_eq!(chc_ctx.vc.rules.len(), before_rules + 1, "expected one hashset rule");
        let rule = chc_ctx.vc.rules.last().expect("hashset fallback call should emit one rule");
        assert_eq!(
            rule.body.constraints.len(),
            1,
            "empty-args fallback should only keep the original stmt constraints"
        );
        assert!(
            chc_ctx.collections.len_state.modified_len_vars.is_empty(),
            "empty-args fallback must not mark collection len state as modified"
        );
    });
}

#[test]
fn test_codegen_call_hashset_direct_non_array_sort_emits_error_rule() {
    with_test_ay_ctx_for_source(HASHSET_DIRECT_CALL_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_hashset_insert_direct");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_hashset_insert_direct", ChcConfig::default());
        chc_ctx.declare_block_relations();
        chc_ctx.declare_error_relation();

        let (bb_idx, args, destination, target) = find_hashset_insert_call(&chc_ctx, &body);
        let from_app = build_from_app(&chc_ctx, bb_idx);
        let stmt_constraints = [Expr::bool_const(true)];

        let collection_local =
            chc_ctx.resolve_collection_local(&args).expect("hashset insert should resolve local");
        let collection_idx = chc_ctx.state_idx_for_local(collection_local);
        chc_ctx.state_var_mgr.state_vars[collection_idx].1 = Sort::bool();
        chc_ctx.state_var_mgr.output_state_vars[collection_idx].1 = Sort::bool();

        let before_rules = chc_ctx.vc.rules.len();
        let cx = ChcCallContext {
            stub: StubKind::HashSetInsert,
            args: &args,
            destination: &destination,
            target,
            from_app: &from_app,
            stmt_constraints: &stmt_constraints,
            modified_locals: &HashSet::new(),
        };
        chc_ctx.codegen_call_hashset(&cx);

        assert_eq!(
            chc_ctx.vc.rules.len(),
            before_rules + 1,
            "forced-failure hashset path should emit one fail-closed rule"
        );
        let rule = chc_ctx.vc.rules.last().expect("hashset fail-closed call should emit a rule");
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
