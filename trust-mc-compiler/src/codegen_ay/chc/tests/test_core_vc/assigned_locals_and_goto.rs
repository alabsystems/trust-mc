// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

// =============================================================================
// codegen_rules.rs + codegen_stmt.rs edge-path coverage (Part of #2188)
// =============================================================================

#[test]
fn test_collect_assigned_locals_includes_direct_assignment_to_arg() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_direct_assign(mut x: u8) {
            x = x.wrapping_add(1);
            let _ = x;
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_direct_assign");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_direct_assign", ChcConfig::default());

        let assigned = chc_ctx.collect_assigned_locals();
        assert!(
            assigned.contains(&1),
            "argument local _1 should be collected for direct assignment"
        );
    });
}

#[test]
fn test_collect_assigned_locals_ignores_projection_only_assignment() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_projection_only(mut pair: (u8, u8)) {
            pair.0 = 9;
            let _ = pair.0;
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_projection_only");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_projection_only", ChcConfig::default());

        let assigned = chc_ctx.collect_assigned_locals();
        assert!(
            !assigned.contains(&1),
            "projection-only assignment should not mark argument local _1 as directly assigned"
        );
    });
}

#[test]
fn test_collect_assigned_locals_tracks_multiple_direct_args() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_multi_assign(mut x: u8, mut y: u8) {
            x = x.wrapping_add(1);
            y = y.wrapping_add(2);
            let _ = (x, y);
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_multi_assign");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_multi_assign", ChcConfig::default());

        let assigned = chc_ctx.collect_assigned_locals();
        assert!(assigned.contains(&1), "argument local _1 should be marked assigned");
        assert!(assigned.contains(&2), "argument local _2 should be marked assigned");
    });
}

#[test]
fn test_collect_assigned_locals_skips_read_only_args() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_read_only(x: u8, y: u8) -> u8 {
            x.wrapping_add(y)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_read_only");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_read_only", ChcConfig::default());

        let assigned = chc_ctx.collect_assigned_locals();
        assert!(
            !assigned.contains(&1),
            "argument local _1 should remain unassigned when only read"
        );
        assert!(
            !assigned.contains(&2),
            "argument local _2 should remain unassigned when only read"
        );
    });
}

#[test]
fn test_block_relation_name_uses_fn_prefix() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_rel_name() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_rel_name");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_rel_name", ChcConfig::default());

        assert_eq!(chc_ctx.block_relation_name(3), "probe_rel_name__bb3");
    });
}

#[test]
fn test_emit_guarded_goto_rule_true_delegates_to_unconditional_rule() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_emit_true(x: u32) -> u32 { x }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_emit_true");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_emit_true", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let state_args: Vec<Expr> = chc_ctx
            .state_var_mgr
            .state_vars
            .iter()
            .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
            .collect();
        let from_rel = chc_ctx.block_relations.get(&0).expect("bb0 relation").clone();
        let from_app = RelationApp::new(from_rel.clone(), state_args.clone());
        let stmt_constraints = vec![Expr::bool_const(true)];

        let before = chc_ctx.vc.rules.len();
        chc_ctx.emit_guarded_goto_rule(
            &from_app,
            0,
            &state_args,
            &stmt_constraints,
            Expr::bool_const(true),
        );
        assert_eq!(chc_ctx.vc.rules.len(), before + 1);

        let emitted = &chc_ctx.vc.rules[before];
        assert_eq!(emitted.head.name, from_rel);
        assert_eq!(
            emitted.body.constraints.len(),
            stmt_constraints.len(),
            "guard=true path should not append an extra guard constraint"
        );
    });
}

#[test]
fn test_emit_guarded_goto_rule_false_emits_no_rule() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_emit_false(x: u32) -> u32 { x }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_emit_false");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_emit_false", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let state_args: Vec<Expr> = chc_ctx
            .state_var_mgr
            .state_vars
            .iter()
            .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
            .collect();
        let from_rel = chc_ctx.block_relations.get(&0).expect("bb0 relation").clone();
        let from_app = RelationApp::new(from_rel, state_args.clone());
        let before = chc_ctx.vc.rules.len();

        chc_ctx.emit_guarded_goto_rule(
            &from_app,
            0,
            &state_args,
            &[Expr::bool_const(true)],
            Expr::bool_const(false),
        );
        assert_eq!(chc_ctx.vc.rules.len(), before, "guard=false should suppress rule emission");
    });
}

#[test]
fn test_emit_guarded_goto_rule_symbolic_guard_appends_constraint() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_emit_symbolic(x: u32) -> u32 { x }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_emit_symbolic");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_emit_symbolic", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let state_args: Vec<Expr> = chc_ctx
            .state_var_mgr
            .state_vars
            .iter()
            .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
            .collect();
        let from_rel = chc_ctx.block_relations.get(&0).expect("bb0 relation").clone();
        let from_app = RelationApp::new(from_rel.clone(), state_args.clone());
        let stmt_constraints = vec![Expr::bool_const(true)];
        let guard = Expr::var("__guard", Sort::bool());
        let before = chc_ctx.vc.rules.len();

        chc_ctx.emit_guarded_goto_rule(&from_app, 0, &state_args, &stmt_constraints, guard.clone());
        assert_eq!(chc_ctx.vc.rules.len(), before + 1);

        let emitted = &chc_ctx.vc.rules[before];
        assert_eq!(emitted.head.name, from_rel);
        assert_eq!(emitted.body.constraints.len(), stmt_constraints.len() + 1);
        assert_eq!(
            emitted.body.constraints.last().expect("guard constraint").to_string(),
            guard.to_string()
        );
    });
}

#[test]
fn test_emit_guarded_goto_rule_missing_target_is_noop() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_emit_missing_target(x: u32) -> u32 { x }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_emit_missing_target");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_emit_missing_target", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let state_args: Vec<Expr> = chc_ctx
            .state_var_mgr
            .state_vars
            .iter()
            .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
            .collect();
        let from_rel = chc_ctx.block_relations.get(&0).expect("bb0 relation").clone();
        let from_app = RelationApp::new(from_rel, state_args.clone());
        let before = chc_ctx.vc.rules.len();

        chc_ctx.emit_guarded_goto_rule(
            &from_app,
            usize::MAX,
            &state_args,
            &[Expr::bool_const(true)],
            Expr::var("__guard_missing_target", Sort::bool()),
        );
        assert_eq!(
            chc_ctx.vc.rules.len(),
            before,
            "missing target should not emit a guarded transition rule"
        );
    });
}

#[test]
fn test_emit_goto_rule_missing_target_is_noop() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_missing_target(x: u32) -> u32 { x }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_missing_target");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_missing_target", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let state_args: Vec<Expr> = chc_ctx
            .state_var_mgr
            .state_vars
            .iter()
            .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
            .collect();
        let from_rel = chc_ctx.block_relations.get(&0).expect("bb0 relation").clone();
        let from_app = RelationApp::new(from_rel, state_args.clone());
        let before = chc_ctx.vc.rules.len();

        chc_ctx.emit_goto_rule(&from_app, usize::MAX, &state_args, &[Expr::bool_const(true)]);
        assert_eq!(chc_ctx.vc.rules.len(), before, "missing target should not emit a rule");
    });
}
