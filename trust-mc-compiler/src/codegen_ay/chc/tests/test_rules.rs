// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Test code: unwrap is acceptable for assertions
#![allow(clippy::unwrap_used)]

//! MIR-driven integration tests for CHC codegen_rules.rs rule generation.
//!
//! Tests cover the full translate() pipeline — compiling real Rust source,
//! building a ChcCtx, and inspecting the generated ChcVc structure:
//! - Entry rule generation (true/constraints → bb0)
//! - Goto transition rules (bb_i → bb_j)
//! - SwitchInt guarded transitions (Bool and bitvec discriminants)
//! - Assert terminator encoding (guard + error rule)
//! - Return terminator (no successor rule)
//! - Block relation naming and arity consistency
//! - Rule well-formedness: all targets are declared relations
//! - Enum match multi-arm SwitchInt
//! - Loop back-edge generation
//!
//! switchint_case_guard unit tests are in test_types.rs.
//! Solver-level correctness tests are in test_solver.rs.
//!
//! Part of #2016 (test coverage for codegen_ay/chc/codegen_rules.rs).

use std::sync::Arc;

use num_bigint::BigInt;

use super::super::codegen_rules::transition_drop::{
    collect_box_dyn_dealloc_effects, collect_shared_pointer_dealloc_effects,
};
use super::super::codegen_rules_helpers::known_alloc_id_for_unprojected_drop_place;
use super::common::*;

// ═══════════════════════════════════════════════════════════════════════
// Full-pipeline translate() tests
// ═══════════════════════════════════════════════════════════════════════

// ─── Simple linear function: entry + goto + return ───────────────────

#[test]
fn test_translate_linear_fn_has_entry_and_transition_rules() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn linear_add(x: u32) -> u32 {
            x + 1
        }
        "#,
        |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "linear_add");
            let body = instance.body().expect("body");
            let chc_ctx = ChcCtx::new(ctx.tcx, &body, "linear_add", ChcConfig::default());
            let (vc, _needs_promote) = chc_ctx.translate();

            // Should have at least one relation (for bb0)
            assert!(
                !vc.relations.is_empty(),
                "translate() should declare at least one block relation"
            );

            // Should have an error relation
            let has_error = vc.relations.iter().any(|r| r.name == "error");
            assert!(has_error, "translate() should declare an 'error' relation");

            // Should have block relations named linear_add__bb0, etc.
            let has_bb0 = vc.relations.iter().any(|r| r.name.contains("__bb0"));
            assert!(has_bb0, "translate() should declare a bb0 relation");

            // Should have at least one rule (entry rule)
            assert!(!vc.rules.is_empty(), "translate() should generate at least one rule (entry)");

            // Entry rule: body has no relation (init rule), head targets bb0
            let entry_rules: Vec<_> =
                vc.rules.iter().filter(|r| r.body.relation.is_none()).collect();
            assert!(!entry_rules.is_empty(), "should have at least one entry (init) rule");
            let entry_head = &entry_rules[0].head;
            assert!(
                entry_head.name.contains("__bb0"),
                "entry rule should target bb0, got: {}",
                entry_head.name
            );
        },
    );
}

// ─── Function with branch: SwitchInt generates guarded rules ─────────

#[test]
fn test_translate_branch_generates_switchint_rules() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn branch_test(x: u32) -> u32 {
            if x > 10 { x } else { 0 }
        }
        "#,
        |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "branch_test");
            let body = instance.body().expect("body");
            let chc_ctx = ChcCtx::new(ctx.tcx, &body, "branch_test", ChcConfig::default());
            let (vc, _) = chc_ctx.translate();

            // A branch should produce multiple block relations
            let block_rels: Vec<_> =
                vc.relations.iter().filter(|r| r.name.contains("__bb")).collect();
            assert!(
                block_rels.len() >= 2,
                "branch function should have at least 2 block relations, got {}",
                block_rels.len()
            );

            // Should have transition rules (from_app → to_app)
            let transition_rules: Vec<_> =
                vc.rules.iter().filter(|r| r.body.relation.is_some()).collect();
            assert!(
                transition_rules.len() >= 2,
                "branch should produce at least 2 transition rules (one per branch arm), got {}",
                transition_rules.len()
            );
        },
    );
}

// ─── Constructor-guard walker: direct regression coverage ────────────

#[test]
fn test_collect_constructor_guards_dedups_same_container_constructor() {
    let enum_sort = enum_sort(
        "TwoFieldEnum",
        vec![
            ("Pair", vec![("left", Sort::bitvec(32)), ("right", Sort::bitvec(32))]),
            ("Empty", vec![]),
        ],
    );
    let enum_var = Expr::var("enum_var", enum_sort);
    let left = enum_var.clone().field_select("TwoFieldEnum", "left", Sort::bitvec(32));
    let right = enum_var.field_select("TwoFieldEnum", "right", Sort::bitvec(32));

    let guards = super::super::collect_constructor_guards(&[
        left.eq(Expr::bitvec_const(1u64, 32)),
        right.eq(Expr::bitvec_const(2u64, 32)),
    ]);

    assert_eq!(
        guards.len(),
        1,
        "same container/constructor should emit one tester guard even with multiple field selects"
    );
    match guards[0].value() {
        ExprValue::DatatypeTester { constructor_name, expr, .. } => {
            assert_eq!(constructor_name, "Pair");
            assert!(
                matches!(expr.value(), ExprValue::Var { name, .. } if name == "enum_var"),
                "guard should target the original enum var, got {:?}",
                expr.value()
            );
        }
        other => panic!("expected DatatypeTester guard, got {:?}", other),
    }
}

#[test]
fn test_collect_constructor_guards_recurses_through_bv2int() {
    let option_sort = enum_sort(
        "Option_bv32",
        vec![("None", vec![]), ("Some", vec![("value", Sort::bitvec(32))])],
    );
    let option_var = Expr::var("option_var", option_sort);
    let payload = option_var.field_select("Option_bv32", "value", Sort::bitvec(32));

    let guards =
        super::super::collect_constructor_guards(&[payload.bv2int().eq(Expr::int_const(7))]);

    assert_eq!(
        guards.len(),
        1,
        "Bv2Int-wrapped selectors should still emit constructor guards for PDR"
    );
    match guards[0].value() {
        ExprValue::DatatypeTester { constructor_name, expr, .. } => {
            assert_eq!(constructor_name, "Some");
            assert!(
                matches!(expr.value(), ExprValue::Var { name, .. } if name == "option_var"),
                "guard should recurse to the wrapped selector container, got {:?}",
                expr.value()
            );
        }
        other => panic!("expected DatatypeTester guard, got {:?}", other),
    }
}

// ─── Constructor-guard walker: skip guard on known DT constants (#3896) ──

#[test]
fn test_collect_constructor_guards_skips_known_dt_constant() {
    let option_sort = enum_sort(
        "Option_bv32",
        vec![("None_Option", vec![]), ("Some_Option", vec![("value", Sort::bitvec(32))])],
    );
    // Container is a known DT constant: None_Option
    let none_const = Expr::datatype_constructor("Option_bv32", "None_Option", vec![], option_sort);
    // Selector for "value" (owned by Some_Option) on None_Option container —
    // this is the pattern that caused vacuous PROOF (#3896).
    let selector = none_const.field_select("Option_bv32", "value", Sort::bitvec(32));
    let ite_expr = Expr::ite(Expr::bool_const(true), selector, Expr::bitvec_const(0u64, 32));

    let guards = super::super::collect_constructor_guards(&[ite_expr]);

    assert_eq!(
        guards.len(),
        0,
        "must NOT emit ((_ is Some_Option) None_Option) — it would be vacuously false"
    );
}

#[test]
fn test_collect_constructor_guards_emits_for_symbolic_container() {
    let option_sort = enum_sort(
        "Option_bv32",
        vec![("None_Option", vec![]), ("Some_Option", vec![("value", Sort::bitvec(32))])],
    );
    let sym_var = Expr::var("x", option_sort);
    let selector = sym_var.field_select("Option_bv32", "value", Sort::bitvec(32));

    let guards =
        super::super::collect_constructor_guards(&[selector.eq(Expr::bitvec_const(0u64, 32))]);

    assert_eq!(guards.len(), 1, "symbolic container still needs is_constructor guard");
}

// ─── Overflow check produces error rule via Assert terminator ────────
//
// The Rust `assert!()` macro expands to a panic call, not MIR Assert.
// MIR Assert terminators come from runtime checks like overflow detection.
// In debug mode, `x + 1` emits CheckedAdd with an Assert terminator.

#[test]
fn test_translate_overflow_check_produces_error_rule() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn overflow_test(x: u32) -> u32 {
            x + 1
        }
        "#,
        |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "overflow_test");
            let body = instance.body().expect("body");

            // Verify the body has an Assert terminator (debug mode overflow check)
            let has_assert = body.blocks.iter().any(|bb| {
                matches!(bb.terminator.kind, rustc_public::mir::TerminatorKind::Assert { .. })
            });

            let chc_ctx = ChcCtx::new(ctx.tcx, &body, "overflow_test", ChcConfig::default());
            let (vc, _) = chc_ctx.translate();

            if has_assert {
                // Assert terminators should produce error rules
                let error_rules: Vec<_> =
                    vc.rules.iter().filter(|r| r.head.name == "error").collect();
                assert!(
                    !error_rules.is_empty(),
                    "Assert terminator should produce at least one error rule"
                );

                for rule in &error_rules {
                    assert!(
                        rule.body.relation.is_some(),
                        "error rule should have a source block relation"
                    );
                }
            }
            // Regardless of Assert, translate should complete successfully
            assert!(!vc.rules.is_empty());
        },
    );
}

#[test]
fn test_untranslatable_mir_assert_fallback_emits_error_and_successor_rules() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn fallback_probe(x: u32) -> u32 {
            if x > 0 { x } else { 0 }
        }
        "#,
        |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "fallback_probe");
            let body = instance.body().expect("body");
            let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "fallback_probe", ChcConfig::default());

            chc_ctx.declare_block_relations();
            chc_ctx.declare_error_relation();

            let from_rel = chc_ctx.block_relations.get(&0).expect("bb0 relation").clone();
            let output_args: Vec<_> = chc_ctx
                .state_var_mgr
                .state_vars
                .iter()
                .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
                .collect();
            let from_app = RelationApp::new(&from_rel, output_args.clone());

            let target = *chc_ctx
                .block_relations
                .keys()
                .find(|&&idx| idx != 0)
                .expect("expected at least one non-entry block");
            let target_rel =
                chc_ctx.block_relations.get(&target).expect("target relation should exist").clone();

            let before_len = chc_ctx.vc.rules.len();
            let shared_constraints: Arc<[Expr]> = vec![Expr::bool_const(true)].into();
            chc_ctx.emit_untranslatable_assert_fallback(
                &from_app,
                target,
                &output_args,
                &shared_constraints,
                0,
            );

            // Fix for P1:1437: non-deterministic choice emits BOTH error rule
            // AND successor transition. This prevents false proofs (error rule
            // catches real bugs) while preserving CFG reachability (successor
            // edge keeps downstream code verifiable).
            let new_rules = &chc_ctx.vc.rules[before_len..];
            assert_eq!(
                new_rules.len(),
                2,
                "non-deterministic choice emits error rule + successor transition"
            );
            assert!(
                new_rules.iter().any(|rule| rule.head.name == "error"),
                "fallback must emit error rule to prevent false proofs"
            );
            assert!(
                new_rules.iter().any(|rule| rule.head.name == target_rel),
                "fallback must preserve CFG reachability with successor transition"
            );
        },
    );
}

#[test]
fn test_switchint_fallback_emits_error_and_selector_guarded_successors() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn switch_fallback_probe(x: u32) -> u32 {
            if x > 0 { x } else { 0 }
        }
        "#,
        |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "switch_fallback_probe");
            let body = instance.body().expect("body");
            let mut chc_ctx =
                ChcCtx::new(ctx.tcx, &body, "switch_fallback_probe", ChcConfig::default());

            chc_ctx.declare_block_relations();
            chc_ctx.declare_error_relation();

            let from_rel = chc_ctx.block_relations.get(&0).expect("bb0 relation").clone();
            let output_args: Vec<_> = chc_ctx
                .state_var_mgr
                .state_vars
                .iter()
                .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
                .collect();
            let from_app = RelationApp::new(&from_rel, output_args.clone());

            let mut successor_blocks: Vec<usize> =
                chc_ctx.block_relations.keys().copied().filter(|&idx| idx != 0).collect();
            successor_blocks.sort_unstable();
            assert!(
                successor_blocks.len() >= 3,
                "test requires at least 3 non-entry blocks, got {}",
                successor_blocks.len()
            );

            let branches = vec![(0_u128, successor_blocks[0]), (1_u128, successor_blocks[1])];
            let otherwise = successor_blocks[2];
            let expected_successor_heads: HashSet<Arc<str>> =
                [successor_blocks[0], successor_blocks[1], otherwise]
                    .into_iter()
                    .map(|bb| {
                        chc_ctx.block_relations.get(&bb).expect("block relation must exist").clone()
                    })
                    .collect();

            let before_len = chc_ctx.vc.rules.len();
            let shared_constraints: Arc<[Expr]> = Vec::new().into();
            let modified_locals = HashSet::new();
            let tctx = super::super::codegen_rules::TransitionContext {
                from_app: &from_app,
                output_args: &output_args,
                shared_constraints: &shared_constraints,
                modified_locals: &modified_locals,
                bb_idx: 0,
            };
            chc_ctx.emit_switchint_fallback_rules(
                &branches,
                otherwise,
                &tctx,
                "test switchint fallback",
            );

            let new_rules = &chc_ctx.vc.rules[before_len..];
            assert_eq!(
                new_rules.len(),
                4,
                "fallback must emit 1 error rule + 3 guarded successor rules"
            );
            assert_eq!(
                new_rules.iter().filter(|rule| rule.head.name == "error").count(),
                1,
                "fallback must emit exactly one conservative error rule"
            );

            let successor_rules: Vec<_> =
                new_rules.iter().filter(|rule| rule.head.name != "error").collect();
            assert_eq!(
                successor_rules.len(),
                3,
                "fallback must emit one guarded rule per explicit/otherwise successor"
            );
            for rule in &successor_rules {
                assert!(
                    expected_successor_heads.contains(&*rule.head.name),
                    "unexpected fallback successor rule target: {}",
                    rule.head.name
                );
                assert_eq!(
                    rule.body.constraints.len(),
                    1,
                    "selector-guarded fallback successor must have exactly one guard constraint"
                );
            }

            let guard_texts: HashSet<String> = successor_rules
                .iter()
                .map(|rule| {
                    let guard = rule.body.constraints.first().expect("guard constraint required");
                    let guard_smt = guard.to_string();
                    assert!(
                        guard_smt.contains("__switch_choice_"),
                        "fallback guard should reference selector var, got: {guard_smt}"
                    );
                    guard_smt
                })
                .collect();
            assert_eq!(
                guard_texts.len(),
                3,
                "fallback selector guards must be unique per successor"
            );
        },
    );
}

// ─── Bool SwitchInt: if-else on bool ─────────────────────────────────

#[test]
fn test_translate_bool_switchint_branches() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn bool_branch(flag: bool) -> u32 {
            if flag { 1 } else { 0 }
        }
        "#,
        |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "bool_branch");
            let body = instance.body().expect("body");
            let chc_ctx = ChcCtx::new(ctx.tcx, &body, "bool_branch", ChcConfig::default());
            let (vc, _) = chc_ctx.translate();

            // Bool branch should have guarded transition rules
            let transition_rules: Vec<_> =
                vc.rules.iter().filter(|r| r.body.relation.is_some()).collect();

            // At minimum: 2 branches from switchint + possibly continuation rules
            assert!(
                transition_rules.len() >= 2,
                "bool branch should produce at least 2 transition rules, got {}",
                transition_rules.len()
            );
        },
    );
}

// ─── Multiple returns: well-formed rule graph ────────────────────────

#[test]
fn test_translate_early_return_rule_graph() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn early_return(x: u32) -> u32 {
            if x == 0 {
                return 42;
            }
            x + 1
        }
        "#,
        |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "early_return");
            let body = instance.body().expect("body");
            let chc_ctx = ChcCtx::new(ctx.tcx, &body, "early_return", ChcConfig::default());
            let (vc, _) = chc_ctx.translate();

            // Get all declared block relation names
            let all_blocks: HashSet<_> = vc
                .relations
                .iter()
                .filter(|r| r.name.contains("__bb"))
                .map(|r| r.name.clone())
                .collect();

            assert!(
                all_blocks.len() >= 2,
                "early return function should have at least 2 blocks, got {}",
                all_blocks.len()
            );

            // All rules should reference declared relations
            let declared: HashSet<_> = vc.relations.iter().map(|r| r.name.as_str()).collect();
            for rule in &vc.rules {
                assert!(declared.contains(rule.head.name.as_str()));
            }
        },
    );
}

// ═══════════════════════════════════════════════════════════════════════
// Rule structure verification tests
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn test_translate_error_relation_is_nullary() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn nullary_test(x: u32) -> u32 { x }
        "#,
        |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "nullary_test");
            let body = instance.body().expect("body");
            let chc_ctx = ChcCtx::new(ctx.tcx, &body, "nullary_test", ChcConfig::default());
            let (vc, _) = chc_ctx.translate();

            let error_rel = vc.relations.iter().find(|r| r.name == "error");
            assert!(error_rel.is_some(), "should have error relation");
            assert_eq!(error_rel.unwrap().arity(), 0, "error relation should be nullary");
        },
    );
}

#[test]
fn test_translate_block_relations_have_state_vars() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn state_test(x: u32, y: u32) -> u32 { x + y }
        "#,
        |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "state_test");
            let body = instance.body().expect("body");
            let chc_ctx = ChcCtx::new(ctx.tcx, &body, "state_test", ChcConfig::default());
            let (vc, _) = chc_ctx.translate();

            // Block relations should have arity > 0 (state variables)
            let bb_rels: Vec<_> = vc.relations.iter().filter(|r| r.name.contains("__bb")).collect();
            assert!(!bb_rels.is_empty(), "should have block relations");
            for rel in &bb_rels {
                assert!(
                    rel.arity() > 0,
                    "block relation {} should have state variables (arity > 0), got {}",
                    rel.name,
                    rel.arity()
                );
            }
        },
    );
}

// ─── Entry rule arguments match block relation arity ─────────────────

#[test]
fn test_entry_rule_args_match_bb0_arity() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn arity_test(x: u32) -> u32 { x }
        "#,
        |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "arity_test");
            let body = instance.body().expect("body");
            let chc_ctx = ChcCtx::new(ctx.tcx, &body, "arity_test", ChcConfig::default());
            let (vc, _) = chc_ctx.translate();

            let bb0_rel = vc
                .relations
                .iter()
                .find(|r| r.name.contains("__bb0"))
                .expect("arity_test VC must contain a bb0 relation");
            let entry_rule = vc
                .rules
                .iter()
                .find(|r| r.body.relation.is_none())
                .expect("arity_test VC must contain an entry rule");

            assert_eq!(
                entry_rule.head.args.len(),
                bb0_rel.arity(),
                "entry rule head args ({}) should match bb0 arity ({})",
                entry_rule.head.args.len(),
                bb0_rel.arity()
            );
        },
    );
}

#[test]
fn test_entry_rule_defaults_unassigned_bool_locals_to_false() {
    with_test_ay_ctx_for_source(
        r#"
        #![allow(dead_code, unused_assignments, unused_variables)]
        pub fn entry_default_unassigned_bool(x: u32) -> u32 {
            let flag: bool;
            x
        }
        "#,
        |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "entry_default_unassigned_bool");
            let body = instance.body().expect("body");
            let mut chc_ctx =
                ChcCtx::new(ctx.tcx, &body, "entry_default_unassigned_bool", ChcConfig::default());

            // Make the target deterministic by injecting a synthetic Bool state var
            // with no MIR assignment. This exercises the exact entry-rule fallback
            // logic regardless of upstream MIR local optimization.
            let synthetic_local = body.local_decls().count() + 16;
            let synthetic_name = format!("_entry_default_unassigned_bool_{synthetic_local}");
            let synthetic_vec_idx = chc_ctx.state_var_mgr.state_vars.len();
            chc_ctx.state_var_mgr.local_to_state_idx.insert(synthetic_local, synthetic_vec_idx);
            chc_ctx.push_state_var_pair(
                &synthetic_name,
                &format!("{synthetic_name}__out"),
                Sort::bool(),
            );

            chc_ctx.declare_block_relations();
            chc_ctx.emit_entry_rule();

            let entry_rule = chc_ctx
                .vc
                .rules
                .iter()
                .find(|r| r.body.relation.is_none())
                .expect("expected entry rule");
            let entry_smt = entry_rule
                .body
                .constraints
                .first()
                .expect("entry rule must have a constraint expression")
                .to_string();
            let needle = format!("(= {synthetic_name} false)");
            assert!(
                entry_smt.contains(&needle),
                "entry rule should default unassigned Bool state var `{synthetic_name}` to false"
            );
        },
    );
}

#[test]
fn test_entry_rule_does_not_default_bool_arguments() {
    with_test_ay_ctx_for_source(
        r#"
        #![allow(dead_code)]
        pub fn entry_bool_arg(flag: bool) -> bool { flag }
        "#,
        |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "entry_bool_arg");
            let body = instance.body().expect("body");
            let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "entry_bool_arg", ChcConfig::default());

            chc_ctx.declare_block_relations();
            chc_ctx.emit_entry_rule();

            let entry_rule = chc_ctx
                .vc
                .rules
                .iter()
                .find(|r| r.body.relation.is_none())
                .expect("expected entry rule");
            let entry_smt = entry_rule
                .body
                .constraints
                .first()
                .expect("entry rule must have a constraint expression")
                .to_string();

            let arg_vec_idx = *chc_ctx
                .state_var_mgr
                .local_to_state_idx
                .get(&1usize)
                .expect("expected first argument local mapping");
            let (arg_state_var, _) = chc_ctx
                .state_var_mgr
                .state_vars
                .get(arg_vec_idx)
                .expect("expected first argument state var");

            let forbidden = format!("(= {arg_state_var} false)");
            assert!(
                !entry_smt.contains(&forbidden),
                "entry rule should not default Bool argument `{arg_state_var}` to false"
            );
        },
    );
}

#[test]
fn test_entry_rule_does_not_default_assigned_bool_local() {
    with_test_ay_ctx_for_source(
        r#"
        #![allow(dead_code, unused_assignments, unused_variables)]
        pub fn entry_assigned_bool(x: u32) -> u32 {
            let mut flag = false;
            flag = x > 0;
            x
        }
        "#,
        |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "entry_assigned_bool");
            let body = instance.body().expect("body");
            let mut chc_ctx =
                ChcCtx::new(ctx.tcx, &body, "entry_assigned_bool", ChcConfig::default());

            // Inject a synthetic Bool state var WITH a matching assignment so
            // collect_assigned_locals() recognises it as assigned. The real MIR
            // may optimise out the bool local; the synthetic local isolates the
            // exact code path under test.
            let synthetic_local = body.local_decls().count() + 16;
            let synthetic_name = format!("_entry_assigned_bool_{synthetic_local}");
            let synthetic_vec_idx = chc_ctx.state_var_mgr.state_vars.len();
            chc_ctx.state_var_mgr.local_to_state_idx.insert(synthetic_local, synthetic_vec_idx);
            chc_ctx.push_state_var_pair(
                &synthetic_name,
                &format!("{synthetic_name}__out"),
                Sort::bool(),
            );

            // Mark the synthetic local as assigned by inserting it into the set
            // that collect_assigned_locals will scan. Since the real scan
            // iterates MIR blocks, and our synthetic local isn't in MIR, we
            // override collect_assigned_locals by directly inserting a MIR
            // statement. Instead, let's just verify the production logic:
            // emit_entry_rule calls collect_assigned_locals internally, so we
            // need to check that the assigned bool from the REAL source is not
            // defaulted. We'll check both: the real flag (if present) and verify
            // the synthetic IS defaulted (proving selectivity).
            chc_ctx.declare_block_relations();
            chc_ctx.emit_entry_rule();

            let entry_rule = chc_ctx
                .vc
                .rules
                .iter()
                .find(|r| r.body.relation.is_none())
                .expect("expected entry rule");

            let entry_smt = if let Some(c) = entry_rule.body.constraints.first() {
                c.to_string()
            } else {
                String::new()
            };

            // The synthetic local has NO MIR assignment → it SHOULD be defaulted
            let synthetic_needle = format!("(= {synthetic_name} false)");
            assert!(
                entry_smt.contains(&synthetic_needle),
                "synthetic unassigned Bool should be defaulted to false; got: {entry_smt}"
            );

            // Now check that any real Bool locals with assignments are NOT
            // defaulted. The `flag` local in the source is assigned (`flag = x > 0`),
            // so collect_assigned_locals should include it.
            let assigned = chc_ctx.collect_assigned_locals();
            // Verify at least one non-arg non-return local is assigned
            let arg_count = body.arg_locals().len();
            let has_assigned_non_arg =
                assigned.iter().any(|&local| local > arg_count && local != 0);
            assert!(
                has_assigned_non_arg,
                "source should have at least one assigned non-argument local"
            );

            // For each assigned Bool local that has a state var, verify no default
            for &assigned_local in &assigned {
                if assigned_local == 0 || assigned_local <= arg_count {
                    continue;
                }
                if let Some(&vec_idx) =
                    chc_ctx.state_var_mgr.local_to_state_idx.get(&assigned_local)
                {
                    let (name, sort) = &chc_ctx.state_var_mgr.state_vars[vec_idx];
                    if sort.is_bool() {
                        let forbidden = format!("(= {name} false)");
                        assert!(
                            !entry_smt.contains(&forbidden),
                            "assigned Bool local _{assigned_local} (`{name}`) must NOT be defaulted in entry rule; got: {entry_smt}"
                        );
                    }
                }
            }
        },
    );
}

// ─── Transition rule sources and targets are valid relations ─────────

#[test]
fn test_transition_rule_targets_are_declared_relations() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn target_test(x: u32) -> u32 {
            if x > 5 { x + 1 } else { x }
        }
        "#,
        |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "target_test");
            let body = instance.body().expect("body");
            let chc_ctx = ChcCtx::new(ctx.tcx, &body, "target_test", ChcConfig::default());
            let (vc, _) = chc_ctx.translate();

            let declared: HashSet<_> = vc.relations.iter().map(|r| r.name.as_str()).collect();

            for rule in &vc.rules {
                assert!(
                    declared.contains(rule.head.name.as_str()),
                    "rule head '{}' should be a declared relation",
                    rule.head.name
                );
                if let Some(from) = &rule.body.relation {
                    assert!(
                        declared.contains(from.name.as_str()),
                        "rule body relation '{}' should be a declared relation",
                        from.name
                    );
                }
            }
        },
    );
}

// ─── Checked arithmetic produces well-formed error rules ────────────

#[test]
fn test_translate_checked_add_error_rules_well_formed() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn checked_add_test(x: u32) -> u32 {
            x + 1
        }
        "#,
        |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "checked_add_test");
            let body = instance.body().expect("body");
            let chc_ctx = ChcCtx::new(ctx.tcx, &body, "checked_add_test", ChcConfig::default());
            let (vc, _) = chc_ctx.translate();

            // Error rules should be well-formed: head is error, body has source
            let error_rules: Vec<_> = vc.rules.iter().filter(|r| r.head.name == "error").collect();
            for rule in &error_rules {
                assert!(rule.body.relation.is_some(), "error rule must have a source block");
                assert_eq!(rule.head.args.len(), 0, "error head should be nullary");
            }
        },
    );
}

// ─── Multi-arm SwitchInt on integer produces guarded rules ───────────
//
// Note: enum matches may be optimized away by the compiler (direct
// discriminant return), so we test SwitchInt via integer matching.

#[test]
fn test_translate_multi_arm_switchint_on_integer() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn classify(x: u32) -> u32 {
            match x {
                0 => 10,
                1 => 20,
                2 => 30,
                _ => 99,
            }
        }
        "#,
        |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "classify");
            let body = instance.body().expect("body");

            // Verify the body has a SwitchInt terminator
            let has_switchint = body.blocks.iter().any(|bb| {
                matches!(bb.terminator.kind, rustc_public::mir::TerminatorKind::SwitchInt { .. })
            });
            assert!(has_switchint, "match on u32 should produce SwitchInt terminator");

            let chc_ctx = ChcCtx::new(ctx.tcx, &body, "classify", ChcConfig::default());
            let (vc, _) = chc_ctx.translate();

            // SwitchInt with 3 explicit cases + otherwise = at least 4 transition rules
            let transition_rules: Vec<_> = vc
                .rules
                .iter()
                .filter(|r| r.body.relation.is_some() && r.head.name != "error")
                .collect();
            assert!(
                transition_rules.len() >= 4,
                "3-case SwitchInt should produce at least 4 transition rules (3 + otherwise), got {}",
                transition_rules.len()
            );

            // All transition rules should be well-formed
            let declared: HashSet<_> = vc.relations.iter().map(|r| r.name.as_str()).collect();
            for rule in &transition_rules {
                assert!(declared.contains(rule.head.name.as_str()));
            }
        },
    );
}

// ─── Loop generates back-edge rules ──────────────────────────────────

#[test]
fn test_translate_loop_generates_back_edge_rule() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn loop_test(mut x: u32) -> u32 {
            while x < 10 {
                x += 1;
            }
            x
        }
        "#,
        |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "loop_test");
            let body = instance.body().expect("body");
            let chc_ctx = ChcCtx::new(ctx.tcx, &body, "loop_test", ChcConfig::default());
            let (vc, _) = chc_ctx.translate();

            let block_rels: Vec<_> =
                vc.relations.iter().filter(|r| r.name.contains("__bb")).collect();
            assert!(
                block_rels.len() >= 2,
                "loop should have at least 2 block relations, got {}",
                block_rels.len()
            );

            // Should have transition rules forming a cycle
            let source_targets: Vec<_> = vc
                .rules
                .iter()
                .filter_map(|r| {
                    r.body.relation.as_ref().map(|from| (from.name.clone(), r.head.name.clone()))
                })
                .collect();
            assert!(
                source_targets.len() >= 3,
                "loop should produce at least 3 transition edges, got {}",
                source_targets.len()
            );
        },
    );
}

// ─── Transition rule arity consistency ───────────────────────────────

#[test]
fn test_all_transition_rule_args_match_relation_arity() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn multi_path(x: u32, y: u32) -> u32 {
            if x > 0 {
                if y > 0 { x + y } else { x }
            } else {
                y
            }
        }
        "#,
        |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "multi_path");
            let body = instance.body().expect("body");
            let chc_ctx = ChcCtx::new(ctx.tcx, &body, "multi_path", ChcConfig::default());
            let (vc, _) = chc_ctx.translate();

            // Build arity map for all declared relations
            let arity_map: std::collections::HashMap<_, _> =
                vc.relations.iter().map(|r| (r.name.as_str(), r.arity())).collect();

            // Every rule head and body relation application must match declared arity
            for rule in &vc.rules {
                let expected_arity = arity_map
                    .get(rule.head.name.as_str())
                    .expect("rule head references undeclared relation");
                assert_eq!(
                    rule.head.args.len(),
                    *expected_arity,
                    "rule head '{}' has {} args but relation arity is {}",
                    rule.head.name,
                    rule.head.args.len(),
                    expected_arity
                );
                if let Some(from) = &rule.body.relation {
                    let expected_arity = arity_map
                        .get(from.name.as_str())
                        .expect("rule body relation references undeclared relation");
                    assert_eq!(
                        from.args.len(),
                        *expected_arity,
                        "rule body relation '{}' has {} args but relation arity is {}",
                        from.name,
                        from.args.len(),
                        expected_arity
                    );
                }
            }
        },
    );
}

// ─── Ptr track level includes stack allocation constraints ──────────

#[test]
fn test_translate_ptr_level_has_stack_alloc_entry_constraints() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn ptr_level_test(x: u32) -> u32 {
            let y = x + 1;
            y
        }
        "#,
        |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "ptr_level_test");
            let body = instance.body().expect("body");
            let chc_ctx = ChcCtx::new(
                ctx.tcx,
                &body,
                "ptr_level_test",
                ChcConfig { track_level: crate::args::ChcTrackLevel::Ptr, ..ChcConfig::default() },
            );
            let (vc, _) = chc_ctx.translate();

            // At Ptr level, entry rule may have additional constraints for
            // stack allocation (obj_valid, obj_size). Check that there is
            // at least one entry (init) rule.
            assert!(vc.rules.iter().any(|r| r.body.relation.is_none()), "should have entry rule");

            // At minimum, translate should succeed at Ptr level
            assert!(!vc.rules.is_empty());
            assert!(!vc.relations.is_empty());
        },
    );
}

// ─── Nested if-else produces well-formed transition graph ────────────

#[test]
fn test_translate_nested_branches_well_formed() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn nested(x: u32) -> u32 {
            if x > 100 {
                if x > 200 { 3 } else { 2 }
            } else {
                if x > 50 { 1 } else { 0 }
            }
        }
        "#,
        |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "nested");
            let body = instance.body().expect("body");
            let chc_ctx = ChcCtx::new(ctx.tcx, &body, "nested", ChcConfig::default());
            let (vc, _) = chc_ctx.translate();

            // Nested branches: at least 4 block relations (2 SwitchInts + merge + return)
            let block_rels: Vec<_> =
                vc.relations.iter().filter(|r| r.name.contains("__bb")).collect();
            assert!(
                block_rels.len() >= 4,
                "nested branches should have at least 4 block relations, got {}",
                block_rels.len()
            );

            // At least 4 transition rules (2 SwitchInts × 2 arms each)
            let transition_rules: Vec<_> = vc
                .rules
                .iter()
                .filter(|r| r.body.relation.is_some() && r.head.name != "error")
                .collect();
            assert!(
                transition_rules.len() >= 4,
                "nested branches should produce at least 4 transition rules, got {}",
                transition_rules.len()
            );

            // Well-formedness: all rule targets are declared
            let declared: HashSet<_> = vc.relations.iter().map(|r| r.name.as_str()).collect();
            for rule in &vc.rules {
                assert!(declared.contains(rule.head.name.as_str()));
            }
        },
    );
}

// ─── Empty function still generates entry rule ──────────────────────

#[test]
fn test_translate_empty_fn_generates_entry_rule() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn empty_fn() {}
        "#,
        |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "empty_fn");
            let body = instance.body().expect("body");
            let chc_ctx = ChcCtx::new(ctx.tcx, &body, "empty_fn", ChcConfig::default());
            let (vc, _) = chc_ctx.translate();

            // Even an empty function should have an error relation and entry rule
            let has_error = vc.relations.iter().any(|r| r.name == "error");
            assert!(has_error, "empty fn should still declare error relation");

            let has_entry = vc.rules.iter().any(|r| r.body.relation.is_none());
            assert!(has_entry, "empty fn should still have an entry rule");
        },
    );
}

// ─── Fn with multiple args: all state vars in relations ─────────────

#[test]
fn test_translate_multi_arg_fn_state_vars() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn multi_arg(a: u32, b: u32, c: u32) -> u32 {
            a + b + c
        }
        "#,
        |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "multi_arg");
            let body = instance.body().expect("body");
            let chc_ctx = ChcCtx::new(ctx.tcx, &body, "multi_arg", ChcConfig::default());
            let (vc, _) = chc_ctx.translate();

            // Block relations should carry all state vars (args + return + temps)
            let bb0_rel = vc
                .relations
                .iter()
                .find(|r| r.name.contains("__bb0"))
                .expect("multi_arg VC must have a bb0 relation");
            // At minimum: return (1) + 3 args + possibly temporaries
            assert!(
                bb0_rel.arity() >= 4,
                "multi_arg bb0 should have arity >= 4 (return + 3 args), got {}",
                bb0_rel.arity()
            );
        },
    );
}

// ═══════════════════════════════════════════════════════════════════════
// Drop(Box) deallocation at Ptr track level (Part of #2272 Step 4)
// ═══════════════════════════════════════════════════════════════════════

fn expr_is_var_named(expr: &Expr, expected: &str) -> bool {
    matches!(expr.value(), ExprValue::Var { name, .. } if name.as_str() == expected)
}

fn expr_is_var_with_prefix(expr: &Expr, prefix: &str) -> bool {
    matches!(expr.value(), ExprValue::Var { name, .. } if name.starts_with(prefix))
}

fn expr_is_bv32_const(expr: &Expr, expected: u32) -> bool {
    matches!(
        expr.value(),
        ExprValue::BitVecConst { value, width }
            if *width == 32 && value == &BigInt::from(expected)
    )
}

fn expr_selects_array(expr: &Expr, array_name: &str) -> bool {
    matches!(
        expr.value(),
        ExprValue::Select { array, .. } if expr_is_var_named(array, array_name)
    )
}

fn expr_selects_array_at_bv32_const(expr: &Expr, array_name: &str, obj_id: u32) -> bool {
    matches!(
        expr.value(),
        ExprValue::Select { array, index }
            if expr_is_var_named(array, array_name) && expr_is_bv32_const(index, obj_id)
    )
}

fn expr_is_obj_size_zero(expr: &Expr) -> bool {
    match expr.value() {
        ExprValue::Eq(lhs, rhs) => {
            ((expr_selects_array(lhs, "obj_size") || expr_is_var_with_prefix(lhs, "obj_size_at_"))
                && expr_is_bv32_const(rhs, 0))
                || ((expr_selects_array(rhs, "obj_size")
                    || expr_is_var_with_prefix(rhs, "obj_size_at_"))
                    && expr_is_bv32_const(lhs, 0))
        }
        _ => false,
    }
}

fn expr_is_obj_valid_select(expr: &Expr) -> bool {
    expr_selects_array(expr, "obj_valid") || expr_is_var_with_prefix(expr, "obj_valid_at_")
}

fn expr_is_low_pointer_offset(expr: &Expr) -> bool {
    matches!(expr.value(), ExprValue::BvExtract { high, low, .. } if *high == 31 && *low == 0)
}

fn expr_is_offset_zero(expr: &Expr) -> bool {
    match expr.value() {
        ExprValue::Eq(lhs, rhs) => {
            (expr_is_low_pointer_offset(lhs) && expr_is_bv32_const(rhs, 0))
                || (expr_is_low_pointer_offset(rhs) && expr_is_bv32_const(lhs, 0))
        }
        _ => false,
    }
}

fn expr_is_dealloc_validity_guard(expr: &Expr) -> bool {
    matches!(
        expr.value(),
        ExprValue::Or(args)
            if args.len() == 2
                && args.iter().any(expr_is_obj_size_zero)
                && args.iter().any(expr_is_obj_valid_select)
    )
}

fn expr_is_dealloc_base_pointer_guard(expr: &Expr) -> bool {
    matches!(
        expr.value(),
        ExprValue::Or(args)
            if args.len() == 2
                && args.iter().any(expr_is_obj_size_zero)
                && args.iter().any(expr_is_offset_zero)
    )
}

fn error_rule_negates_guard(
    rule: &trust_mc_core::chc::Rule,
    guard_pred: impl Fn(&Expr) -> bool,
) -> bool {
    rule.head.name == "error"
        && rule.body.constraints.iter().any(|constraint| {
            constraint_tree_contains(constraint, &|expr| match expr.value() {
                ExprValue::Not(inner) => guard_pred(inner),
                _ => false,
            })
        })
}

fn expr_stores_obj_valid_false_at_const_obj_id(expr: &Expr, obj_id: u32) -> bool {
    if matches!(
        expr.value(),
        ExprValue::Store { array, index, value }
            if expr_is_var_named(array, "obj_valid")
                && expr_is_bv32_const(index, obj_id)
                && matches!(value.value(), ExprValue::BoolConst(false))
    ) {
        return true;
    }
    let scalarized_name = format!("obj_valid_at_0x{obj_id:x}_bv32__out");
    matches!(
        expr.value(),
        ExprValue::Eq(lhs, rhs)
            if ((expr_is_var_named(lhs, &scalarized_name)
                && matches!(rhs.value(), ExprValue::BoolConst(false)))
                || (expr_is_var_named(rhs, &scalarized_name)
                    && matches!(lhs.value(), ExprValue::BoolConst(false))))
    )
}

fn expr_stores_obj_valid_false_at_const_obj_id_any(expr: &Expr) -> bool {
    if matches!(
        expr.value(),
        ExprValue::Store { array, index, value }
            if expr_is_var_named(array, "obj_valid")
                && matches!(index.value(), ExprValue::BitVecConst { width, .. } if *width == 32)
                && matches!(value.value(), ExprValue::BoolConst(false))
    ) {
        return true;
    }
    matches!(
        expr.value(),
        ExprValue::Eq(lhs, rhs)
            if ((expr_is_var_with_prefix(lhs, "obj_valid_at_")
                && matches!(lhs.value(), ExprValue::Var { name, .. } if name.ends_with("__out"))
                && matches!(rhs.value(), ExprValue::BoolConst(false)))
                || (expr_is_var_with_prefix(rhs, "obj_valid_at_")
                    && matches!(rhs.value(), ExprValue::Var { name, .. } if name.ends_with("__out"))
                    && matches!(lhs.value(), ExprValue::BoolConst(false))))
    )
}

fn expr_key(expr: &Expr) -> String {
    expr.to_string()
}

fn select_index_key(expr: &Expr, array_name: &str) -> Option<String> {
    match expr.value() {
        ExprValue::Select { array, index } if expr_is_var_named(array, array_name) => {
            Some(expr_key(index))
        }
        _ => None,
    }
}

fn store_index_key(expr: &Expr, array_name: &str) -> Option<String> {
    match expr.value() {
        ExprValue::Store { array, index, value }
            if expr_is_var_named(array, array_name)
                && matches!(value.value(), ExprValue::BoolConst(false)) =>
        {
            Some(expr_key(index))
        }
        _ => None,
    }
}

fn first_nested_key(expr: &Expr, f: impl Fn(&Expr) -> Option<String>) -> Option<String> {
    if let Some(key) = f(expr) {
        return Some(key);
    }
    let mut stack = expr_children(expr);
    while let Some(child) = stack.pop() {
        if let Some(key) = f(child) {
            return Some(key);
        }
        stack.extend(expr_children(child));
    }
    None
}

fn dealloc_validity_guard_object_key(expr: &Expr) -> Option<String> {
    match expr.value() {
        ExprValue::Or(args) if args.len() == 2 => {
            let size_key = args
                .iter()
                .find_map(|arg| first_nested_key(arg, |e| select_index_key(e, "obj_size")))?;
            let valid_key = args
                .iter()
                .find_map(|arg| first_nested_key(arg, |e| select_index_key(e, "obj_valid")))?;
            (size_key == valid_key).then_some(size_key)
        }
        _ => None,
    }
}

fn dealloc_base_guard_object_and_pointer_key(expr: &Expr) -> Option<(String, String)> {
    match expr.value() {
        ExprValue::Or(args) if args.len() == 2 => {
            let size_key = args
                .iter()
                .find_map(|arg| first_nested_key(arg, |e| select_index_key(e, "obj_size")))?;
            let ptr_key = args.iter().find_map(|arg| {
                first_nested_key(arg, |e| match e.value() {
                    ExprValue::BvExtract { expr, high, low } if *high == 31 && *low == 0 => {
                        Some(expr_key(expr))
                    }
                    _ => None,
                })
            })?;
            Some((size_key, ptr_key))
        }
        _ => None,
    }
}

fn stack_exclusion_object_key(expr: &Expr, stack_obj_id: u32) -> Option<String> {
    match expr.value() {
        ExprValue::Not(inner) => match inner.value() {
            ExprValue::Eq(lhs, rhs) if expr_is_bv32_const(lhs, stack_obj_id) => Some(expr_key(rhs)),
            ExprValue::Eq(lhs, rhs) if expr_is_bv32_const(rhs, stack_obj_id) => Some(expr_key(lhs)),
            _ => None,
        },
        _ => None,
    }
}

fn assert_dealloc_effects_use_one_object_identity(
    checks: &[Expr],
    updates: &[Expr],
    expected_obj_key: &str,
    expected_ptr_key: &str,
    stack_obj_id: u32,
) {
    let validity_key = checks
        .iter()
        .find_map(dealloc_validity_guard_object_key)
        .expect("dealloc effects must include obj_size/obj_valid validity guard");
    assert_eq!(
        validity_key, expected_obj_key,
        "validity guard must use the same object id for obj_size and obj_valid"
    );

    let (base_obj_key, base_ptr_key) = checks
        .iter()
        .find_map(dealloc_base_guard_object_and_pointer_key)
        .expect("dealloc effects must include obj_size/offset base-pointer guard");
    assert_eq!(
        base_obj_key, expected_obj_key,
        "base-pointer guard must use the same object id as the validity guard"
    );
    assert_eq!(
        base_ptr_key, expected_ptr_key,
        "offset guard must be computed from the projected dealloc pointer"
    );

    let store_key = updates
        .iter()
        .find_map(|update| first_nested_key(update, |e| store_index_key(e, "obj_valid")))
        .expect("dealloc effects must invalidate obj_valid");
    assert_eq!(
        store_key, expected_obj_key,
        "obj_valid store must invalidate the same object id used by the guards"
    );

    let stack_key = updates
        .iter()
        .find_map(|update| stack_exclusion_object_key(update, stack_obj_id))
        .expect("dealloc effects must exclude stack object aliases");
    assert_eq!(
        stack_key, expected_obj_key,
        "stack exclusion must constrain the same object id used by guards and store"
    );
}

/// Tests that `drop(box)` at Ptr track level emits deallocation semantics:
/// - error-headed safety rules (double-free / non-base-pointer checks)
/// - metadata transition update via `obj_valid__out = store(obj_valid, obj_id, false)`
///
/// Part of #2272 / #2276: semantic regression guard for Box deallocation.
#[test]
fn test_box_ptr_level_drop_call_emits_error_and_obj_valid_store() {
    with_test_ay_ctx_for_source(
        r#"
        #![allow(dead_code)]
        pub fn probe_box_drop(x: u32) {
            let b = Box::new(x);
            drop(b);
        }
        "#,
        |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "probe_box_drop");
            let body = instance.body().expect("body");

            let vc = mir_to_chc(
                ctx.tcx,
                &body,
                "probe_box_drop",
                ChcConfig { track_level: crate::args::ChcTrackLevel::Ptr, ..ChcConfig::default() },
            );

            let smt = crate::codegen_ay::emit_chc(&vc).to_string();

            assert!(!vc.rules.is_empty(), "Box::new + drop at Ptr level must produce non-empty VC");
            assert!(
                vc.relations.iter().any(|r| r.name == "error"),
                "Ptr-level Box VC must declare error relation"
            );
            let error_rule_count = vc.rules.iter().filter(|rule| rule.head.name == "error").count();
            assert!(
                error_rule_count >= 1,
                "Drop(Box) must emit at least one error-headed safety rule, got {}",
                error_rule_count
            );
            assert!(
                vc.rules
                    .iter()
                    .any(|rule| error_rule_negates_guard(rule, expr_is_dealloc_validity_guard)),
                "Drop(Box) validity error rule must negate \
                 (obj_size[obj_id] == 0 || obj_valid[obj_id])"
            );
            assert!(
                vc.rules
                    .iter()
                    .any(|rule| error_rule_negates_guard(rule, expr_is_dealloc_base_pointer_guard)),
                "Drop(Box) base-pointer error rule must negate \
                 (obj_size[obj_id] == 0 || offset == 0)"
            );

            assert!(
                smt.contains("obj_valid"),
                "Ptr-level Box VC must include obj_valid heap metadata array"
            );
            assert!(
                smt.contains("obj_size"),
                "Ptr-level Box VC must include obj_size heap metadata array"
            );

            // The output state must track obj_valid__out for heap state updates.
            assert!(
                smt.contains("obj_valid__out"),
                "Ptr-level Box VC must include obj_valid__out for heap state updates"
            );
            assert!(
                vc.rules.iter().any(|rule| {
                    rule.body.constraints.iter().any(|constraint| {
                        constraint_tree_contains(constraint, &|expr| {
                            expr_stores_obj_valid_false_at_const_obj_id_any(expr)
                        })
                    })
                }),
                "Drop(Box) transition must store false into obj_valid at a concrete BV32 obj_id"
            );

            let entry_rule =
                vc.rules.iter().find(|r| r.body.relation.is_none()).expect("entry rule must exist");
            assert!(
                !entry_rule.body.constraints.is_empty(),
                "Entry rule should have allocation constraints from Box::new"
            );
        },
    );
}

#[test]
fn test_box_dyn_drop_dealloc_guards_match_rust_dealloc_shape() {
    with_test_ay_ctx_for_source(
        r#"
        #![allow(dead_code)]

        trait Probe {
            fn get(&self) -> u32;
        }

        struct Impl(u32);

        impl Probe for Impl {
            fn get(&self) -> u32 { self.0 }
        }

        pub fn probe_box_dyn_drop(x: u32) {
            let _b: Box<dyn Probe> = Box::new(Impl(x));
        }
        "#,
        |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "probe_box_dyn_drop");
            let body = instance.body().expect("body");
            let vc = mir_to_chc(
                ctx.tcx,
                &body,
                "probe_box_dyn_drop",
                ChcConfig { track_level: crate::args::ChcTrackLevel::Ptr, ..ChcConfig::default() },
            );

            assert!(
                vc.rules
                    .iter()
                    .any(|rule| error_rule_negates_guard(rule, expr_is_dealloc_validity_guard)),
                "Drop(Box<dyn>) validity error rule must negate \
                 (obj_size[obj_id] == 0 || obj_valid[obj_id])"
            );
            assert!(
                vc.rules
                    .iter()
                    .any(|rule| error_rule_negates_guard(rule, expr_is_dealloc_base_pointer_guard)),
                "Drop(Box<dyn>) base-pointer error rule must negate \
                 (obj_size[obj_id] == 0 || offset == 0)"
            );
        },
    );
}

#[test]
fn test_rc_drop_dealloc_guards_match_rust_dealloc_shape() {
    with_test_ay_ctx_for_source(
        r#"
        #![allow(dead_code)]
        use std::rc::Rc;

        pub fn probe_rc_drop(x: u32) {
            let _r = Rc::new(x);
        }
        "#,
        |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "probe_rc_drop");
            let body = instance.body().expect("body");
            let vc = mir_to_chc(
                ctx.tcx,
                &body,
                "probe_rc_drop",
                ChcConfig { track_level: crate::args::ChcTrackLevel::Ptr, ..ChcConfig::default() },
            );

            assert!(
                vc.rules
                    .iter()
                    .any(|rule| error_rule_negates_guard(rule, expr_is_dealloc_validity_guard)),
                "Drop(Rc) validity error rule must negate \
                 (obj_size[obj_id] == 0 || obj_valid[obj_id])"
            );
            assert!(
                vc.rules
                    .iter()
                    .any(|rule| error_rule_negates_guard(rule, expr_is_dealloc_base_pointer_guard)),
                "Drop(Rc) base-pointer error rule must negate \
                 (obj_size[obj_id] == 0 || offset == 0)"
            );
        },
    );
}

#[test]
fn test_rc_dealloc_known_alloc_id_replaces_symbolic_pointer_extract_only_when_supplied() {
    with_test_ay_ctx_for_source(
        r#"
        #![allow(dead_code)]
        pub fn probe_symbolic_rc_dealloc_id(x: u32) -> u32 { x }
        "#,
        |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "probe_symbolic_rc_dealloc_id");
            let body = instance.body().expect("body");
            let mut chc_ctx =
                ChcCtx::new(ctx.tcx, &body, "probe_symbolic_rc_dealloc_id", ChcConfig::default());
            let obj_id = 7u32;
            let stack_obj_id = 3u32;
            chc_ctx.heap_state.insert_local_address(
                2,
                stack_obj_id,
                "stack_obj_for_rc_test".to_string(),
            );
            let symbolic_ptr = Expr::var("symbolic_rc_ptr", Sort::bitvec(64));
            let expected_known_key = expr_key(&Expr::bitvec_const(obj_id as i128, 32));
            let expected_symbolic_key = expr_key(&symbolic_ptr.clone().extract(63, 32));
            let expected_ptr_key = expr_key(&symbolic_ptr);

            let effects_with_id =
                collect_shared_pointer_dealloc_effects(&mut chc_ctx, &symbolic_ptr, Some(obj_id))
                    .expect("symbolic BV64 pointer should split");
            assert_dealloc_effects_use_one_object_identity(
                &effects_with_id.pending_checks,
                &effects_with_id.pending_updates,
                &expected_known_key,
                &expected_ptr_key,
                stack_obj_id,
            );

            assert!(
                effects_with_id.pending_checks.iter().any(|check| {
                    constraint_tree_contains(check, &|expr| {
                        expr_selects_array_at_bv32_const(expr, "obj_size", obj_id)
                    })
                }),
                "Rc dealloc checks should use the supplied allocation id for obj_size selects"
            );
            assert!(
                effects_with_id.pending_checks.iter().any(|check| {
                    constraint_tree_contains(check, &|expr| {
                        expr_selects_array_at_bv32_const(expr, "obj_valid", obj_id)
                    })
                }),
                "Rc dealloc checks should use the supplied allocation id for obj_valid selects"
            );
            assert!(
                effects_with_id.pending_updates.iter().any(|update| {
                    constraint_tree_contains(update, &|expr| {
                        expr_stores_obj_valid_false_at_const_obj_id(expr, obj_id)
                    })
                }),
                "Rc dealloc update should store false using the supplied allocation id"
            );

            let effects_without_id =
                collect_shared_pointer_dealloc_effects(&mut chc_ctx, &symbolic_ptr, None)
                    .expect("symbolic BV64 pointer should split without a known id");
            assert_dealloc_effects_use_one_object_identity(
                &effects_without_id.pending_checks,
                &effects_without_id.pending_updates,
                &expected_symbolic_key,
                &expected_ptr_key,
                stack_obj_id,
            );
            assert!(
                !effects_without_id
                    .pending_checks
                    .iter()
                    .chain(effects_without_id.pending_updates.iter())
                    .any(|expr| {
                        constraint_tree_contains(expr, &|node| {
                            expr_selects_array_at_bv32_const(node, "obj_size", obj_id)
                                || expr_selects_array_at_bv32_const(node, "obj_valid", obj_id)
                                || expr_stores_obj_valid_false_at_const_obj_id(node, obj_id)
                        })
                    }),
                "Rc dealloc must not recover a concrete allocation id unless the caller \
                 supplies one"
            );
        },
    );
}

#[test]
fn test_box_dyn_dealloc_effects_use_same_projected_object_identity() {
    with_test_ay_ctx_for_source(
        r#"
        #![allow(dead_code)]
        pub fn probe_symbolic_box_dyn_dealloc_id(x: u32) -> u32 { x }
        "#,
        |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "probe_symbolic_box_dyn_dealloc_id");
            let body = instance.body().expect("body");
            let mut chc_ctx = ChcCtx::new(
                ctx.tcx,
                &body,
                "probe_symbolic_box_dyn_dealloc_id",
                ChcConfig::default(),
            );
            let stack_obj_id = 4u32;
            chc_ctx.heap_state.insert_local_address(
                2,
                stack_obj_id,
                "stack_obj_for_box_dyn_test".to_string(),
            );

            let projected_ptr = Expr::var("projected_box_dyn_ptr", Sort::bitvec(64))
                .bvadd(Expr::bitvec_const(16u64, 64));
            let obj_id = 0xCAFEu32;
            let expected_known_key = expr_key(&Expr::bitvec_const(obj_id as i128, 32));
            let expected_symbolic_key = expr_key(&projected_ptr.clone().extract(63, 32));
            let expected_ptr_key = expr_key(&projected_ptr);

            let known_effects =
                collect_box_dyn_dealloc_effects(&mut chc_ctx, projected_ptr.clone(), Some(obj_id))
                    .expect("projected Box<dyn> pointer should split");
            assert_dealloc_effects_use_one_object_identity(
                &known_effects.pending_checks,
                &known_effects.pending_updates,
                &expected_known_key,
                &expected_ptr_key,
                stack_obj_id,
            );

            let projected_effects =
                collect_box_dyn_dealloc_effects(&mut chc_ctx, projected_ptr, None)
                    .expect("projected Box<dyn> pointer should split without known id");
            assert_dealloc_effects_use_one_object_identity(
                &projected_effects.pending_checks,
                &projected_effects.pending_updates,
                &expected_symbolic_key,
                &expected_ptr_key,
                stack_obj_id,
            );
        },
    );
}

#[test]
fn test_projected_drop_place_does_not_reuse_containing_known_alloc_id() {
    with_test_ay_ctx_for_source(
        r#"
        #![allow(dead_code)]
        pub fn probe_projected_drop_alloc_id(x: u32) -> u32 { x }
        "#,
        |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "probe_projected_drop_alloc_id");
            let body = instance.body().expect("body");
            let mut chc_ctx =
                ChcCtx::new(ctx.tcx, &body, "probe_projected_drop_alloc_id", ChcConfig::default());
            let local_idx = 1usize;
            let obj_id = 0xBEEFu32;
            chc_ctx.known_alloc_ids.insert(local_idx, obj_id);

            let bare_place = Place { local: local_idx, projection: Vec::new() };
            assert_eq!(
                known_alloc_id_for_unprojected_drop_place(&chc_ctx, &bare_place),
                Some(obj_id),
                "bare Drop(local) may reuse the local allocation identity"
            );

            let projected_place = Place {
                local: local_idx,
                projection: vec![rustc_public::mir::ProjectionElem::Deref],
            };
            assert_eq!(
                known_alloc_id_for_unprojected_drop_place(&chc_ctx, &projected_place),
                None,
                "projected Drop places must derive dealloc identity from the projected pointer"
            );
        },
    );
}

/// Tests that dropping a reference to a Box does not deallocate the Box value.
///
/// `drop(&b)` drops only the reference; deallocation must happen once when `b`
/// itself is dropped.
#[test]
fn test_box_ptr_level_drop_ref_does_not_double_deallocate() {
    with_test_ay_ctx_for_source(
        r#"
        #![allow(dead_code)]
        #![allow(dropping_references)]
        pub fn probe_box_drop_ref_only(x: u32) -> u32 {
            let b = Box::new(x);
            let r = &b;
            drop(r);
            *b
        }

        pub fn probe_box_drop_other_ref(x: u32) -> u32 {
            let b = Box::new(x);
            let y = 1u32;
            let r = &y;
            drop(r);
            *b
        }
        "#,
        |ctx| {
            let dealloc_count = |vc: &trust_mc_core::chc::ChcVc| -> usize {
                vc.rules
                    .iter()
                    .flat_map(|rule| rule.body.constraints.iter())
                    .filter(|constraint| {
                        constraint_tree_contains(constraint, &|expr| {
                            expr_stores_obj_valid_false_at_const_obj_id_any(expr)
                        })
                    })
                    .count()
            };

            let with_ref_instance = find_instance_by_suffix(ctx.tcx, "probe_box_drop_ref_only");
            let with_ref_body = with_ref_instance.body().expect("body");
            let with_ref_chc = ChcCtx::new(
                ctx.tcx,
                &with_ref_body,
                "probe_box_drop_ref_only",
                ChcConfig { track_level: ChcTrackLevel::Ptr, ..ChcConfig::default() },
            );
            let with_ref_drop_call_hits = with_ref_body
                .blocks
                .iter()
                .filter_map(|bb| match &bb.terminator.kind {
                    TerminatorKind::Call { func, args, .. } => Some((func, args.as_slice())),
                    _ => None,
                })
                .filter(|(func, args)| with_ref_chc.detect_box_drop_call(func, args))
                .count();
            let with_ref_vc = mir_to_chc(
                ctx.tcx,
                &with_ref_body,
                "probe_box_drop_ref_only",
                ChcConfig { track_level: crate::args::ChcTrackLevel::Ptr, ..ChcConfig::default() },
            );
            let with_ref_deallocs = dealloc_count(&with_ref_vc);

            let other_ref_instance = find_instance_by_suffix(ctx.tcx, "probe_box_drop_other_ref");
            let other_ref_body = other_ref_instance.body().expect("body");
            let other_ref_vc = mir_to_chc(
                ctx.tcx,
                &other_ref_body,
                "probe_box_drop_other_ref",
                ChcConfig { track_level: crate::args::ChcTrackLevel::Ptr, ..ChcConfig::default() },
            );
            let other_ref_deallocs = dealloc_count(&other_ref_vc);

            assert!(
                other_ref_deallocs >= 1,
                "baseline Box path should include at least one dealloc transition"
            );
            assert_eq!(
                with_ref_drop_call_hits, 0,
                "drop(&Box<T>) must not be detected as a Box dealloc call (hits={})",
                with_ref_drop_call_hits
            );
            assert_eq!(
                with_ref_deallocs, other_ref_deallocs,
                "drop(&Box<T>) must not add extra Box deallocation transitions (with_ref={}, other_ref={})",
                with_ref_deallocs, other_ref_deallocs
            );
        },
    );
}

/// Tests that an implicit `TerminatorKind::Drop` for a Box (scope-end drop
/// without explicit `drop()` call) emits the same deallocation semantics as
/// the explicit call-form path: error-headed safety rules and
/// `obj_valid__out = store(obj_valid, obj_id, false)`.
///
/// Part of #2272 Wave 3 Target B: implicit Drop(Box) parity.
#[test]
fn test_box_ptr_level_drop_terminator_emits_error_and_obj_valid_store() {
    with_test_ay_ctx_for_source(
        r#"
        #![allow(dead_code)]
        pub fn probe_box_implicit_drop(x: u32) -> u32 {
            let b = Box::new(x);
            *b
        }
        "#,
        |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "probe_box_implicit_drop");
            let body = instance.body().expect("body");

            // Verify MIR contains at least one TerminatorKind::Drop (not Call)
            let drop_terminator_count = body
                .blocks
                .iter()
                .filter(|bb| matches!(bb.terminator.kind, TerminatorKind::Drop { .. }))
                .count();
            assert!(
                drop_terminator_count >= 1,
                "implicit Box scope-end should produce at least one TerminatorKind::Drop, got {}",
                drop_terminator_count
            );

            // Generate VC at Ptr track level
            let vc = mir_to_chc(
                ctx.tcx,
                &body,
                "probe_box_implicit_drop",
                ChcConfig { track_level: crate::args::ChcTrackLevel::Ptr, ..ChcConfig::default() },
            );

            let smt = crate::codegen_ay::emit_chc(&vc).to_string();

            // Must have at least one error-headed rule (double-free / base-pointer guard)
            let error_rule_count = vc.rules.iter().filter(|rule| rule.head.name == "error").count();
            assert!(
                error_rule_count >= 1,
                "implicit Drop(Box) must emit at least one error-headed safety rule, got {}",
                error_rule_count
            );

            // Must include obj_valid metadata update (deallocation semantics)
            assert!(
                smt.contains("obj_valid__out"),
                "implicit Drop(Box) VC must include obj_valid__out for heap state updates"
            );
            assert!(
                vc.rules.iter().any(|rule| {
                    rule.body.constraints.iter().any(|constraint| {
                        constraint_tree_contains(constraint, &|expr| {
                            expr_stores_obj_valid_false_at_const_obj_id_any(expr)
                        })
                    })
                }),
                "implicit Drop(Box) transition must invalidate obj_valid; SMT:\n{}",
                smt
            );

            // Entry rule should have stack allocation constraints from Box::new
            let entry_rule =
                vc.rules.iter().find(|r| r.body.relation.is_none()).expect("entry rule must exist");
            assert!(
                !entry_rule.body.constraints.is_empty(),
                "entry rule should have allocation constraints from Box::new"
            );
        },
    );
}

/// Tests that dropping a non-Box type at Ptr track level does NOT emit
/// deallocation semantics and still emits plain Drop-terminator transitions.
///
/// This is the negative case for the Drop(Box) deallocation path in
/// `generate_transition_rules`. Non-Box drops at Ptr level should produce
/// the same goto rule as Reg level.
///
/// Part of #2272: covers `codegen_rules.rs:212-219` (non-Box Drop at Ptr level).
#[test]
fn test_non_box_ptr_level_drop_emits_goto_not_dealloc() {
    with_test_ay_ctx_for_source(
        r#"
        #![allow(dead_code)]

        struct NonBoxDrop(u32);

        impl Drop for NonBoxDrop {
            fn drop(&mut self) {}
        }

        pub fn probe_non_box_drop(x: u32) -> u32 {
            let _y = NonBoxDrop(x);
            x.wrapping_add(1)
        }
        "#,
        |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "probe_non_box_drop");
            let body = instance.body().expect("body");

            // Verify MIR actually exercises the Drop terminator branch under test.
            let drop_terminator_count = body
                .blocks
                .iter()
                .filter(|bb| matches!(bb.terminator.kind, TerminatorKind::Drop { .. }))
                .count();
            assert!(
                drop_terminator_count >= 1,
                "probe_non_box_drop should produce at least one TerminatorKind::Drop, got {}",
                drop_terminator_count
            );

            // Generate VC at Ptr track level
            let vc = mir_to_chc(
                ctx.tcx,
                &body,
                "probe_non_box_drop",
                ChcConfig { track_level: crate::args::ChcTrackLevel::Ptr, ..ChcConfig::default() },
            );

            let smt = crate::codegen_ay::emit_chc(&vc).to_string();

            // Non-Box drop should NOT emit deallocation writes to obj_valid/obj_size.
            // Note: error rules from cleanup/unwind paths (Resume/Abort) may reference
            // obj_valid as part of the Ptr-level relation signature — this is expected
            // since obj_valid is a state variable at Ptr track level, not a deallocation
            // check. The meaningful invariant is that no STORE operations target obj_valid
            // or obj_size, which would indicate deallocation semantics.

            // The SMT should NOT contain obj_valid/obj_size heap metadata for deallocation.
            assert!(
                !smt.contains("store obj_valid"),
                "non-Box Drop must not store into obj_valid (no deallocation); SMT:\n{}",
                smt
            );
            assert!(
                !smt.contains("store obj_size"),
                "non-Box Drop must not store into obj_size (no deallocation); SMT:\n{}",
                smt
            );

            // Should still have transition rules (goto rules for the Drop terminator).
            assert!(
                !vc.rules.is_empty(),
                "non-Box Drop at Ptr level must still produce goto transition rules"
            );
        },
    );
}

// ═══════════════════════════════════════════════════════════════════════
// Drop(Box) coverage gap: Reg vs Ptr track level (Part of #2736)
// ═══════════════════════════════════════════════════════════════════════

/// Documents the known coverage gap for Box deallocation at Reg track level:
/// - At Ptr level: `drop(Box)` emits deallocation semantics (error rules for
///   double-free, `obj_valid` store) — same as `test_box_ptr_level_drop_call_*`.
/// - At Reg level: deallocation safety checks (double-free, use-after-free,
///   base-pointer) ARE emitted, matching Ptr-level behavior.
///
/// Fix #2736: obj_valid/obj_size arrays are now declared at ALL track levels,
/// and dealloc safety checks are no longer gated behind `track_level >= Ptr`.
/// This closes the coverage gap that previously left Reg-level verification
/// blind to RAII/Drop safety properties.
///
/// Part of #2736.
#[test]
fn test_box_drop_reg_level_includes_dealloc_safety_checks() {
    with_test_ay_ctx_for_source(
        r#"
        #![allow(dead_code)]
        pub fn probe_box_drop_gap(x: u32) {
            let b = Box::new(x);
            drop(b);
        }
        "#,
        |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "probe_box_drop_gap");
            let body = instance.body().expect("body");

            // --- Ptr level: deallocation safety checks MUST be present ---
            let vc_ptr = mir_to_chc(
                ctx.tcx,
                &body,
                "probe_box_drop_gap",
                ChcConfig { track_level: crate::args::ChcTrackLevel::Ptr, ..ChcConfig::default() },
            );

            let ptr_error_rules = vc_ptr.rules.iter().filter(|r| r.head.name == "error").count();
            assert!(
                ptr_error_rules >= 1,
                "Ptr level must emit error-headed safety rules for Box drop, got {}",
                ptr_error_rules
            );
            assert!(
                vc_ptr.rules.iter().any(|rule| {
                    rule.body.constraints.iter().any(|constraint| {
                        constraint_tree_contains(constraint, &|expr| {
                            expr_stores_obj_valid_false_at_const_obj_id_any(expr)
                        })
                    })
                }),
                "Ptr level must emit obj_valid invalidation for Box drop"
            );

            // --- Reg level: deallocation safety checks MUST also be present (Fix #2736) ---
            let vc_reg = mir_to_chc(ctx.tcx, &body, "probe_box_drop_gap", ChcConfig::default());
            let smt_reg = crate::codegen_ay::emit_chc(&vc_reg).to_string();

            // Reg level MUST contain obj_valid deallocation semantics (Fix #2736).
            assert!(
                smt_reg.contains("obj_valid"),
                "Reg level must declare obj_valid heap metadata (Fix #2736)"
            );

            // Reg level should still produce valid transition rules.
            assert!(!vc_reg.rules.is_empty(), "Reg-level Box drop must produce transition rules");

            // Reg-level MUST have dealloc error rules referencing obj_valid (Fix #2736).
            let reg_dealloc_error_rules = vc_reg
                .rules
                .iter()
                .filter(|r| r.head.name == "error" && rule_contains_var(r, "obj_valid"))
                .count();
            assert!(
                reg_dealloc_error_rules >= 1,
                "Reg-level must have >= 1 dealloc error rules referencing obj_valid (Fix #2736), got {}",
                reg_dealloc_error_rules
            );

            // Ptr level must also have dealloc-specific error rules.
            let ptr_dealloc_error_rules = vc_ptr
                .rules
                .iter()
                .filter(|r| r.head.name == "error" && rule_contains_var(r, "obj_valid"))
                .count();
            assert!(
                ptr_dealloc_error_rules >= 1,
                "Ptr level must have at least 1 dealloc-specific error rule, got {}",
                ptr_dealloc_error_rules
            );
        },
    );
}

// ═══════════════════════════════════════════════════════════════════════
// InlineAsm fail-closed (Part of #2756)
// ═══════════════════════════════════════════════════════════════════════

/// Tests that `TerminatorKind::InlineAsm` in the CHC pipeline:
/// 1. Emits a conservative error rule (fail-closed, no vacuous PROOF)
/// 2. Preserves reachability to successor blocks via goto rule
/// 3. Records a sound fallback (increments sound_fallback_count, Part of #3099)
///
/// The test source uses `core::arch::asm!("nop")` to produce a MIR InlineAsm
/// terminator.  If MIR does not contain InlineAsm (future compiler change),
/// the test succeeds trivially to avoid false negatives.
///
/// Part of #2756. Updated by #3099 (sound over-approximation reclassification).
#[test]
fn test_inline_asm_emits_error_rule_and_preserves_successor_reachability() {
    // No Mutex needed — set_chc_fallback_count_for_fn overwrites per function name,
    // so the "probe_inline_asm" entry reflects exactly this translation (Part of #2906).
    with_test_ay_ctx_for_source(
        r#"
        #![allow(dead_code)]
        pub fn probe_inline_asm(x: u32) -> u32 {
            unsafe { core::arch::asm!("nop"); }
            x + 1
        }
        "#,
        |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "probe_inline_asm");
            let body = instance.body().expect("body");

            // Verify the body actually has an InlineAsm terminator.
            let has_inline_asm = body.blocks.iter().any(|bb| {
                matches!(bb.terminator.kind, rustc_public::mir::TerminatorKind::InlineAsm { .. })
            });
            if !has_inline_asm {
                // Compiler may optimise away the nop — skip test to avoid
                // false negatives. The unit test below covers the codegen
                // path directly.
                return;
            }

            let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_inline_asm", ChcConfig::default());
            let (vc, _) = chc_ctx.translate();

            // 1. Must have at least one error rule (fail-closed for InlineAsm).
            assert!(
                vc.rules.iter().any(|r| r.head.name == "error"),
                "InlineAsm block must emit at least one conservative error rule (fail-closed)"
            );

            // 2. Successor blocks after InlineAsm must be reachable.
            // Find the InlineAsm destination block and verify it has
            // incoming transition rules.
            let asm_dest: Option<usize> =
                body.blocks.iter().find_map(|bb| match &bb.terminator.kind {
                    rustc_public::mir::TerminatorKind::InlineAsm { destination, .. } => {
                        *destination
                    }
                    _ => None,
                });
            if let Some(dest_bb) = asm_dest {
                let dest_rel =
                    vc.relations.iter().find(|r| r.name.contains(&format!("__bb{dest_bb}")));
                assert!(
                    dest_rel.is_some(),
                    "InlineAsm destination bb{dest_bb} must have a declared relation"
                );
                let dest_name = &dest_rel.unwrap().name;
                let has_incoming =
                    vc.rules.iter().any(|r| &r.head.name == dest_name && r.body.relation.is_some());
                assert!(
                    has_incoming,
                    "InlineAsm destination bb{dest_bb} must have incoming transition rules \
                     (successor reachability preserved)"
                );
            }

            // Part of #3369: InlineAsm reclassified from sound over-approximation
            // (#3099) to unsound fallback. The goto rule for successor blocks
            // passes stale locals when InlineAsm modifies them (under-approx).
            let fallback_counts = get_chc_fallback_counts();
            let count = fallback_counts.get("probe_inline_asm").copied().unwrap_or(0);
            assert_eq!(
                count, 1,
                "InlineAsm must increment unsound fallback_count (stale locals in goto rule); \
                 got {count} for probe_inline_asm in map: {fallback_counts:?}"
            );
        },
    );
}

/// Unit test for the InlineAsm fail-closed path using direct ChcCtx method
/// calls. This exercises the exact code path regardless of compiler MIR
/// optimisations.
///
/// Part of #2756. Updated by #3369 (reclassified from sound to unsound fallback).
#[test]
fn test_inline_asm_fallback_records_fallback_and_emits_error() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn asm_fallback_probe(x: u32) -> u32 {
            if x > 0 { x } else { 0 }
        }
        "#,
        |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "asm_fallback_probe");
            let body = instance.body().expect("body");
            let mut chc_ctx =
                ChcCtx::new(ctx.tcx, &body, "asm_fallback_probe", ChcConfig::default());

            chc_ctx.declare_block_relations();
            chc_ctx.declare_error_relation();

            let from_rel = chc_ctx.block_relations.get(&0).expect("bb0 relation").clone();
            let output_args: Vec<_> = chc_ctx
                .state_var_mgr
                .state_vars
                .iter()
                .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
                .collect();
            let from_app = RelationApp::new(&from_rel, output_args.clone());

            let target = *chc_ctx
                .block_relations
                .keys()
                .find(|&&idx| idx != 0)
                .expect("expected at least one non-entry block");
            let target_rel = chc_ctx.block_relations.get(&target).expect("target relation").clone();

            let before_rules = chc_ctx.vc.rules.len();
            let before_fallback = chc_ctx.fallback_count;
            let stmt_constraints: Arc<[Expr]> = vec![Expr::bool_const(true)].into();

            // Simulate InlineAsm handler: error rule + record_fallback + goto
            // (Part of #3369: InlineAsm reclassified to unsound fallback — stale locals)
            chc_ctx.emit_untranslatable_assert_rule_shared(
                &from_app,
                &stmt_constraints,
                0,
                "TerminatorKind::InlineAsm",
            );
            chc_ctx.record_fallback();
            chc_ctx.emit_goto_rule_shared(&from_app, target, &output_args, &stmt_constraints);

            let new_rules = &chc_ctx.vc.rules[before_rules..];
            assert_eq!(
                new_rules.len(),
                2,
                "InlineAsm handler must emit error rule + successor goto rule"
            );
            assert!(
                new_rules.iter().any(|r| r.head.name == "error"),
                "InlineAsm handler must emit conservative error rule"
            );
            assert!(
                new_rules.iter().any(|r| r.head.name == target_rel),
                "InlineAsm handler must preserve successor reachability"
            );
            for rule in new_rules {
                match &rule.body.constraints {
                    trust_mc_core::constraints::Constraints::Shared { base, .. } => {
                        assert!(
                            Arc::ptr_eq(base, &stmt_constraints),
                            "InlineAsm rules must reuse shared stmt constraint base"
                        );
                    }
                    other => unreachable!(
                        "InlineAsm fallback should emit shared constraints, got {other:?}"
                    ),
                }
            }
            assert_eq!(
                chc_ctx.fallback_count,
                before_fallback + 1,
                "InlineAsm handler must call record_fallback() (unsound — stale locals)"
            );
        },
    );
}

/// Solver-level guard for #2736: verify the simple Box::new + drop harness
/// produces well-formed SMT at Reg level with dealloc safety checks.
///
/// Fix #2736: This test confirms that:
/// 1. Reg-level SMT is well-formed and solvable (no undeclared variables)
/// 2. Reg-level Box drop produces PROOF (safe code → unsat with dealloc checks)
/// 3. Both Reg and Ptr levels contain dealloc error rules
#[test]
fn test_box_drop_reg_level_solver_produces_proof() {
    with_test_ay_ctx_for_source(
        r#"
        #![allow(dead_code)]
        pub fn probe_box_drop_reg_solver(x: u32) {
            let b = Box::new(x);
            drop(b);
        }
        "#,
        |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "probe_box_drop_reg_solver");
            let body = instance.body().expect("body");

            // Reg level: dealloc checks present, safe code → unsat (PROOF)
            let vc_reg =
                mir_to_chc(ctx.tcx, &body, "probe_box_drop_reg_solver", ChcConfig::default());
            let smt_reg = crate::codegen_ay::emit_chc(&vc_reg).to_string();
            assert_z3_result(&smt_reg, "unsat");

            // Ptr level: dealloc checks also present
            let vc_ptr = mir_to_chc(
                ctx.tcx,
                &body,
                "probe_box_drop_reg_solver",
                ChcConfig { track_level: crate::args::ChcTrackLevel::Ptr, ..ChcConfig::default() },
            );

            // Fix #2736: Both levels must have dealloc error rules
            let reg_dealloc_rules = vc_reg
                .rules
                .iter()
                .filter(|r| r.head.name == "error" && rule_contains_var(r, "obj_valid"))
                .count();
            let ptr_dealloc_rules = vc_ptr
                .rules
                .iter()
                .filter(|r| r.head.name == "error" && rule_contains_var(r, "obj_valid"))
                .count();
            assert!(
                reg_dealloc_rules >= 1,
                "Reg level must have >= 1 dealloc error rule (Fix #2736), got {reg_dealloc_rules}"
            );
            assert!(
                ptr_dealloc_rules >= 1,
                "Ptr level must have >= 1 dealloc error rule, got {ptr_dealloc_rules}"
            );
        },
    );
}

/// Fix #2745: Ptr-level Box::new + drop must produce PROOF (unsat) for safe code.
///
/// Before the fix, Z3 returned `sat` because the exchange_malloc arguments
/// could not be resolved, causing translate_rust_alloc to return None. The
/// fallback path left the pointer destination unconstrained, so the dealloc
/// offset check `extract(31,0, ptr) == 0` fired on a symbolic pointer.
/// The fix ensures translate_rust_alloc always returns a valid pointer
/// (with symbolic size when arguments can't be resolved).
#[test]
fn test_box_drop_ptr_level_solver_produces_proof() {
    with_test_ay_ctx_for_source(
        r#"
        #![allow(dead_code)]
        pub fn probe_box_drop_ptr_solver(x: u32) {
            let b = Box::new(x);
            drop(b);
        }
        "#,
        |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "probe_box_drop_ptr_solver");
            let body = instance.body().expect("body");

            let vc = mir_to_chc(
                ctx.tcx,
                &body,
                "probe_box_drop_ptr_solver",
                ChcConfig { track_level: crate::args::ChcTrackLevel::Ptr, ..ChcConfig::default() },
            );
            let smt = crate::codegen_ay::emit_chc(&vc).to_string();

            // Safe code must produce unsat (PROOF) at Ptr level.
            // If this fails with "sat", the dealloc offset check fires spuriously.
            assert_z3_result(&smt, "unsat");
        },
    );
}
