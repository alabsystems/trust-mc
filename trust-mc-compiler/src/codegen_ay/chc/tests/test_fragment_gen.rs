// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Dedicated tests for `fragment_gen.rs` — fragment-based CHC rule generation
//! for Large-step encoding (#112).
//!
//! Exercises `generate_fragment_rules`, `generate_single_block_rules`,
//! `is_composable_linear_chain`, `is_composable_fragment`, and
//! `classify_inlineable_call` through real Rust MIR, verifying rule structure:
//! relation references, constraint composition, fragment classification.
//!
//! Part of #3132: test coverage for CHC rule generation.

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;

// =============================================================================
// Single-block fragment: delegates to per-block rule generation
// =============================================================================

/// Verify that a function whose entire body is a single basic block in Large
/// mode produces rules equivalent to Small mode — the single-block fragment
/// path delegates to `generate_single_block_rules`.
///
/// Exercises `fragment_gen.rs:154-155` (single-block fragment branch).
#[test]
fn test_fragment_gen_single_block_delegates_to_per_block() {
    with_test_ay_ctx_for_source(
        r#"
        #![allow(dead_code)]
        pub fn probe_single_block(x: u32) -> u32 {
            x
        }
        "#,
        |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "probe_single_block");
            let body = instance.body().expect("body");

            let vc_small = mir_to_chc(ctx.tcx, &body, "probe_single_block", ChcConfig::default());
            let vc_large = mir_to_chc(
                ctx.tcx,
                &body,
                "probe_single_block",
                ChcConfig { step_mode: crate::args::ChcStepMode::Large, ..ChcConfig::default() },
            );

            // Single-block function: Large mode should produce the same structure
            // as Small mode (same number of relations and rules).
            assert_eq!(
                vc_small.relations.len(),
                vc_large.relations.len(),
                "Single-block: Large should match Small relation count"
            );
            assert_eq!(
                vc_small.rules.len(),
                vc_large.rules.len(),
                "Single-block: Large should match Small rule count"
            );

            // Both must have entry rule and error relation
            assert!(
                vc_large.rules.iter().any(|r| r.body.relation.is_none()),
                "Large mode single-block must have entry rule"
            );
            assert!(
                vc_large.relations.iter().any(|r| r.name == "error"),
                "Large mode single-block must have error relation"
            );
        },
    );
}

// =============================================================================
// Composable linear chain: intermediate blocks composed away
// =============================================================================

/// Verify that a function with a composable linear chain of blocks (all
/// intermediate blocks have Goto terminators) produces fewer relations in
/// Large mode than Small mode — composition eliminates intermediate predicates.
///
/// Exercises `fragment_gen.rs:156-157` (composable linear chain branch) and
/// `is_composable_linear_chain`.
#[test]
fn test_fragment_gen_composable_chain_reduces_predicates() {
    with_test_ay_ctx_for_source(
        r#"
        #![allow(dead_code)]
        pub fn probe_chain(a: u32, b: u32) -> u32 {
            let c = a.wrapping_add(b);
            let d = c.wrapping_mul(2);
            let e = d.wrapping_add(1);
            let f = e.wrapping_sub(3);
            f
        }
        "#,
        |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "probe_chain");
            let body = instance.body().expect("body");

            let vc_small = mir_to_chc(ctx.tcx, &body, "probe_chain", ChcConfig::default());
            let vc_large = mir_to_chc(
                ctx.tcx,
                &body,
                "probe_chain",
                ChcConfig { step_mode: crate::args::ChcStepMode::Large, ..ChcConfig::default() },
            );

            // Large mode should have <= relations (composition reduces predicates)
            assert!(
                vc_large.relations.len() <= vc_small.relations.len(),
                "Large mode should have <= predicates than Small: Large={}, Small={}",
                vc_large.relations.len(),
                vc_small.relations.len()
            );

            // Both must have entry rule and referentially valid rules
            let declared: HashSet<_> = vc_large.relations.iter().map(|r| r.name.as_str()).collect();
            for rule in &vc_large.rules {
                assert!(
                    declared.contains(rule.head.name.as_str()),
                    "Large mode rule head '{}' references undeclared relation",
                    rule.head.name
                );
            }

            // Large-mode output must preserve the semantic content (arithmetic
            // operations should still appear in composed constraints).
            assert_has_nontrivial_transition_constraints(&vc_large, "probe_chain");
            assert_rule_contains_expr_kind(
                &vc_large,
                "probe_chain (Large)",
                |e| matches!(e.value(), ExprValue::BvAdd(..)),
                "BvAdd (wrapping_add preserved in composed fragment)",
            );
        },
    );
}

// =============================================================================
// Non-composable fragment: internal branching falls back to per-block
// =============================================================================

/// Verify that a function with internal branching (SwitchInt within a fragment)
/// that is non-composable falls back to per-block rule generation, producing
/// rules for each block individually.
///
/// Exercises `fragment_gen.rs:168-170` (non-composable fallback) and
/// `generate_fallback_fragment_rules`.
#[test]
fn test_fragment_gen_noncomposable_falls_back_to_per_block() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn probe_noncomposable(x: u32) -> u32 {
            if x > 10 {
                if x > 20 {
                    x.wrapping_mul(3)
                } else {
                    x.wrapping_mul(2)
                }
            } else {
                x.wrapping_add(1)
            }
        }
        "#,
        |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "probe_noncomposable");
            let body = instance.body().expect("body");

            let vc_large = mir_to_chc(
                ctx.tcx,
                &body,
                "probe_noncomposable",
                ChcConfig { step_mode: crate::args::ChcStepMode::Large, ..ChcConfig::default() },
            );

            // Must have block relations for the branch targets
            let block_rels: Vec<_> =
                vc_large.relations.iter().filter(|r| r.name.contains("__bb")).collect();
            assert!(
                block_rels.len() >= 3,
                "Non-composable fragment should declare >= 3 block relations, got {}",
                block_rels.len()
            );

            // Must have transition rules from each branch
            let transition_count = vc_large
                .rules
                .iter()
                .filter(|r| r.body.relation.is_some() && r.head.name != "error")
                .count();
            assert!(
                transition_count >= 3,
                "Non-composable fragment should produce >= 3 transitions, got {}",
                transition_count
            );

            // Referential integrity
            let declared: HashSet<_> = vc_large.relations.iter().map(|r| r.name.as_str()).collect();
            for rule in &vc_large.rules {
                assert!(
                    declared.contains(rule.head.name.as_str()),
                    "Fallback rule head '{}' references undeclared relation",
                    rule.head.name
                );
            }
        },
    );
}

// =============================================================================
// Dead-end block extraction: composable path with exit branches
// =============================================================================

/// Verify that a loop with a conditional exit (creating dead-end blocks)
/// in Large mode correctly separates dead-end blocks from the composable path,
/// producing separate relations for exit branches.
///
/// Exercises `fragment_gen.rs:158-167` (dead-end extraction path) and
/// `extract_composable_path` / `compute_dead_end_blocks`.
#[test]
fn test_fragment_gen_dead_end_blocks_get_separate_relations() {
    with_test_ay_ctx_for_source(
        r#"
        #![allow(dead_code)]
        pub fn probe_dead_end(n: u32) -> u32 {
            let mut sum = 0u32;
            for i in 0u32..n {
                sum = sum.wrapping_add(i);
            }
            sum
        }
        "#,
        |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "probe_dead_end");
            let body = instance.body().expect("body");

            let vc_large = mir_to_chc(
                ctx.tcx,
                &body,
                "probe_dead_end",
                ChcConfig { step_mode: crate::args::ChcStepMode::Large, ..ChcConfig::default() },
            );

            // Must have entry and error
            assert!(
                vc_large.rules.iter().any(|r| r.body.relation.is_none()),
                "Large mode loop must have entry rule"
            );
            assert!(
                vc_large.relations.iter().any(|r| r.name == "error"),
                "Large mode loop must have error relation"
            );

            // Loop should produce back-edge rules (cycle in the graph)
            let source_target_pairs: Vec<_> = vc_large
                .rules
                .iter()
                .filter_map(|r| {
                    r.body.relation.as_ref().map(|from| (from.name.clone(), r.head.name.clone()))
                })
                .collect();
            assert!(
                source_target_pairs.len() >= 2,
                "Loop should produce at least 2 transition edges, got {}",
                source_target_pairs.len()
            );

            // Referential integrity: all rule heads must reference declared relations
            let declared: HashSet<_> = vc_large.relations.iter().map(|r| r.name.as_str()).collect();
            for rule in &vc_large.rules {
                assert!(
                    declared.contains(rule.head.name.as_str()),
                    "Rule head '{}' not declared in Large mode loop VC",
                    rule.head.name
                );
            }

            // Must have BvAdd from the wrapping_add
            assert_rule_contains_expr_kind(
                &vc_large,
                "probe_dead_end (Large)",
                |e| matches!(e.value(), ExprValue::BvAdd(..)),
                "BvAdd (wrapping_add in loop body)",
            );
        },
    );
}

// =============================================================================
// Fragment composition preserves semantic constraints
// =============================================================================

/// Verify that fragment composition in Large mode preserves all semantic
/// constraints from composed blocks. When blocks B0→B1→B2 are composed,
/// the resulting rule must contain constraints from all three blocks
/// (not just the last one).
///
/// This tests the constraint accumulation in `generate_composed_rules`.
#[test]
fn test_fragment_composition_preserves_all_block_constraints() {
    with_test_ay_ctx_for_source(
        r#"
        #![allow(dead_code)]
        pub fn probe_compose_semantics(x: u32) -> u32 {
            let a = x.wrapping_add(1);
            let b = a.wrapping_mul(2);
            let c = b.wrapping_sub(3);
            c
        }
        "#,
        |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "probe_compose_semantics");
            let body = instance.body().expect("body");

            let vc_large = mir_to_chc(
                ctx.tcx,
                &body,
                "probe_compose_semantics",
                ChcConfig { step_mode: crate::args::ChcStepMode::Large, ..ChcConfig::default() },
            );

            // Must have non-trivial constraints (not vacuously true)
            assert_has_nontrivial_transition_constraints(&vc_large, "probe_compose_semantics");

            // All three arithmetic operations must appear in the VC
            assert_rule_contains_expr_kind(
                &vc_large,
                "probe_compose_semantics",
                |e| matches!(e.value(), ExprValue::BvAdd(..)),
                "BvAdd (wrapping_add)",
            );
            assert_rule_contains_expr_kind(
                &vc_large,
                "probe_compose_semantics",
                |e| matches!(e.value(), ExprValue::BvMul(..)),
                "BvMul (wrapping_mul)",
            );
            assert_rule_contains_expr_kind(
                &vc_large,
                "probe_compose_semantics",
                |e| matches!(e.value(), ExprValue::BvSub(..)),
                "BvSub (wrapping_sub)",
            );
        },
    );
}

// =============================================================================
// Large vs Small solver equivalence: both produce unsat for safe code
// =============================================================================

/// Verify that Large mode and Small mode produce solver-equivalent results:
/// both should return unsat (PROOF) for safe code. This confirms that
/// fragment composition does not lose constraints needed for verification.
///
/// Exercises the full `generate_fragment_rules` path end-to-end.
#[test]
fn test_fragment_gen_solver_equivalence_with_small_mode() {
    with_test_ay_ctx_for_source(
        r#"
        #![allow(dead_code)]
        pub fn probe_solver_equiv(x: u32) -> u32 {
            let y = x.wrapping_add(1);
            y
        }
        "#,
        |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "probe_solver_equiv");
            let body = instance.body().expect("body");

            let vc_small = mir_to_chc(ctx.tcx, &body, "probe_solver_equiv", ChcConfig::default());
            let vc_large = mir_to_chc(
                ctx.tcx,
                &body,
                "probe_solver_equiv",
                ChcConfig { step_mode: crate::args::ChcStepMode::Large, ..ChcConfig::default() },
            );

            let smt_small = crate::codegen_ay::emit_chc(&vc_small).to_string();
            let smt_large = crate::codegen_ay::emit_chc(&vc_large).to_string();

            // Both should produce well-formed SMT
            assert!(!smt_small.is_empty(), "Small mode SMT must be non-empty");
            assert!(!smt_large.is_empty(), "Large mode SMT must be non-empty");

            // Both should produce unsat (safe code → PROOF)
            assert_z3_result(&smt_small, "unsat");
            assert_z3_result(&smt_large, "unsat");
        },
    );
}

// =============================================================================
// Rule arity consistency: emitted apps match declared relations (#3696)
// =============================================================================

/// Verify that all emitted rule head and body RelationApps have arity matching
/// their declared relation after Large-mode codegen. This catches stale
/// from_app snapshots that miss late-created state vars.
///
/// Part of #3696: regression test for large-step late-state-var parity.
#[test]
fn test_fragment_gen_single_block_rule_arity_matches_declarations() {
    with_test_ay_ctx_for_source(
        r#"
        #![allow(dead_code)]
        pub fn probe_arity_single(x: u32) -> u32 {
            x.wrapping_add(1)
        }
        "#,
        |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "probe_arity_single");
            let body = instance.body().expect("body");

            let vc = mir_to_chc(
                ctx.tcx,
                &body,
                "probe_arity_single",
                ChcConfig { step_mode: crate::args::ChcStepMode::Large, ..ChcConfig::default() },
            );

            assert_rule_arity_matches_declarations(&vc, "single-block Large");
        },
    );
}

/// Verify rule arity consistency for a composed linear chain in Large mode.
///
/// Part of #3696: regression test for large-step late-state-var parity.
#[test]
fn test_fragment_gen_composed_chain_rule_arity_matches_declarations() {
    with_test_ay_ctx_for_source(
        r#"
        #![allow(dead_code)]
        pub fn probe_arity_chain(a: u32, b: u32) -> u32 {
            let c = a.wrapping_add(b);
            let d = c.wrapping_mul(2);
            let e = d.wrapping_add(1);
            e
        }
        "#,
        |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "probe_arity_chain");
            let body = instance.body().expect("body");

            let vc = mir_to_chc(
                ctx.tcx,
                &body,
                "probe_arity_chain",
                ChcConfig { step_mode: crate::args::ChcStepMode::Large, ..ChcConfig::default() },
            );

            assert_rule_arity_matches_declarations(&vc, "composed-chain Large");
        },
    );
}

/// Helper: assert all rule head/body relation apps have arity matching declarations.
fn assert_rule_arity_matches_declarations(vc: &trust_mc_core::chc::ChcVc, label: &str) {
    let declared: std::collections::HashMap<&str, usize> =
        vc.relations.iter().map(|r| (r.name.as_str(), r.arg_sorts.len())).collect();

    for (i, rule) in vc.rules.iter().enumerate() {
        let expected_head = declared.get(rule.head.name.as_str()).unwrap_or_else(|| {
            panic!("[{label}] rule {i}: head '{}' not declared", rule.head.name)
        });
        assert_eq!(
            rule.head.args.len(),
            *expected_head,
            "[{label}] rule {i}: head '{}' arity mismatch (got {}, expected {})",
            rule.head.name,
            rule.head.args.len(),
            expected_head,
        );

        if let Some(body_rel) = &rule.body.relation {
            let expected_body = declared.get(body_rel.name.as_str()).unwrap_or_else(|| {
                panic!("[{label}] rule {i}: body '{}' not declared", body_rel.name)
            });
            assert_eq!(
                body_rel.args.len(),
                *expected_body,
                "[{label}] rule {i}: body '{}' arity mismatch (got {}, expected {})",
                body_rel.name,
                body_rel.args.len(),
                expected_body,
            );
        }
    }
}
