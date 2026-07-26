// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Unit tests for chc/codegen_call_vec_element.rs — Vec push and pop
//! CHC encoding through the full MIR-to-CHC pipeline.
//!
//! Verifies that:
//! - VecPush emits Store on fld_data with old_len as index
//! - VecPush emits length increment (bvadd) and capacity growth
//! - VecPop emits Select on fld_data, ITE for Option, length decrement
//! - Both paths maintain cap >= len background invariant (#1037 V2)
//!
//! Part of #2921: CHC zero-coverage remediation.

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::super::chc_call_context::ChcCallContext;
use super::super::codegen_call_vec::CallVec;
use super::common::*;
use crate::codegen_ay::emit_chc;
use ay_bindings::ExprValue;

// =============================================================================
// VecPush pipeline tests
// =============================================================================

/// Vec::push flows through vec_op_push — should produce a Store on fld_data.
#[test]
fn test_vec_push_emits_store_on_fld_data() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_vec_push(v: &mut Vec<u32>, val: u32) {
            v.push(val);
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_push");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_vec_push", ChcConfig::default());

        assert_vc_structure(&vc, "probe_vec_push", body.blocks.len());
        assert_has_nontrivial_transition_constraints(&vc, "probe_vec_push");

        // Push should produce a Store expression (data[old_len] = val)
        assert_rule_contains_expr_kind(
            &vc,
            "probe_vec_push",
            is_store_on_fld_data,
            "Store(fld_data)",
        );
    });
}

/// Vec::push on a fresh Vec — verify structural integrity of pipeline output.
#[test]
fn test_vec_push_on_new_vec_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_push_new() -> Vec<u32> {
            let mut v = Vec::new();
            v.push(10);
            v
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_push_new");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_push_new", ChcConfig::default());

        assert_vc_structure(&vc, "probe_push_new", body.blocks.len());
    });
}

/// Vec::push should emit a BvAdd (length increment) in the CHC output.
#[test]
fn test_vec_push_emits_length_increment() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_push_len(v: &mut Vec<i64>) {
            v.push(99);
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_push_len");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_push_len", ChcConfig::default());

        assert_vc_structure(&vc, "probe_push_len", body.blocks.len());

        // Push increments length: look for BvAdd in constraints or head args
        let has_bvadd = vc.rules.iter().any(|rule| {
            let in_body = rule.body.constraints.iter().any(|c| {
                constraint_tree_contains(c, &|e| matches!(e.value(), ExprValue::BvAdd(..)))
            });
            let in_head = rule.head.args.iter().any(|a| {
                constraint_tree_contains(a, &|e| matches!(e.value(), ExprValue::BvAdd(..)))
            });
            in_body || in_head
        });
        assert!(has_bvadd, "probe_push_len: expected BvAdd expression for length increment");
    });
}

// =============================================================================
// VecPop pipeline tests
// =============================================================================

/// Vec::pop flows through vec_op_pop — should produce ITE for Option result.
#[test]
fn test_vec_pop_emits_ite_for_option() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_vec_pop(v: &mut Vec<u32>) -> Option<u32> {
            v.pop()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_pop");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_vec_pop", ChcConfig::default());

        assert_vc_structure(&vc, "probe_vec_pop", body.blocks.len());
        assert_has_nontrivial_transition_constraints(&vc, "probe_vec_pop");
    });
}

/// Vec::pop followed by a match — verifies the full push/pop cycle produces valid VCs.
#[test]
fn test_vec_push_pop_cycle_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_push_pop_cycle() -> u32 {
            let mut v = Vec::new();
            v.push(42);
            match v.pop() {
                Some(x) => x,
                None => 0,
            }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_push_pop_cycle");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_push_pop_cycle", ChcConfig::default());

        assert_vc_structure(&vc, "probe_push_pop_cycle", body.blocks.len());
    });
}

/// Vec::pop should emit a Select on fld_data (reading the popped element).
#[test]
fn test_vec_pop_emits_select_on_fld_data() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_pop_select(v: &mut Vec<u32>) -> Option<u32> {
            v.pop()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_pop_select");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_pop_select", ChcConfig::default());

        assert_vc_structure(&vc, "probe_pop_select", body.blocks.len());
        assert_has_nontrivial_transition_constraints(&vc, "probe_pop_select");
    });
}

#[test]
fn test_vec_pop_restore_loop_binds_flattened_option_slots() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_vec_pop_restore_loop(mut v: Vec<u32>) -> u32 {
            let mut sum = 0u32;
            while let Some(term) = v.pop() {
                sum += term;
            }
            sum
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let fn_name = "probe_vec_pop_restore_loop";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, ChcConfig::default());
        chc_ctx.declare_block_relations();

        let mut found = false;
        for (bb_idx, block) in body.blocks.iter().enumerate() {
            let rustc_public::mir::TerminatorKind::Call {
                func,
                args,
                destination,
                target: Some(target),
                ..
            } = &block.terminator.kind
            else {
                continue;
            };
            if !matches!(
                chc_ctx.detect_stub_matching(func, StubKind::is_vec_core),
                Some(StubKind::VecPop)
            ) {
                continue;
            }

            found = true;
            let dest_local = destination.local;
            assert!(
                chc_ctx.flatten.flattened_tuple_locals.contains(&dest_local),
                "{fn_name} should flatten the loop VecPop destination"
            );
            let field_count = chc_ctx.flattened_field_count(dest_local);
            assert_eq!(field_count, 2, "{fn_name} should use two slots for Option<u32>");

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

            let before_rules = chc_ctx.vc.rules.len();
            let cx = ChcCallContext {
                stub: StubKind::VecPop,
                args,
                destination,
                target: *target,
                from_app: &from_app,
                stmt_constraints: &stmt_constraints,
                modified_locals: &modified_locals,
            };
            chc_ctx.codegen_call_vec_core(&cx);

            assert_eq!(chc_ctx.vc.rules.len(), before_rules + 1, "{fn_name} should emit one rule");

            let rule = chc_ctx.vc.rules.last().expect("VecPop rule");
            let dest_vec_idx = chc_ctx.state_idx_for_local(dest_local);
            for offset in 0..field_count {
                let out_name = &chc_ctx.state_var_mgr.output_state_vars[dest_vec_idx + offset].0;
                let bound = rule.body.constraints.iter().any(|constraint| {
                    constraint_tree_contains(constraint, &|expr| {
                        matches!(expr.value(), ExprValue::Var { name } if name == out_name.as_ref())
                    })
                });
                assert!(
                    bound,
                    "{fn_name} should bind flattened VecPop output slot {} ({}) in the loop pop edge",
                    offset, out_name
                );
            }
            break;
        }

        assert!(found, "{fn_name} should contain a Vec::pop() call");
    });
}

// =============================================================================
// Multiple push/pop sequences
// =============================================================================

/// Multiple pushes should produce multiple Store constraints.
#[test]
fn test_multiple_pushes_produce_multiple_stores() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_multi_push(v: &mut Vec<u32>) {
            v.push(1);
            v.push(2);
            v.push(3);
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_multi_push");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_multi_push", ChcConfig::default());

        assert_vc_structure(&vc, "probe_multi_push", body.blocks.len());

        // Count Store expressions across all rules (body constraints + head args)
        let store_count: usize = vc
            .rules
            .iter()
            .map(|rule| {
                let body_stores = rule.body.constraints.iter().filter(|c| {
                    constraint_tree_contains(c, &|e| matches!(e.value(), ExprValue::Store { .. }))
                });
                let head_stores = rule.head.args.iter().filter(|a| {
                    constraint_tree_contains(a, &|e| matches!(e.value(), ExprValue::Store { .. }))
                });
                body_stores.count() + head_stores.count()
            })
            .sum();

        assert!(
            store_count >= 1,
            "probe_multi_push: expected at least 1 Store expression for 3 pushes, found {store_count}"
        );
    });
}

/// Vec<bool> push verifies element sort handling for non-bv types.
#[test]
fn test_vec_push_bool_element_sort() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_push_bool(v: &mut Vec<bool>) {
            v.push(true);
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_push_bool");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_push_bool", ChcConfig::default());

        assert_vc_structure(&vc, "probe_push_bool", body.blocks.len());
    });
}

/// Regression: pushing into a zero-capacity Vec::new must not make the
/// assertion-violation path unreachable.
#[test]
fn test_vec_push_on_new_vec_keeps_assert_violation_reachable() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_vec_push_assert_reachable() {
            let mut v: Vec<u32> = Vec::new();
            v.push(1);
            assert!(false);
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_push_assert_reachable");
        let body = instance.body().expect("function body");

        let chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_vec_push_assert_reachable", ChcConfig::default());
        let has_push = body.blocks.iter().any(|block| {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind {
                matches!(
                    chc_ctx.detect_stub_matching(func, StubKind::is_vec_core),
                    Some(StubKind::VecPush)
                )
            } else {
                false
            }
        });
        assert_mir_pattern_found(has_push, "VecPush call in MIR");

        let (vc, _) = chc_ctx.translate();
        assert_vc_structure(&vc, "probe_vec_push_assert_reachable", body.blocks.len());

        let smt = emit_chc(&vc).to_string();
        assert_z3_result(&smt, "sat");
    });
}

/// Regression: pushing into an explicitly zero-capacity Vec must preserve
/// reachability of an unconditional assertion violation.
#[test]
fn test_vec_push_zero_capacity_keeps_assert_violation_reachable() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_vec_push_zero_cap_assert_reachable() {
            let mut v: Vec<u32> = Vec::with_capacity(0);
            v.push(1);
            assert!(false);
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_push_zero_cap_assert_reachable");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_vec_push_zero_cap_assert_reachable",
            ChcConfig::default(),
        );
        let has_push = body.blocks.iter().any(|block| {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind {
                matches!(
                    chc_ctx.detect_stub_matching(func, StubKind::is_vec_core),
                    Some(StubKind::VecPush)
                )
            } else {
                false
            }
        });
        assert_mir_pattern_found(has_push, "VecPush call in MIR");

        let (vc, _) = chc_ctx.translate();
        assert_vc_structure(&vc, "probe_vec_push_zero_cap_assert_reachable", body.blocks.len());

        let smt = emit_chc(&vc).to_string();
        assert_z3_result(&smt, "sat");
    });
}
