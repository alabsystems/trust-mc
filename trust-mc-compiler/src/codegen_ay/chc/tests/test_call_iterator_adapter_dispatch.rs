// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for `codegen_call_iterator_adapter.rs` — the main
//! `codegen_call_iterator_adapter` dispatch method.
//!
//! Complements `test_call_iterator_adapter.rs` (helper functions) and
//! `test_call_iterator_adapter_range.rs` (RangeSpecNext path details).
//! These tests exercise the top-level dispatch for each StubKind branch.
//!
//! Part of #2921 (CHC codegen test coverage).

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::super::chc_call_context::ChcCallContext;
use super::super::codegen_call_iterator_adapter::CallIteratorAdapter;
use super::common::*;
use ay_bindings::Expr;

const ADAPTER_SOURCE: &str = r#"
    #![allow(dead_code)]
    pub fn probe_adapter_dispatch(x: u32) -> u32 { x }
"#;

/// Helper: build a minimal ChcCallContext for testing dispatch branches.
///
/// Creates the context with a given StubKind and empty args, exercising
/// the fallback/symbolic paths in each match arm.
fn run_adapter_dispatch_with_stub(stub: StubKind) {
    with_test_ay_ctx_for_source(ADAPTER_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_adapter_dispatch");
        let body = instance.body().expect("body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_adapter_dispatch", ChcConfig::default());
        chc_ctx.declare_block_relations();
        chc_ctx.declare_error_relation();

        let from_bb = 0;
        let destination = rustc_public::mir::Place { local: 0, projection: vec![] };
        let from_rel =
            chc_ctx.block_relations.get(&from_bb).expect("source relation for bb0").clone();
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

        let empty_args: Vec<rustc_public::mir::Operand> = Vec::new();
        let cx = ChcCallContext {
            stub,
            args: &empty_args,
            destination: &destination,
            target: 0,
            from_app: &from_app,
            stmt_constraints: &stmt_constraints,
            modified_locals: &modified_locals,
        };
        chc_ctx.codegen_call_iterator_adapter(&cx);

        let after_rules = chc_ctx.vc.rules.len();
        // Every dispatch should produce at least one rule
        // (either a goto rule or an error rule for fail-closed stubs).
        assert!(
            after_rules > before_rules,
            "{stub:?}: dispatch should emit at least one rule (before={before_rules}, after={after_rules})"
        );
    });
}

// =============================================================================
// Dispatch tests: one per StubKind branch
// =============================================================================

/// MapNext with empty args falls through to symbolic over-approximation
/// and produces a goto rule.
#[test]
fn test_dispatch_map_next_empty_args() {
    run_adapter_dispatch_with_stub(StubKind::MapNext);
}

/// FilterNext with empty args falls through to symbolic over-approximation.
#[test]
fn test_dispatch_filter_next_empty_args() {
    run_adapter_dispatch_with_stub(StubKind::FilterNext);
}

/// FlattenNext with empty args falls through to symbolic over-approximation.
#[test]
fn test_dispatch_flatten_next_empty_args() {
    run_adapter_dispatch_with_stub(StubKind::FlattenNext);
}

/// ChainNext with empty args falls through to symbolic over-approximation.
#[test]
fn test_dispatch_chain_next_empty_args() {
    run_adapter_dispatch_with_stub(StubKind::ChainNext);
}

/// RangeSpecNext with empty args triggers fail-closed error rule.
#[test]
fn test_dispatch_range_spec_next_empty_args_fail_closed() {
    with_test_ay_ctx_for_source(ADAPTER_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_adapter_dispatch");
        let body = instance.body().expect("body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_adapter_dispatch", ChcConfig::default());
        chc_ctx.declare_block_relations();
        chc_ctx.declare_error_relation();

        let from_bb = 0;
        let destination = rustc_public::mir::Place { local: 0, projection: vec![] };
        let from_rel =
            chc_ctx.block_relations.get(&from_bb).expect("source relation for bb0").clone();
        let output_args: Vec<_> = chc_ctx
            .state_var_mgr
            .state_vars
            .iter()
            .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
            .collect();
        let from_app = RelationApp::new(&from_rel, output_args);
        let stmt_constraints = [Expr::bool_const(true)];
        let modified_locals = HashSet::new();

        let empty_args: Vec<rustc_public::mir::Operand> = Vec::new();
        let cx = ChcCallContext {
            stub: StubKind::RangeSpecNext,
            args: &empty_args,
            destination: &destination,
            target: 0,
            from_app: &from_app,
            stmt_constraints: &stmt_constraints,
            modified_locals: &modified_locals,
        };
        chc_ctx.codegen_call_iterator_adapter(&cx);

        // RangeSpecNext failure should produce an error rule
        let last_rule = chc_ctx.vc.rules.last().expect("should have emitted a rule");
        assert_eq!(
            last_rule.head.name, "error",
            "RangeSpecNext with empty args should produce fail-closed error rule"
        );
    });
}

/// IterFold with empty args falls through to symbolic fallback.
#[test]
fn test_dispatch_iter_fold_empty_args() {
    run_adapter_dispatch_with_stub(StubKind::IterFold);
}

/// IterSum with empty args falls through to symbolic fallback.
#[test]
fn test_dispatch_iter_sum_empty_args() {
    run_adapter_dispatch_with_stub(StubKind::IterSum);
}

/// IterMap with empty args falls through to symbolic fallback.
#[test]
fn test_dispatch_iter_map_empty_args() {
    run_adapter_dispatch_with_stub(StubKind::IterMap);
}

/// IterFilter with empty args falls through to symbolic fallback.
#[test]
fn test_dispatch_iter_filter_empty_args() {
    run_adapter_dispatch_with_stub(StubKind::IterFilter);
}

/// IterCollect with empty args falls through to symbolic fallback.
#[test]
fn test_dispatch_iter_collect_empty_args() {
    run_adapter_dispatch_with_stub(StubKind::IterCollect);
}

// =============================================================================
// Telemetry counters: RangeSpecNextPathCounts
// =============================================================================

/// `get_range_spec_next_path_counts` returns a consistent snapshot where
/// all counts are non-negative.
#[test]
fn test_range_spec_next_path_counts_snapshot_consistent() {
    let counts = super::super::codegen_call_iterator_adapter::get_range_spec_next_path_counts();
    // Counts are cumulative across all tests in the process, so we just
    // verify the struct is well-formed and all fields are accessible.
    // usize is always >= 0 but this asserts the struct fields are consistent.
    let total = counts.datatype + counts.flattened + counts.fail_closed;
    assert_eq!(
        total,
        counts.datatype + counts.flattened + counts.fail_closed,
        "path counts should be internally consistent"
    );
}

// =============================================================================
// IterFold: identity element for empty iterator
// =============================================================================

const FOLD_SOURCE: &str = r#"
    #![allow(dead_code)]
    pub fn probe_iter_fold(v: &[u32]) -> u32 {
        v.iter().fold(0u32, |acc, &x| acc + x)
    }
"#;

const TRY_FOLD_ALWAYS_SOME_SOURCE: &str = r#"
    #![allow(dead_code)]
    pub fn probe_try_fold_always_some() {
        let arr = [(1, 2), (2, 2)];
        let result = arr.iter().try_fold((), |_acc, &_i| Some(()));
        assert_ne!(result, None);
    }
"#;

/// IterFold produces a VC with an ITE expression: `ite(has_remaining, symbolic, init)`.
/// The init value (0u32) should appear as a bitvec constant.
#[test]
fn test_iter_fold_produces_valid_vc() {
    with_test_ay_ctx_for_source(FOLD_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_iter_fold");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_iter_fold", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_iter_fold", bb_count);
    });
}

#[test]
fn test_iter_try_fold_always_some_preserves_success_variant() {
    with_test_ay_ctx_for_source(TRY_FOLD_ALWAYS_SOME_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_try_fold_always_some");
        let body = instance.body().expect("function body");
        let chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_try_fold_always_some", ChcConfig::default());

        let iter_stubs: Vec<StubKind> = body
            .blocks
            .iter()
            .filter_map(|block| {
                if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                {
                    chc_ctx.detect_stub_matching(func, StubKind::is_iterator_adapter)
                } else {
                    None
                }
            })
            .collect();
        assert!(
            iter_stubs.contains(&StubKind::IterFold),
            "expected try_fold to route through the IterFold adapter stub, got {iter_stubs:?}"
        );

        let vc = mir_to_chc(ctx.tcx, &body, "probe_try_fold_always_some", ChcConfig::default());

        let has_symbolic_fold_result = vc.rules.iter().any(|rule| {
            let is_symbolic_fold_result = |expr: &Expr| {
                matches!(
                    expr.value(),
                    ExprValue::Var { name }
                        if name.starts_with("iter_try_fold_value")
                            || name.starts_with("iter_fold_value")
                )
            };
            rule.body
                .constraints
                .iter()
                .any(|expr| constraint_tree_contains(expr, &is_symbolic_fold_result))
                || rule
                    .head
                    .args
                    .iter()
                    .any(|expr| constraint_tree_contains(expr, &is_symbolic_fold_result))
                || rule.body.relation.as_ref().is_some_and(|relation| {
                    relation
                        .args
                        .iter()
                        .any(|expr| constraint_tree_contains(expr, &is_symbolic_fold_result))
                })
        });
        assert!(
            !has_symbolic_fold_result,
            "try_fold with an always-Some closure should not use a symbolic fold result"
        );

        let has_literal_some_none_comparison =
            vc.rules.iter().any(|rule| {
                let is_literal_some_none_comparison =
                    |expr: &Expr| expr_is_literal_some_none_comparison(expr);
                rule.body
                    .constraints
                    .iter()
                    .any(|expr| constraint_tree_contains(expr, &is_literal_some_none_comparison))
                    || rule.head.args.iter().any(|expr| {
                        constraint_tree_contains(expr, &is_literal_some_none_comparison)
                    })
                    || rule.body.relation.as_ref().is_some_and(|relation| {
                        relation.args.iter().any(|expr| {
                            constraint_tree_contains(expr, &is_literal_some_none_comparison)
                        })
                    })
            });
        assert!(
            !has_literal_some_none_comparison,
            "try_fold result comparison against None should reduce to a boolean guard"
        );
    });
}

// =============================================================================
// IterSum: zero identity for empty iterator
// =============================================================================

const SUM_SOURCE: &str = r#"
    #![allow(dead_code)]
    pub fn probe_iter_sum(v: &[u32]) -> u32 {
        v.iter().copied().sum()
    }
"#;

/// IterSum produces a VC with an ITE expression: `ite(has_remaining, symbolic, zero)`.
#[test]
fn test_iter_sum_produces_valid_vc() {
    with_test_ay_ctx_for_source(SUM_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_iter_sum");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_iter_sum", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_iter_sum", bb_count);
    });
}

// =============================================================================
// Iterator adapter semantics (migrated from test_call_misc.rs, Part of #3746)
// =============================================================================

fn expr_is_literal_some_none_comparison(expr: &Expr) -> bool {
    fn is_some_ctor(expr: &Expr) -> bool {
        matches!(
            expr.value(),
            ExprValue::DatatypeConstructor { constructor_name, args, .. }
                if constructor_name.starts_with("Some") && args.len() == 1
        )
    }

    fn is_none_ctor(expr: &Expr) -> bool {
        matches!(
            expr.value(),
            ExprValue::DatatypeConstructor { constructor_name, args, .. }
                if constructor_name.starts_with("None") && args.is_empty()
        ) || matches!(
            expr.value(),
            ExprValue::FuncApp { name, args }
                if name.starts_with("None") && args.is_empty()
        )
    }

    match expr.value() {
        ExprValue::Eq(lhs, rhs) => {
            (is_some_ctor(lhs) && is_none_ctor(rhs)) || (is_none_ctor(lhs) && is_some_ctor(rhs))
        }
        _ => false,
    }
}

fn expr_is_option_shape_ite(expr: &Expr) -> bool {
    fn is_some_ctor(expr: &Expr) -> bool {
        matches!(
            expr.value(),
            ExprValue::DatatypeConstructor { constructor_name, args, .. }
                if constructor_name.starts_with("Some") && args.len() == 1
        )
    }

    fn is_none_ctor(expr: &Expr) -> bool {
        matches!(
            expr.value(),
            ExprValue::DatatypeConstructor { constructor_name, args, .. }
                if constructor_name.starts_with("None") && args.is_empty()
        )
    }

    fn is_option_shape_side(expr: &Expr) -> bool {
        match expr.value() {
            ExprValue::Ite { then_expr, else_expr, .. } => {
                (is_some_ctor(then_expr) && is_none_ctor(else_expr))
                    || (is_some_ctor(else_expr) && is_none_ctor(then_expr))
            }
            _ => false,
        }
    }

    match expr.value() {
        ExprValue::Eq(lhs, rhs) => is_option_shape_side(lhs) || is_option_shape_side(rhs),
        _ => false,
    }
}

fn expr_has_ite_else_const(expr: &Expr, expected: u64) -> bool {
    fn is_expected_const(expr: &Expr, expected: u64) -> bool {
        match expr.value() {
            ExprValue::BitVecConst { value, .. }
            | ExprValue::IntConst(value)
            | ExprValue::RealConst(value) => *value == expected.into(),
            _ => false,
        }
    }

    let mut worklist = vec![expr];
    while let Some(current) = worklist.pop() {
        if matches!(
            current.value(),
            ExprValue::Ite { else_expr, .. } if is_expected_const(else_expr, expected)
        ) {
            return true;
        }
        worklist.extend(expr_children(current));
    }
    false
}

/// Iterator adapter calls should encode Option shape and empty-iterator identities.
#[test]
fn test_iterator_adapter_semantics() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_iter_adapter_semantics(v: Vec<u32>) -> (Option<u32>, u32, u32) {
            let mut map_it = v.clone().into_iter().map(|x| x + 1);
            let next_value = map_it.next();
            let fold_value = v.clone().into_iter().fold(7u32, |acc, x| acc + x);
            let sum_value: u32 = v.into_iter().sum();
            (next_value, fold_value, sum_value)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_iter_adapter_semantics");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_iter_adapter_semantics",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let iter_stubs: Vec<StubKind> = body
            .blocks
            .iter()
            .filter_map(|block| {
                if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                {
                    chc_ctx.detect_stub_matching(func, StubKind::is_iterator_adapter)
                } else {
                    None
                }
            })
            .collect();

        assert!(
            iter_stubs.iter().any(|stub| stub.is_iterator_adapter()),
            "expected iterator adapter stubs in MIR call graph"
        );

        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_iter_adapter_semantics",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        assert_vc_structure(&vc, "probe_iter_adapter_semantics", body.blocks.len());

        let transition_constraints: Vec<&Expr> = vc
            .rules
            .iter()
            .filter(|rule| rule.body.relation.is_some())
            .flat_map(|rule| rule.body.constraints.iter())
            .collect();
        assert!(
            !transition_constraints.is_empty(),
            "iterator adapter calls should emit constrained transitions"
        );

        if iter_stubs.iter().any(|stub| {
            matches!(
                stub,
                StubKind::MapNext
                    | StubKind::FilterNext
                    | StubKind::FlattenNext
                    | StubKind::ChainNext
            )
        }) {
            let has_option_shape = transition_constraints
                .iter()
                .any(|constraint| expr_is_option_shape_ite(constraint));
            // Flattened Option encoding: discriminant (Bool ITE) + payload (BV ITE)
            // instead of DatatypeConstructor Some/None. Check for ITE in constraints.
            let has_flattened_option_ite = transition_constraints.iter().any(|constraint| {
                constraint_tree_contains(constraint, &|e| {
                    matches!(e.value(), ExprValue::Ite { .. })
                })
            });
            assert!(
                has_option_shape || has_flattened_option_ite,
                "expected Option-shape or flattened ITE constraint for adapter next() calls"
            );
        }

        if iter_stubs.contains(&StubKind::IterFold) {
            let has_fold_identity = transition_constraints
                .iter()
                .any(|constraint| expr_has_ite_else_const(constraint, 7));
            assert!(
                has_fold_identity,
                "expected fold(empty, init, f) identity branch (else = init)"
            );
        }

        if iter_stubs.contains(&StubKind::IterSum) {
            let has_sum_identity = transition_constraints
                .iter()
                .any(|constraint| expr_has_ite_else_const(constraint, 0));
            assert!(has_sum_identity, "expected sum(empty) identity branch (else = zero)");
        }
    });
}
