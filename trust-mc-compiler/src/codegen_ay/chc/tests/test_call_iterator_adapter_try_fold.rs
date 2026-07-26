// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for try_fold-specific iterator adapter semantics.

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used)]

use super::common::*;
use ay_bindings::{Expr, ExprValue};
use trust_mc_core::chc::Rule;

const TRY_FOLD_ALWAYS_SOME_SOURCE: &str = r#"
    #![allow(dead_code)]
    pub fn probe_try_fold_always_some() {
        let arr = [(1, 2), (2, 2)];
        let result = arr.iter().try_fold((), |_acc, &_i| Some(()));
        assert_ne!(result, None);
    }
"#;

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

        assert!(
            !vc.rules.iter().any(rule_contains_symbolic_fold_result),
            "try_fold with an always-Some closure should not use a symbolic fold result"
        );
        assert!(
            !vc.rules.iter().any(rule_contains_literal_some_none_comparison),
            "try_fold result comparison against None should reduce to a boolean guard"
        );
    });
}

fn rule_contains_symbolic_fold_result(rule: &Rule) -> bool {
    rule_contains_expr(rule, |expr| {
        matches!(
            expr.value(),
            ExprValue::Var { name }
                if name.starts_with("iter_try_fold_value") || name.starts_with("iter_fold_value")
        )
    })
}

fn rule_contains_literal_some_none_comparison(rule: &Rule) -> bool {
    rule_contains_expr(rule, expr_is_literal_some_none_comparison)
}

fn rule_contains_expr(rule: &Rule, pred: impl Fn(&Expr) -> bool) -> bool {
    rule.body.constraints.iter().any(|expr| constraint_tree_contains(expr, &pred))
        || rule.head.args.iter().any(|expr| constraint_tree_contains(expr, &pred))
        || rule.body.relation.as_ref().is_some_and(|relation| {
            relation.args.iter().any(|expr| constraint_tree_contains(expr, &pred))
        })
}

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
