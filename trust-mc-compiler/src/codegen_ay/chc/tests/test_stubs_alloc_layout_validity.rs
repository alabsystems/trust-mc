// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Regression tests for Layout validity and Layout-ABI alloc safety checks.
//!
//! Part of #2554.

#![allow(clippy::unwrap_used)]

use super::common::*;
use ay_bindings::{Expr, ExprValue, Sort};

#[test]
fn test_layout_size_align_validity_helper_emits_nontrivial_formula() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::alloc::Layout;

        pub fn probe_layout_from_size_align_invalid() -> bool {
            Layout::from_size_align(usize::MAX, 3).is_ok()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_layout_from_size_align_invalid");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_layout_from_size_align_invalid",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let validity = chc_ctx
            .layout_size_align_validity_expr(
                Expr::var("size", Sort::bitvec(crate::codegen_ay::types::POINTER_WIDTH)),
                Expr::var("align", Sort::bitvec(crate::codegen_ay::types::POINTER_WIDTH)),
            )
            .expect("layout validity helper should build a boolean expression");

        assert!(validity.sort().is_bool(), "layout validity helper must return bool");
        assert!(
            !matches!(validity.value(), ExprValue::BoolConst(true)),
            "layout validity helper must not collapse to a hardcoded true"
        );

        assert!(
            constraint_tree_contains(&validity, &|e| matches!(e.value(), ExprValue::BvAnd(..))),
            "layout validity should include align power-of-two mask check"
        );
        assert!(
            constraint_tree_contains(&validity, &|e| matches!(e.value(), ExprValue::BvSub(..))),
            "layout validity should include align-1 subtraction"
        );
        assert!(
            constraint_tree_contains(&validity, &|e| matches!(e.value(), ExprValue::BvUGe(..))),
            "layout validity should include round-up overflow guard"
        );
    });
}

#[test]
fn test_mir_alloc_invalid_layout_emits_error_rule() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub unsafe fn probe_invalid_layout_alloc() {
            let layout = unsafe { std::alloc::Layout::from_size_align_unchecked(usize::MAX, 3) };
            let _ptr = unsafe { std::alloc::alloc(layout) };
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_invalid_layout_alloc");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_invalid_layout_alloc",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let error_rules: Vec<_> =
            vc.rules.iter().filter(|rule| rule.head.name == "error").collect();
        assert!(
            !error_rules.is_empty(),
            "invalid layout allocation must emit at least one error-headed rule"
        );

        let has_pow2_guard_violation = error_rules.iter().any(|rule| {
            let has_bvand = rule_contains_expr(rule, |e| matches!(e.value(), ExprValue::BvAnd(..)));
            let has_bvsub = rule_contains_expr(rule, |e| matches!(e.value(), ExprValue::BvSub(..)));
            has_bvand && has_bvsub
        });
        assert!(
            has_pow2_guard_violation,
            "expected invalid alignment to trigger power-of-two guard violation in error rule"
        );
    });
}
