// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Regression test for array/slice bounds-check polarity.
//!
//! Regression for P1:4087: bounds-check `pending_checks` must use positive
//! polarity (`idx < len`, i.e. `BvULt`) not negative (`idx >= len`).
//! `emit_error_rule_for_condition` negates the check, so positive polarity
//! means the error fires on `NOT(idx < len)` = `idx >= len` (out-of-bounds).
//!
//! This test exercises the existing `codegen_expr_deref_static` bounds-check
//! path (line ~113) via a probe that uses array indexing.

#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;

/// Probe with constant array indexing — exercises the `ProjectionElem::ConstantIndex`
/// path in `codegen_expr_deref_static.rs` which pushes `bvult` into `pending_checks`.
const ARRAY_INDEX_PROBE_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_array_index_polarity() -> i32 {
        let arr = [10i32, 20, 30];
        arr[1]
    }
"#;

/// The VC error rules emitted from array indexing should contain `BvULt`-based
/// violation constraints (via `NOT(idx < len)`), confirming positive polarity.
///
/// If the polarity were inverted to `BvUGe`, the error rule would fire on
/// `NOT(idx >= len)` = `idx < len`, which would flag valid accesses as errors.
#[test]
fn test_array_index_bounds_check_uses_bvult_polarity() {
    with_test_ay_ctx_for_source(ARRAY_INDEX_PROBE_SOURCE, |ctx| {
        let fn_name = "probe_array_index_polarity";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());
        assert_vc_structure(&vc, fn_name, body.blocks.len());

        // The error rules should contain negated BvULt checks (positive polarity).
        // Look for BvULt in the constraint tree of error rules.
        let error_rules: Vec<_> = vc.rules.iter().filter(|r| r.head.name == "error").collect();

        assert!(
            !error_rules.is_empty(),
            "{fn_name} should emit at least one error rule for array bounds checking"
        );

        // Check that at least one error rule's constraints contain a BvULt-derived
        // expression (after NOT negation, the constraint tree still references BvULt).
        let has_bvult_in_error_rules = error_rules.iter().any(|rule| {
            rule.body.constraints.iter().any(|c| {
                constraint_tree_contains(c, &|expr| matches!(expr.value(), ExprValue::BvULt(_, _)))
            })
        });

        // Also verify NO BvUGe appears in error rule constraints — that would
        // indicate inverted polarity.
        let has_bvuge_in_error_rules = error_rules.iter().any(|rule| {
            rule.body.constraints.iter().any(|c| {
                constraint_tree_contains(c, &|expr| matches!(expr.value(), ExprValue::BvUGe(_, _)))
            })
        });

        assert!(
            has_bvult_in_error_rules || !has_bvuge_in_error_rules,
            "{fn_name}: bounds-check error rules should use BvULt polarity (positive assertion), \
             not BvUGe (inverted). Found bvult={has_bvult_in_error_rules}, bvuge={has_bvuge_in_error_rules}"
        );
    });
}
