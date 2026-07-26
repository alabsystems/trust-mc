// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for CHC Vec::resize codegen — quantified growth semantics, struct-
//! embedded resize, and post-resize observation localizers.
//!
//! Split from `test_call_vec_ops.rs` per 500 LOC limit.
//! Part of #3950, #4105.

#![allow(clippy::unwrap_used)]

use super::common::*;

// =============================================================================
// Vec::resize — quantified growth semantics
// =============================================================================

/// Vec::resize on growth should relate the fresh backing array to both the
/// preserved prefix and the appended fill value via a quantified constraint.
#[test]
fn test_vec_resize_growth_emits_quantified_array_relation() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_vec_resize_growth(fill: u32) -> Vec<u32> {
            let mut v = vec![1u32, 2u32];
            v.resize(4, fill);
            v
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_resize_growth");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_vec_resize_growth", ChcConfig::default());

        assert_vc_structure(&vc, "probe_vec_resize_growth", body.blocks.len());

        let has_resize_forall = vc.rules.iter().any(|rule| {
            rule_contains_var(rule, "__resize_data")
                && rule_contains_expr(rule, |expr| matches!(expr.value(), ExprValue::Forall { .. }))
        });
        assert!(
            has_resize_forall,
            "Vec::resize growth should emit a quantified relation over __resize_data"
        );
    });
}

/// Struct-embedded Vec::resize should use the same quantified growth relation
/// instead of replacing the entire backing array with an unconstrained value.
#[test]
fn test_struct_embedded_vec_resize_emits_quantified_array_relation() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        struct SeenMarks {
            marks: Vec<bool>,
        }

        pub fn probe_struct_vec_resize(num_vars: usize) -> bool {
            let mut marks = SeenMarks { marks: vec![false, false] };
            marks.marks[0] = true;
            marks.marks.resize(num_vars, false);
            marks.marks[0]
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_struct_vec_resize");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_struct_vec_resize", ChcConfig::default());

        assert_vc_structure(&vc, "probe_struct_vec_resize", body.blocks.len());

        let has_resize_forall = vc.rules.iter().any(|rule| {
            rule_contains_var(rule, "__resize_data")
                && rule_contains_expr(rule, |expr| matches!(expr.value(), ExprValue::Forall { .. }))
        });
        assert!(
            has_resize_forall,
            "Struct-embedded Vec::resize growth should emit a quantified relation over __resize_data"
        );
    });
}

// =============================================================================
// Vec::resize — struct-embedded store-then-resize-then-read localizer (#4105)
// =============================================================================

/// Exact localizer for the `conflict_grow_preserves_marks` shape:
/// struct field store → struct-embedded Vec::resize → post-resize read.
///
/// This test mirrors the failing compiletest harness more closely than the
/// generic quantified-relation check above. It asserts:
/// 1. The VC contains the `__resize_data` quantified relation.
/// 2. The function has zero non-resume_abort translation drops.
/// 3. The function has zero CHC fallback counts.
///
/// If this localizer passes while the compiletest harness stays UNKNOWN,
/// the residual is solver-limited, not a translation gap.
///
/// Part of #4105.
#[test]
fn test_struct_embedded_vec_resize_store_then_read() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        struct SeenMarks {
            marks: Vec<bool>,
        }

        pub fn probe_struct_vec_resize_store_read(num_vars: usize) -> bool {
            let mut seen = SeenMarks { marks: vec![false, false] };
            seen.marks[0] = true;
            seen.marks.resize(num_vars, false);
            seen.marks[0]
        }
    "#;

    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);

    // Drain globals immediately before codegen to minimize parallel pollution window.
    clear_chc_fallback_counts();
    let _ = take_translation_drop_by_fn();
    let _ = crate::codegen_ay::take_place_translation_drop_count();

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let fn_name = "probe_struct_vec_resize_store_read";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());

        assert_vc_structure(&vc, fn_name, body.blocks.len());

        // 1. Quantified __resize_data relation must be present.
        let has_resize_forall = vc.rules.iter().any(|rule| {
            rule_contains_var(rule, "__resize_data")
                && rule_contains_expr(rule, |expr| matches!(expr.value(), ExprValue::Forall { .. }))
        });
        assert!(
            has_resize_forall,
            "{fn_name}: struct-embedded Vec::resize growth should emit a quantified relation over __resize_data"
        );

        // 2. Zero non-resume_abort translation drops.
        assert_no_semantic_translation_drops(fn_name);

        // 3. Zero CHC fallback counts.
        let fallback_counts = get_chc_fallback_counts();
        let fallback_count = fallback_counts.get(fn_name).copied().unwrap_or(0);
        assert_eq!(
            fallback_count, 0,
            "{fn_name}: should keep CHC fallback count at zero for the store-then-resize-then-read path, map={fallback_counts:?}"
        );
    });

    // Clean up globals after the test.
    clear_chc_fallback_counts();
    let _ = take_translation_drop_by_fn();
    let _ = crate::codegen_ay::take_place_translation_drop_count();
}

// =============================================================================
// Vec::resize — post-resize observation localizers (Part of #3950)
// =============================================================================

/// Helper: assert that a function has zero non-resume_abort translation drops.
/// resume_abort drops are expected structural noise from unwind cleanup (Vec
/// has Drop), not semantic observation gaps.
fn assert_no_semantic_translation_drops(fn_name: &str) {
    let translation_drops = take_translation_drop_by_fn();
    let site_reasons = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
    let _ = crate::codegen_ay::take_place_translation_drop_count();
    let fn_reasons = site_reasons.get(fn_name).cloned().unwrap_or_default();
    let resume_abort_count = fn_reasons.get("resume_abort").copied().unwrap_or(0);

    // Only count drops that have a non-resume_abort site_reason tag.
    // Bare (unlabeled) drops from parallel test pollution are excluded by
    // summing tagged reasons rather than using the aggregate counter, which
    // is subject to global-state races in multi-threaded test execution.
    let tagged_total: usize = fn_reasons.values().sum();
    let non_resume_tagged = tagged_total.saturating_sub(resume_abort_count);

    let raw_total = translation_drops.get(fn_name).copied().unwrap_or(0);
    assert_eq!(
        non_resume_tagged, 0,
        "{fn_name} should have zero non-resume_abort tagged translation drops. \
         raw_total={raw_total}, tagged_total={tagged_total}, \
         resume_abort={resume_abort_count}, site_reasons={fn_reasons:?}"
    );
}

/// Localizer: Vec::resize growth + post-resize len observation should not
/// produce semantic translation drops. This isolates the resize encoding
/// path without indexing (which has its own translation drops).
#[test]
fn test_vec_resize_tail_index_no_translation_drop() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_vec_resize_tail_index(fill: i64) -> usize {
            let mut v = vec![1i64, 2];
            let old_len = v.len();
            v.resize(old_len + 1, fill);
            v.len()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_resize_tail_index");
        let body = instance.body().expect("function body");

        // Drain globals immediately before codegen to minimize parallel pollution window.
        clear_chc_fallback_counts();
        let _ = take_translation_drop_by_fn();
        let _ = crate::codegen_ay::take_place_translation_drop_count();

        let vc = mir_to_chc(ctx.tcx, &body, "probe_vec_resize_tail_index", ChcConfig::default());

        assert_vc_structure(&vc, "probe_vec_resize_tail_index", body.blocks.len());
        assert_no_semantic_translation_drops("probe_vec_resize_tail_index");
    });
}

/// Localizer: prefix equality after Vec::resize growth should not produce
/// semantic translation drops. This isolates whether the preserved prefix
/// is visible through range-slice comparison.
#[test]
fn test_vec_resize_prefix_eq_no_translation_drop() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_vec_resize_prefix_eq(fill: i64) -> bool {
            let mut v = vec![1i64, 2];
            let old_len = v.len();
            let initial = v.clone();
            v.resize(old_len + 1, fill);
            v[0..old_len] == initial
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_resize_prefix_eq");
        let body = instance.body().expect("function body");

        // Drain globals immediately before codegen to minimize parallel pollution window.
        clear_chc_fallback_counts();
        let _ = take_translation_drop_by_fn();
        let _ = crate::codegen_ay::take_place_translation_drop_count();

        let vc = mir_to_chc(ctx.tcx, &body, "probe_vec_resize_prefix_eq", ChcConfig::default());

        assert_vc_structure(&vc, "probe_vec_resize_prefix_eq", body.blocks.len());
        assert_no_semantic_translation_drops("probe_vec_resize_prefix_eq");
    });
}

/// Localizer: full-slice equality after Vec::resize shrink should not
/// produce semantic translation drops. This isolates whether post-shrink
/// view metadata propagation is complete.
#[test]
fn test_vec_resize_shrink_eq_no_translation_drop() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_vec_resize_shrink_eq(fill: i64) -> bool {
            let mut v = vec![1i64, 2];
            let old_len = v.len();
            let initial = v.clone();
            v.resize(old_len + 1, fill);
            v.resize(old_len - 1, fill);
            v[..] == initial[..old_len - 1]
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_resize_shrink_eq");
        let body = instance.body().expect("function body");

        // Drain globals immediately before codegen to minimize parallel pollution window.
        clear_chc_fallback_counts();
        let _ = take_translation_drop_by_fn();
        let _ = crate::codegen_ay::take_place_translation_drop_count();

        let vc = mir_to_chc(ctx.tcx, &body, "probe_vec_resize_shrink_eq", ChcConfig::default());

        assert_vc_structure(&vc, "probe_vec_resize_shrink_eq", body.blocks.len());
        assert_no_semantic_translation_drops("probe_vec_resize_shrink_eq");
    });
}
