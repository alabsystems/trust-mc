// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Full-harness diagnostics for the `copy_nonoverlapping` swap residual.
//!
//! Part of #3798: the generic `swap<T>` callee already translates without
//! demoted fallback. This file classifies the remaining caller-body residual
//! so follow-up production work can target the right layer.

use super::common::*;

const SWAP_CALLER_BODY_SOURCE: &str = r#"
    #![allow(dead_code, deprecated)]

    fn swap<T>(x: &mut T, y: &mut T) {
        unsafe {
            let mut t: T = std::mem::uninitialized();
            std::ptr::copy_nonoverlapping(x, &mut t, 1);
            std::ptr::copy_nonoverlapping(y, x, 1);
            std::ptr::copy_nonoverlapping(&t, y, 1);
            std::mem::forget(t);
        }
    }

    pub fn probe_copy_swap() -> (i32, i32) {
        let mut x = 12;
        let mut y = 13;
        swap(&mut x, &mut y);
        (x, y)
    }
"#;

const SWAP_FULL_HARNESS_SOURCE: &str = r#"
    #![allow(dead_code, deprecated)]

    fn swap<T>(x: &mut T, y: &mut T) {
        unsafe {
            let mut t: T = std::mem::uninitialized();
            std::ptr::copy_nonoverlapping(x, &mut t, 1);
            std::ptr::copy_nonoverlapping(y, x, 1);
            std::ptr::copy_nonoverlapping(&t, y, 1);
            std::mem::forget(t);
        }
    }

    pub fn test_swap() {
        let mut x = 12;
        let mut y = 13;
        swap(&mut x, &mut y);
        assert!(x == 13);
        assert!(y == 12);
    }
"#;

fn reset_swap_harness_metadata() {
    clear_chc_fallback_counts();
    let _ = crate::codegen_ay::take_type_sort_fallback_by_fn();
    let _ = crate::codegen_ay::take_unhandled_call_by_fn();
    let _ = take_translation_drop_by_fn();
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
}

#[test]
fn test_mir_copy_swap_caller_body_has_clean_translation_diagnostics() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    reset_swap_harness_metadata();

    let fn_name = "probe_copy_swap";
    with_test_ay_ctx_for_source(SWAP_CALLER_BODY_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, ChcConfig::default());
        let (vc, _, diagnostics) = chc_ctx.translate_with_diagnostics();

        assert_vc_structure(&vc, fn_name, body.blocks.len());
        assert_eq!(
            diagnostics.fallback_count.get(),
            0,
            "{fn_name} should not use demoted copy-core fallback"
        );
        assert_eq!(
            diagnostics.type_sort_fallback.get(),
            0,
            "{fn_name} should not use type/layout fallback"
        );
        assert_eq!(
            diagnostics.unhandled_call.get(),
            0,
            "{fn_name} should not fall through call dispatch"
        );
        assert!(
            diagnostics.sound_fallback_detail.is_empty(),
            "{fn_name} should not record sound fallback detail in the caller-body shape, got {:?}",
            diagnostics.sound_fallback_detail
        );
    });

    let fallback_counts = get_chc_fallback_counts();
    let type_sort_fallbacks = crate::codegen_ay::take_type_sort_fallback_by_fn();
    let unhandled_calls = crate::codegen_ay::take_unhandled_call_by_fn();
    let translation_drops = take_translation_drop_by_fn();
    let translation_drop_sites = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();

    assert_eq!(
        fallback_counts.get(fn_name).copied().unwrap_or(0),
        0,
        "{fn_name} should not record demoted CHC fallback; fallback_map={fallback_counts:?}"
    );
    assert_eq!(
        type_sort_fallbacks.get(fn_name).copied().unwrap_or(0),
        0,
        "{fn_name} should not record type-sort fallback; type_sort_fallbacks={type_sort_fallbacks:?}"
    );
    assert_eq!(
        unhandled_calls.get(fn_name).copied().unwrap_or(0),
        0,
        "{fn_name} should not increment unhandled-call counters; unhandled_calls={unhandled_calls:?}"
    );
    let translation_drop_count = translation_drops.get(fn_name).copied().unwrap_or(0);
    let site_counts = translation_drop_sites.get(fn_name).cloned().unwrap_or_default();
    assert_eq!(
        translation_drop_count, 0,
        "{fn_name} should not record translation-drop fallback in the caller-body shape; translation_drops={translation_drops:?}"
    );
    assert!(
        site_counts.is_empty(),
        "{fn_name} should not report translation-drop site reasons in the caller-body shape; sites={translation_drop_sites:?}"
    );
}

#[test]
fn test_mir_copy_swap_full_harness_has_clean_translation_diagnostics() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    reset_swap_harness_metadata();

    let fn_name = "test_swap";
    with_test_ay_ctx_for_source(SWAP_FULL_HARNESS_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, ChcConfig::default());
        let (vc, _, diagnostics) = chc_ctx.translate_with_diagnostics();

        assert_vc_structure(&vc, fn_name, body.blocks.len());
        assert_eq!(
            diagnostics.fallback_count.get(),
            0,
            "{fn_name} should not use demoted copy-core fallback"
        );
        assert_eq!(
            diagnostics.type_sort_fallback.get(),
            0,
            "{fn_name} should not use type/layout fallback"
        );
        assert_eq!(
            diagnostics.unhandled_call.get(),
            0,
            "{fn_name} should not fall through call dispatch"
        );
        assert!(
            diagnostics.sound_fallback_detail.is_empty(),
            "{fn_name} should not record sound fallback detail, got {:?}",
            diagnostics.sound_fallback_detail
        );
    });

    let fallback_counts = get_chc_fallback_counts();
    let type_sort_fallbacks = crate::codegen_ay::take_type_sort_fallback_by_fn();
    let unhandled_calls = crate::codegen_ay::take_unhandled_call_by_fn();
    let translation_drops = take_translation_drop_by_fn();
    let translation_drop_sites = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();

    assert_eq!(
        fallback_counts.get(fn_name).copied().unwrap_or(0),
        0,
        "{fn_name} should not record demoted CHC fallback; fallback_map={fallback_counts:?}"
    );
    assert_eq!(
        type_sort_fallbacks.get(fn_name).copied().unwrap_or(0),
        0,
        "{fn_name} should not record type-sort fallback; type_sort_fallbacks={type_sort_fallbacks:?}"
    );
    assert_eq!(
        unhandled_calls.get(fn_name).copied().unwrap_or(0),
        0,
        "{fn_name} should not increment unhandled-call counters; unhandled_calls={unhandled_calls:?}"
    );
    let translation_drop_count = translation_drops.get(fn_name).copied().unwrap_or(0);
    let site_counts = translation_drop_sites.get(fn_name).cloned().unwrap_or_default();
    assert_eq!(
        translation_drop_count, 0,
        "{fn_name} should not record translation-drop fallback; translation_drops={translation_drops:?}"
    );
    assert!(
        site_counts.is_empty(),
        "{fn_name} should not report translation-drop site reasons; sites={translation_drop_sites:?}"
    );
}

/// Diagnostic: verify the swap pattern produces a compact VC (few rules)
/// and that the constraints correctly model x←y, y←x semantics.
/// Part of #3932: investigate Genuine CTREX in copy_nonoverlapping_swap.
#[test]
fn test_swap_vc_rule_count_and_constraint_content() {
    let fn_name = "test_swap";
    with_test_ay_ctx_for_source(SWAP_FULL_HARNESS_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");

        // Dump MIR block count and callee paths for pattern matching diagnosis.
        let bb_count = body.blocks.len();
        eprintln!("[#3932 diag] {fn_name}: MIR has {bb_count} basic blocks");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, ChcConfig::default());
        let (vc, _, _diagnostics) = chc_ctx.translate_with_diagnostics();

        let rule_count = vc.rules.len();
        let relation_count = vc.relations.len();
        eprintln!("[#3932 diag] {fn_name}: VC has {rule_count} rules, {relation_count} relations");

        // If the swap pattern fires, we expect a compact VC:
        // - Relations: ~bb_count + 1 (error) — no expansion from inlining
        // - Rules: ~bb_count + entry (one rule per block transition)
        // If the inline walker fires instead, we'd see many more rules
        // from walking the swap body's 5+ blocks.
        //
        // Compact VC = swap pattern fired. Expanded VC = inline walker.
        assert!(
            rule_count <= bb_count + 5,
            "[#3932] VC has {rule_count} rules for {bb_count} BBs — \
             swap pattern likely NOT firing, inline walker expanding callee body"
        );

        // Dump all rule bodies for manual inspection
        for (i, rule) in vc.rules.iter().enumerate() {
            let head_name = &rule.head.name;
            let constraint_count = rule.body.constraints.len();
            eprintln!("[#3932 diag] rule[{i}]: head={head_name}, constraints={constraint_count}");
        }

        // Solve the VC and verify it gives UNSAT (PROOF).
        // If the unit test VC gives SAT, the constraint generation is wrong.
        // If UNSAT, the issue is only in the full pipeline.
        let smt = crate::codegen_ay::emit_chc(&vc).to_string();
        eprintln!("[#3932 diag] SMT2 length: {} bytes", smt.len());
        assert_z3_result(&smt, "unsat");
    });
}
