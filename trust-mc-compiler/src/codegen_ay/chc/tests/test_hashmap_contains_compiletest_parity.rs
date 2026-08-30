// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Exact-file compiletest-parity localizer for `tests/ay/hashmap_contains.rs`.
//!
//! Part of #4109, #4099, #1739, #134.
//!
//! This module loads the real committed harness file verbatim, strips Kani-only
//! syntax, and translates each harness through the same CHC envelope used by
//! the driver (FunctionInlinePass + Mem track + Auto step mode + instance-aware
//! `mir_to_chc_with_instance`).
//!
//! The goal is to classify whether the shared `chc_translation_drop=1` /
//! `sound_fallback_count=1` residual appears:
//! 1. Before any map mutation (zero-mutation control reproduces),
//! 2. Only on the stateful path (stateful harness reproduces, control clean), or
//! 3. Only in the compiletest/driver envelope (both stay clean here).

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;

/// The real committed harness file, loaded verbatim.
const HASHMAP_CONTAINS_REAL_FILE: &str =
    include_str!("../../../../../tests/ay/hashmap_contains.rs");

/// Strip `#[kani::proof]`, `#[kani::unwind(...)]`, `// kani-expect:`,
/// `// kani-flags:`, `//!` doc comments, and conflicting crate-level
/// `#![...]` attrs. Inject a local kani stub module so the real harness
/// source compiles under the CHC unit test harness without the full Kani
/// sysroot.
fn strip_kani_for_unit_ctx(source: &str) -> String {
    let mut result = String::with_capacity(source.len() + 512);
    result.push_str("#![allow(dead_code, unused_assignments, unused_variables, unused_imports)]\n");
    result.push_str("#![feature(register_tool)]\n");
    result.push_str("#![register_tool(kanitool)]\n\n");
    result.push_str("mod kani {\n");
    result.push_str("    #[kanitool::fn_marker = \"AnyModel\"]\n");
    result.push_str("    pub fn any<T>() -> T { panic!(\"model-only\") }\n\n");
    result.push_str("    #[kanitool::fn_marker = \"AssumeHook\"]\n");
    result.push_str("    pub fn assume(_cond: bool) {}\n");
    result.push_str("}\n\n");
    for line in source.lines() {
        let trimmed = line.trim();
        if trimmed.starts_with("#[kani::") {
            continue;
        }
        if trimmed.starts_with("// kani-expect:") || trimmed.starts_with("// kani-flags:") {
            continue;
        }
        if trimmed.starts_with("//!") {
            continue;
        }
        // Skip existing crate-level attributes that conflict with our injected ones.
        if trimmed.starts_with("#![") {
            continue;
        }
        result.push_str(line);
        result.push('\n');
    }
    result
}

/// Harness names from the real file.
const ZERO_MUTATION_CONTROL: &str = "verify_not_contains_without_insert";
const STATEFUL_HARNESS: &str = "verify_contains_after_insert";

/// Diagnostic results from a compiletest-parity translation run.
struct ParityResult {
    vc: trust_mc_core::chc::ChcVc,
    fallback_counts: std::collections::BTreeMap<String, usize>,
    translation_drops: std::collections::BTreeMap<String, usize>,
    translation_sites:
        std::collections::BTreeMap<String, std::collections::BTreeMap<String, usize>>,
    drop_fallback_reasons:
        std::collections::BTreeMap<String, std::collections::BTreeMap<String, usize>>,
    unhandled_calls: std::collections::BTreeMap<String, usize>,
}

fn reset_parity_counters() {
    clear_chc_fallback_counts();
    let _ = take_translation_drop_by_fn();
    let _ = crate::codegen_ay::take_drop_fallback_reasons_by_fn();
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
    let _ = crate::codegen_ay::take_place_translation_drop_count();
    let _ = crate::codegen_ay::take_constant_translation_drop_count();
    let _ = crate::codegen_ay::take_unsupported_field_projection_count();
    let _ = crate::codegen_ay::take_unhandled_call_by_fn();
}

fn run_compiletest_parity_harness<'tcx>(
    ctx: &mut crate::codegen_ay::context::AYCtx<'tcx, 'static>,
    fn_name: &str,
) -> ParityResult {
    reset_parity_counters();
    ctx.config.use_chc = true;
    ctx.config.function_inlining = true;
    ctx.config.chc_track_level = crate::args::ChcTrackLevel::Mem;
    ctx.config.chc_step_mode = crate::args::ChcStepMode::Auto;
    ctx.queries.set_args(crate::args::Arguments::default());

    let instance = find_instance_by_suffix(ctx.tcx, fn_name);
    let body = ctx.body_or_instance_body(instance).expect("function body");
    let inline_cfg = crate::kani_middle::transform::inline::InlineConfig {
        max_depth: ctx.config.inline_depth,
        enabled: ctx.config.function_inlining,
        preserve_block_on: true,
    };
    let mut inline_pass =
        crate::kani_middle::transform::inline::FunctionInlinePass::new(inline_cfg);
    let (_, body) =
        inline_pass.transform_with_body_provider(ctx.tcx, body, instance, |callee_instance| {
            if !callee_instance.has_body() {
                return None;
            }
            let callee_name = callee_instance.name();
            if crate::kani_middle::reachability::is_prefix_abstracted(&callee_name) {
                return None;
            }
            if callee_name.ends_with("::any_where") || callee_name.contains("::any_where::") {
                return None;
            }
            ctx.body_or_instance_body(callee_instance)
        });

    let vc = crate::codegen_ay::chc::mir_to_chc_with_instance(
        ctx.tcx,
        &body,
        instance,
        fn_name,
        ChcConfig {
            frame_narrowing: crate::codegen_ay::chc::frame_narrowing_enabled(),
            frame_narrowing_flattened: crate::codegen_ay::chc::frame_narrowing_flattened_enabled(),
            nan_checks: ctx.config.nan_checks,
            track_level: ctx.config.chc_track_level,
            step_mode: ctx.config.chc_step_mode,
            int_lift: ctx.config.chc_int_lift,
            chc_debug: crate::codegen_ay::chc::ChcDebugMode::from(ctx.queries.args().ay_chc_debug),
            wide_mem: crate::codegen_ay::chc::WideMemMode::from(ctx.config.ay_wide_mem),
            extra_pointer_checks: ctx.config.extra_pointer_checks,
            prove_safety_only: ctx.config.prove_safety_only,
            memory_safety_checks: ctx.config.memory_safety_checks,
            overflow_checks: ctx.config.overflow_checks,
            undefined_function_checks: ctx.config.undefined_function_checks,
            recursive_unwind_depth: if ctx.config.has_explicit_unwind {
                ctx.config.unwind_depth
            } else {
                0
            },
            unwinding_assertions: ctx.config.unwinding_assertions,
            uninit_checks: ctx.config.uninit_checks,
            contract_static_havoc: false,
        },
    );

    ParityResult {
        vc,
        fallback_counts: get_chc_fallback_counts(),
        translation_drops: take_translation_drop_by_fn(),
        translation_sites: crate::codegen_ay::take_translation_drop_site_reasons_by_fn(),
        drop_fallback_reasons: crate::codegen_ay::take_drop_fallback_reasons_by_fn(),
        unhandled_calls: crate::codegen_ay::take_unhandled_call_by_fn(),
    }
}

/// D1+D2: Zero-mutation control — `verify_not_contains_without_insert`.
///
/// This harness never calls insert, remove, or clear. If it reproduces the
/// same translation-drop / sound-fallback residual as the compiletest report,
/// the shared root cause is upstream of map mutation (HashMap::new or
/// contains_key resolution, assert wrapper, or driver envelope).
#[test]
fn test_hashmap_contains_parity_zero_mutation_control() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    reset_parity_counters();

    let stripped = strip_kani_for_unit_ctx(HASHMAP_CONTAINS_REAL_FILE);
    with_test_ay_ctx_for_source(&stripped, |mut ctx| {
        let result = run_compiletest_parity_harness(&mut ctx, ZERO_MUTATION_CONTROL);

        // Structural: the VC should produce non-empty relations and rules.
        assert!(
            !result.vc.relations.is_empty(),
            "{ZERO_MUTATION_CONTROL} should produce relations"
        );
        assert!(!result.vc.rules.is_empty(), "{ZERO_MUTATION_CONTROL} should produce rules");

        // Classification diagnostics — record for issue triage.
        let fallback = result.fallback_counts.get(ZERO_MUTATION_CONTROL).copied().unwrap_or(0);
        let translation_drop =
            result.translation_drops.get(ZERO_MUTATION_CONTROL).copied().unwrap_or(0);
        let fn_sites = result.translation_sites.get(ZERO_MUTATION_CONTROL);
        let non_benign_sites: usize = fn_sites
            .map(|sites| {
                sites
                    .iter()
                    .filter(|(reason, _)| *reason != "state_idx_missing_collections_dest")
                    .map(|(_, count)| count)
                    .sum()
            })
            .unwrap_or(0);
        let drop_fallback = result.drop_fallback_reasons.get(ZERO_MUTATION_CONTROL);
        let unhandled = result.unhandled_calls.get(ZERO_MUTATION_CONTROL).copied().unwrap_or(0);

        eprintln!(
            "[#4109 parity] {ZERO_MUTATION_CONTROL}: fallback={fallback}, \
             translation_drop={translation_drop}, non_benign_sites={non_benign_sites}, \
             drop_fallback_reasons={drop_fallback:?}, unhandled={unhandled}, \
             translation_sites={fn_sites:?}"
        );

        // The zero-mutation control is the classification gate:
        // - If it already shows translation_drop > 0 or fallback > 0, the
        //   shared root cause is upstream of map mutation.
        // - If it stays clean, the shared root cause is in the stateful path.
        // We record the classification but do not assert clean — the current
        // HEAD may still exhibit the residual, and this test's purpose is to
        // CLASSIFY, not to gate.
    });

    reset_parity_counters();
}

/// D3: Stateful harness — `verify_contains_after_insert`.
///
/// This is the closest real-file sibling of the existing synthetic probe in
/// test_call_collections.rs. If the zero-mutation control stays clean but
/// this harness reproduces, the root cause is in the HashMap mutation pipeline.
#[test]
fn test_hashmap_contains_parity_stateful_harness() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    reset_parity_counters();

    let stripped = strip_kani_for_unit_ctx(HASHMAP_CONTAINS_REAL_FILE);
    with_test_ay_ctx_for_source(&stripped, |mut ctx| {
        let result = run_compiletest_parity_harness(&mut ctx, STATEFUL_HARNESS);

        assert!(!result.vc.relations.is_empty(), "{STATEFUL_HARNESS} should produce relations");
        assert!(!result.vc.rules.is_empty(), "{STATEFUL_HARNESS} should produce rules");

        let fallback = result.fallback_counts.get(STATEFUL_HARNESS).copied().unwrap_or(0);
        let translation_drop = result.translation_drops.get(STATEFUL_HARNESS).copied().unwrap_or(0);
        let fn_sites = result.translation_sites.get(STATEFUL_HARNESS);
        let non_benign_sites: usize = fn_sites
            .map(|sites| {
                sites
                    .iter()
                    .filter(|(reason, _)| *reason != "state_idx_missing_collections_dest")
                    .map(|(_, count)| count)
                    .sum()
            })
            .unwrap_or(0);
        let drop_fallback = result.drop_fallback_reasons.get(STATEFUL_HARNESS);
        let unhandled = result.unhandled_calls.get(STATEFUL_HARNESS).copied().unwrap_or(0);

        eprintln!(
            "[#4109 parity] {STATEFUL_HARNESS}: fallback={fallback}, \
             translation_drop={translation_drop}, non_benign_sites={non_benign_sites}, \
             drop_fallback_reasons={drop_fallback:?}, unhandled={unhandled}, \
             translation_sites={fn_sites:?}"
        );
    });

    reset_parity_counters();
}
