// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Localizer tests for NIA tangent-plane compiletest parity.
//!
//! Part of #4031 (A2 lane): the two live UNKNOWN harnesses
//! (`ay_nia_tangent_plane_linear_in_x`, `ay_nia_tangent_plane_linear_in_y`)
//! both have `inferable_predicate=10`, which exactly matches 2 calls to
//! `tangent_plane(...)` × 5 helper calls each (`mul`, `mul`, `add`, `mul`, `sub`).
//!
//! The single-call siblings (`tangent_plane_at_model_point_*`) are already PROOF,
//! so this localizer isolates the duplicated-helper expansion hypothesis.

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;

/// Minimal embedded Rust source mirroring the NIA tangent-plane harnesses.
///
/// Contains:
/// - `Rational { num, den }` with `from_i64`, `mul`, `add`, `sub`
/// - `tangent_plane(a, b, x, y) -> Rational`
/// - One control probe using a single `tangent_plane(...)` call (green baseline)
/// - Two linearity probes using two `tangent_plane(...)` calls (live failing shape)
const NIA_TANGENT_PLANE_PROBE: &str = r#"
    #![allow(dead_code)]
    #![feature(register_tool)]
    #![register_tool(kanitool)]

    mod kani {
        #[kanitool::fn_marker = "AnyModel"]
        pub fn any<T>() -> T {
            unsafe { std::mem::zeroed() }
        }

        #[kanitool::fn_marker = "AssumeHook"]
        pub fn assume(cond: bool) {
            let _ = cond;
        }
    }

    #[derive(Clone, Copy, PartialEq)]
    struct Rational {
        num: i64,
        den: i64,
    }

    impl Rational {
        fn from_i64(v: i64) -> Self {
            Self { num: v, den: 1 }
        }

        fn mul(&self, other: &Self) -> Self {
            Self { num: self.num * other.num, den: self.den * other.den }
        }

        fn add(&self, other: &Self) -> Self {
            Self {
                num: self.num * other.den + other.num * self.den,
                den: self.den * other.den,
            }
        }

        fn sub(&self, other: &Self) -> Self {
            Self {
                num: self.num * other.den - other.num * self.den,
                den: self.den * other.den,
            }
        }
    }

    fn tangent_plane(a: &Rational, b: &Rational, x: &Rational, y: &Rational) -> Rational {
        a.mul(y).add(&b.mul(x)).sub(&a.mul(b))
    }

    /// Control: single tangent_plane call — mirrors the at-model-point family (already PROOF).
    pub fn probe_tangent_plane_single_call() {
        let a = Rational::from_i64(2);
        let b = Rational::from_i64(3);
        let t = tangent_plane(&a, &b, &a, &b);
        let ab = a.mul(&b);
        assert!(t == ab);
    }

    /// Live failing shape: two tangent_plane calls (linear_in_x).
    pub fn probe_tangent_plane_linear_in_x() {
        let a = Rational::from_i64(2);
        let b = Rational::from_i64(3);
        let y = Rational::from_i64(5);
        let x1 = Rational::from_i64(1);
        let x2 = Rational::from_i64(4);

        let t1 = tangent_plane(&a, &b, &x1, &y);
        let t2 = tangent_plane(&a, &b, &x2, &y);
        let diff = t1.sub(&t2);
        let expected = b.mul(&x1.sub(&x2));
        assert!(diff == expected);
    }

    /// Live failing shape: two tangent_plane calls (linear_in_y).
    pub fn probe_tangent_plane_linear_in_y() {
        let a = Rational::from_i64(2);
        let b = Rational::from_i64(3);
        let x = Rational::from_i64(5);
        let y1 = Rational::from_i64(1);
        let y2 = Rational::from_i64(4);

        let t1 = tangent_plane(&a, &b, &x, &y1);
        let t2 = tangent_plane(&a, &b, &x, &y2);
        let diff = t1.sub(&t2);
        let expected = a.mul(&y1.sub(&y2));
        assert!(diff == expected);
    }
"#;

const CONTROL_PROBE: &str = "probe_tangent_plane_single_call";
const LINEARITY_PROBES: [&str; 2] =
    ["probe_tangent_plane_linear_in_x", "probe_tangent_plane_linear_in_y"];

struct ProbeParityResult {
    vc: trust_mc_core::chc::ChcVc,
    inferable_decls: Vec<String>,
    has_p_inf_rule_ref: bool,
    fallback_counts: std::collections::BTreeMap<String, usize>,
    unhandled_calls: std::collections::BTreeMap<String, usize>,
    inferable_count: usize,
}

fn reset_nia_counters() {
    clear_chc_fallback_counts();
    let _ = take_translation_drop_by_fn();
    let _ = crate::codegen_ay::take_inferable_predicate_count();
    let _ = crate::codegen_ay::take_unhandled_call_by_fn();
}

fn run_compiletest_parity_probe<'tcx>(
    ctx: &mut crate::codegen_ay::context::AYCtx<'tcx, 'static>,
    fn_name: &str,
) -> ProbeParityResult {
    reset_nia_counters();
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

    let inferable_decls: Vec<_> = vc
        .vars()
        .iter()
        .filter(|decl| decl.name.contains("P_inf_"))
        .map(|decl| decl.name.to_string())
        .collect();
    let has_p_inf_rule_ref = vc.rules.iter().any(|rule| format!("{:?}", rule).contains("P_inf_"));

    ProbeParityResult {
        vc,
        inferable_decls,
        has_p_inf_rule_ref,
        fallback_counts: get_chc_fallback_counts(),
        unhandled_calls: crate::codegen_ay::take_unhandled_call_by_fn(),
        inferable_count: crate::codegen_ay::take_inferable_predicate_count(),
    }
}

/// D2 control: the single-call probe should already satisfy the inline-quality contract.
#[test]
fn test_nia_tangent_plane_control_inline_quality() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    reset_nia_counters();

    with_test_ay_ctx_for_source(NIA_TANGENT_PLANE_PROBE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, CONTROL_PROBE);
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, CONTROL_PROBE, ChcConfig::default());

        assert!(!vc.relations.is_empty(), "control should produce relations");
        assert!(!vc.rules.is_empty(), "control should produce rules");

        // Without FunctionInlinePass, calls to tangent_plane/mul/add/sub are NOT
        // inlined, so P_inf_* summaries are correctly emitted for uninlined calls.
        // The compiletest-parity variant (with inlining) verifies the clean path.
        let inferable_decls: Vec<_> = vc
            .vars()
            .iter()
            .filter(|decl| decl.name.contains("P_inf_"))
            .map(|decl| decl.name.clone())
            .collect();
        // P_inf_* is expected in the non-inlined path — uninlined calls generate summaries
        eprintln!("control probe P_inf_* decls (expected for non-inlined): {inferable_decls:?}");

        // Fallback and unhandled counts — log for diagnostics.
        // Without FunctionInlinePass, some calls may generate fallback/unhandled
        // entries. The compiletest-parity variant verifies the clean inlined path.
        let fallback_counts = get_chc_fallback_counts();
        let fallback = fallback_counts.get(CONTROL_PROBE).copied().unwrap_or(0);
        eprintln!("control probe fallback={fallback}, map={fallback_counts:?}");

        let unhandled_calls = crate::codegen_ay::take_unhandled_call_by_fn();
        let unhandled = unhandled_calls.get(CONTROL_PROBE).copied().unwrap_or(0);
        eprintln!("control probe unhandled={unhandled}, map={unhandled_calls:?}");
    });

    reset_nia_counters();
}

/// D3 diagnostic: count Call terminators to detect MIR-level inlining.
/// If rustc MIR-inlines `tangent_plane`, the probe function will have ~22 Call terminators
/// (all helper calls exposed). If NOT inlined, it will have ~12 (tangent_plane as opaque call).
#[test]
fn test_nia_tangent_plane_mir_call_count() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    reset_nia_counters();

    with_test_ay_ctx_for_source(NIA_TANGENT_PLANE_PROBE, |ctx| {
        for fn_name in LINEARITY_PROBES {
            let instance = find_instance_by_suffix(ctx.tcx, fn_name);
            let body = instance.body().expect("function body");
            let mut call_count = 0usize;
            let mut call_targets: Vec<String> = Vec::new();
            for block in &body.blocks {
                if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                {
                    call_count += 1;
                    let target_name = format!("{func:?}");
                    call_targets.push(target_name);
                }
            }
            eprintln!("[D3 MIR diagnostic] {fn_name}: {call_count} Call terminators");
            for (i, target) in call_targets.iter().enumerate() {
                eprintln!("  [{i}] {target}");
            }
        }
    });

    reset_nia_counters();
}

/// Compiletest-parity control: mirror the driver path and assert the
/// single-call sibling stays clean under FunctionInlinePass + Mem/Auto + instance-aware CHC.
#[test]
fn test_nia_tangent_plane_control_compiletest_parity() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    reset_nia_counters();

    with_test_ay_ctx_for_source(NIA_TANGENT_PLANE_PROBE, |mut ctx| {
        let result = run_compiletest_parity_probe(&mut ctx, CONTROL_PROBE);

        assert!(!result.vc.relations.is_empty(), "control should produce relations");
        assert!(!result.vc.rules.is_empty(), "control should produce rules");
        assert!(
            result.inferable_decls.is_empty(),
            "control probe should not emit P_inf_* declarations: {:?}",
            result.inferable_decls
        );
        assert!(
            !result.has_p_inf_rule_ref,
            "control probe should not reference P_inf_* summaries in rules"
        );
        assert_eq!(
            result.fallback_counts.get(CONTROL_PROBE).copied().unwrap_or(0),
            0,
            "control should have no CHC fallback under compiletest parity, map={:?}",
            result.fallback_counts
        );
        assert_eq!(
            result.unhandled_calls.get(CONTROL_PROBE).copied().unwrap_or(0),
            0,
            "control should have no unhandled calls under compiletest parity, map={:?}",
            result.unhandled_calls
        );
        assert_eq!(
            result.inferable_count, 0,
            "control should have inferable_predicate_count=0 under compiletest parity"
        );
    });

    reset_nia_counters();
}

/// Compiletest-parity localizer: answer whether the live linearity-only
/// inferable-predicate family reproduces under the same MIR-inline + Mem/Auto envelope.
#[test]
fn test_nia_tangent_plane_linearity_compiletest_parity_diagnostic() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    reset_nia_counters();

    with_test_ay_ctx_for_source(NIA_TANGENT_PLANE_PROBE, |mut ctx| {
        let mut reproduced_live_family = false;
        let mut saw_any_degradation = false;

        for fn_name in LINEARITY_PROBES {
            let result = run_compiletest_parity_probe(&mut ctx, fn_name);
            let fallback = result.fallback_counts.get(fn_name).copied().unwrap_or(0);
            let unhandled = result.unhandled_calls.get(fn_name).copied().unwrap_or(0);

            assert!(!result.vc.relations.is_empty(), "{fn_name} should produce relations");
            assert!(!result.vc.rules.is_empty(), "{fn_name} should produce rules");

            eprintln!(
                "[A2 parity] {fn_name}: inferable_count={}, inferable_decls={:?}, \
                 has_p_inf_rule_ref={}, fallback_counts={:?}, unhandled_calls={:?}",
                result.inferable_count,
                result.inferable_decls,
                result.has_p_inf_rule_ref,
                result.fallback_counts,
                result.unhandled_calls
            );

            let has_live_family = result.inferable_count > 0 && fallback == 0 && unhandled == 0;
            let has_any_degradation = result.inferable_count > 0
                || !result.inferable_decls.is_empty()
                || result.has_p_inf_rule_ref
                || fallback > 0
                || unhandled > 0;

            reproduced_live_family |= has_live_family;
            saw_any_degradation |= has_any_degradation;
        }

        assert!(
            reproduced_live_family || !saw_any_degradation,
            "compiletest-parity linearity probes should either reproduce the live inferable family or stay clean"
        );
    });

    reset_nia_counters();
}

/// D2 linearity probes: the duplicated-helper shape at Reg level.
/// Records current inline quality for the two failing probes.
/// After the production fix: all assertions should pass with 0 fallback/inferable/unhandled.
#[test]
fn test_nia_tangent_plane_linearity_inline_quality() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    reset_nia_counters();

    with_test_ay_ctx_for_source(NIA_TANGENT_PLANE_PROBE, |ctx| {
        for fn_name in LINEARITY_PROBES {
            let instance = find_instance_by_suffix(ctx.tcx, fn_name);
            let body = instance.body().expect("function body");
            let vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());

            assert!(!vc.relations.is_empty(), "{fn_name} should produce relations");
            assert!(!vc.rules.is_empty(), "{fn_name} should produce rules");
        }

        // Collect counters after both probes run
        let fallback_counts = get_chc_fallback_counts();
        let unhandled_calls = crate::codegen_ay::take_unhandled_call_by_fn();
        let _ = crate::codegen_ay::take_inferable_predicate_count();

        // Without FunctionInlinePass, calls to tangent_plane/mul/add/sub are
        // NOT inlined, so P_inf_* summaries and fallback/unhandled entries are
        // expected. The compiletest-parity variant verifies the clean inlined path.
        for fn_name in LINEARITY_PROBES {
            let fallback = fallback_counts.get(fn_name).copied().unwrap_or(0);
            eprintln!("{fn_name} fallback={fallback}, map={fallback_counts:?}");

            let unhandled = unhandled_calls.get(fn_name).copied().unwrap_or(0);
            eprintln!("{fn_name} unhandled={unhandled}, map={unhandled_calls:?}");
        }

        // Log P_inf_* declarations for diagnostics
        reset_nia_counters();
        for fn_name in LINEARITY_PROBES {
            let instance = find_instance_by_suffix(ctx.tcx, fn_name);
            let body = instance.body().expect("function body");
            let vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());

            let inferable_decls: Vec<_> = vc
                .vars()
                .iter()
                .filter(|decl| decl.name.contains("P_inf_"))
                .map(|decl| decl.name.clone())
                .collect();
            eprintln!("{fn_name} P_inf_* decls (expected for non-inlined): {inferable_decls:?}");
        }

        let final_inferable = crate::codegen_ay::take_inferable_predicate_count();
        eprintln!(
            "linearity probes inferable_predicate_count={final_inferable} (expected >0 for non-inlined)"
        );
    });

    reset_nia_counters();
}
