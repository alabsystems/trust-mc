// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Regression tests for CHC method-path `offset_from[_unsigned]` dispatch.
//!
//! Part of #3778: std/core pointer methods must route through the same CHC
//! pointer-distance lowering as the Kani model hook path.

#![allow(clippy::unwrap_used, clippy::panic)]

use super::super::chc_call_context::DispatchCallContext;
use super::super::codegen_call_cmp_string::CallCmpString;
use super::common::*;

/// Assert that a function has no encoding-gap translation drops (tolerating
/// `resume_abort` sound over-approximation on unwind paths), no unhandled
/// calls, and no inferable predicates. Resets counters after checking.
fn assert_no_encoding_gap_drops_and_cleanup(fn_name: &str) {
    let translation_drops = take_translation_drop_by_fn();
    let site_reasons =
        crate::codegen_ay::chc::codegen_ctx::take_translation_drop_site_reasons_by_fn();
    let drop_count = translation_drops.get(fn_name).copied().unwrap_or(0);
    let fn_reasons = site_reasons.get(fn_name).cloned().unwrap_or_default();
    let resume_abort_count = fn_reasons.get("resume_abort").copied().unwrap_or(0);
    let non_resume_drops = drop_count.saturating_sub(resume_abort_count);
    assert_eq!(
        non_resume_drops, 0,
        "{fn_name} should have zero non-resume_abort translation drops. \
         total={drop_count}, resume_abort={resume_abort_count}, site_reasons={fn_reasons:?}"
    );

    let unhandled_calls = crate::codegen_ay::take_unhandled_call_by_fn();
    let unhandled_count = unhandled_calls.get(fn_name).copied().unwrap_or(0);
    assert_eq!(
        unhandled_count, 0,
        "{fn_name} should have zero unhandled calls, map={unhandled_calls:?}"
    );

    let inferable_count = crate::codegen_ay::take_inferable_predicate_count();
    assert_eq!(
        inferable_count, 0,
        "{fn_name}: optimized path should avoid inferable-predicate summaries"
    );

    reset_ptr_offset_method_counters();
    let _ = take_translation_drop_by_fn();
    let _ = crate::codegen_ay::take_inferable_predicate_count();
}

const PTR_OFFSET_METHOD_SOURCE: &str = r#"
    #![allow(dead_code)]

    use core::ptr::NonNull;

    pub unsafe fn probe_ptr_offset_from_unsigned_raw(
        lhs: *mut [u64; 3],
        rhs: *mut [u64; 3],
    ) -> usize {
        unsafe { lhs.offset_from_unsigned(rhs) }
    }

    pub unsafe fn probe_ptr_offset_from_unsigned_nonnull(
        lhs: NonNull<[u64; 3]>,
        rhs: NonNull<[u64; 3]>,
    ) -> usize {
        unsafe { lhs.offset_from_unsigned(rhs) }
    }
 "#;

const PTR_OFFSET_RUNTIME_GUARD_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![feature(register_tool)]
    #![register_tool(kanitool)]

    mod kani {
        #[kanitool::fn_marker = "AnyModel"]
        pub fn any<T>() -> T {
            panic!("model-only marker function")
        }

        #[kanitool::fn_marker = "AssumeHook"]
        pub fn assume(_cond: bool) {}

        #[inline(always)]
        pub fn any_where<T, F: FnOnce(&T) -> bool>(f: F) -> T {
            let result = any();
            assume(f(&result));
            result
        }
    }

    pub fn probe_offset_non_power_two_runtime_guard(mut v: Vec<[u64; 3]>) -> bool {
        unsafe {
            let offset = kani::any_where(|o: &usize| *o <= v.len());
            let begin = v.as_mut_ptr();
            let end = begin.add(offset);
            end.offset_from_unsigned(begin) == offset
        }
    }
"#;

/// Combined probe source: exact literal shape from the real `offset_non_power_two`
/// compiletest harness. Uses `vec![[0u64; 3], [2u64; 3]]` (concrete literal), not
/// a parameter-based abstract Vec. Part of #3783 D1.
const PTR_OFFSET_VEC_LITERAL_COMBINED_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![feature(register_tool)]
    #![register_tool(kanitool)]

    mod kani {
        #[kanitool::fn_marker = "AnyModel"]
        pub fn any<T>() -> T {
            panic!("model-only marker function")
        }

        #[kanitool::fn_marker = "AssumeHook"]
        pub fn assume(_cond: bool) {}

        #[inline(always)]
        pub fn any_where<T, F: FnOnce(&T) -> bool>(f: F) -> T {
            let result = any();
            assume(f(&result));
            result
        }
    }

    pub fn probe_vec_literal_offset_combined() -> bool {
        let mut v = vec![[0u64; 3], [2u64; 3]];
        unsafe {
            let offset = kani::any_where(|o: &usize| *o <= v.len());
            let begin = v.as_mut_ptr();
            let end = begin.add(offset);
            end.offset_from_unsigned(begin) == offset
        }
    }
"#;

fn reset_ptr_offset_method_counters() {
    clear_chc_fallback_counts();
    let _ = take_translation_drop_by_fn();
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
    let _ = crate::codegen_ay::take_inferable_predicate_count();
    let _ = crate::codegen_ay::take_unhandled_call_by_fn();
}

fn with_ptr_offset_method_dispatch(
    probe_suffix: &str,
    assertions: impl FnOnce(
        &mut ChcCtx<'_, '_>,
        &Operand,
        &[Operand],
        &Place,
        usize,
        &RelationApp,
        &[Expr],
        &HashSet<usize>,
        usize,
        &str,
    ) + Send,
) {
    with_test_ay_ctx_for_source(PTR_OFFSET_METHOD_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, probe_suffix);
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, probe_suffix, ChcConfig::default());
        chc_ctx.declare_block_relations();

        use rustc_public::mir::TerminatorKind;
        let (bb_idx, func, args, destination, target, callee_path) = body
            .blocks
            .iter()
            .enumerate()
            .find_map(|(bb_idx, block)| {
                if let TerminatorKind::Call {
                    func, args, destination, target: Some(target), ..
                } = &block.terminator.kind
                    && let Some(path) = chc_ctx.resolve_callee_path(func)
                    && path.contains("offset_from_unsigned")
                {
                    Some((bb_idx, func.clone(), args.clone(), destination.clone(), *target, path))
                } else {
                    None
                }
            })
            .unwrap_or_else(|| {
                panic!("expected offset_from_unsigned call terminator in {probe_suffix}")
            });

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

        assertions(
            &mut chc_ctx,
            &func,
            &args,
            &destination,
            target,
            &from_app,
            &stmt_constraints,
            &modified_locals,
            bb_idx,
            &callee_path,
        );
    });
}

fn assert_precise_ptr_offset_dispatch(
    chc_ctx: &mut ChcCtx<'_, '_>,
    func: &Operand,
    actual_args: &[Operand],
    destination: &Place,
    target: usize,
    from_app: &RelationApp,
    stmt_constraints: &[Expr],
    modified_locals: &HashSet<usize>,
    bb_idx: usize,
    callee_path: &str,
) {
    assert!(
        callee_path.contains("offset_from_unsigned"),
        "precondition: expected offset_from_unsigned callee path, got {callee_path}"
    );
    let before_rules = chc_ctx.vc.rules.len();
    assert_eq!(chc_ctx.sound_fallback_count(), 0, "precondition: sound fallback count at zero");
    assert_eq!(chc_ctx.fallback_count, 0, "precondition: demoted fallback count at zero");
    assert_eq!(
        chc_ctx.diagnostics.unhandled_call.get(),
        0,
        "precondition: unhandled-call counter at zero"
    );
    assert_eq!(
        chc_ctx.diagnostics.inferable_predicate.get(),
        0,
        "precondition: inferable counter at zero"
    );

    let target_opt = Some(target);
    let dcx = DispatchCallContext {
        bb_idx,
        func,
        args: actual_args,
        destination,
        target: &target_opt,
        from_app,
        stmt_constraints,
        modified_locals,
        callee_path: None,
    };

    assert!(
        chc_ctx.try_dispatch_call_misc_intrinsic(&dcx),
        "{callee_path} should be intercepted by misc intrinsic dispatch"
    );
    assert_eq!(chc_ctx.vc.rules.len(), before_rules + 1, "expected one goto rule");
    assert_eq!(
        chc_ctx.sound_fallback_count(),
        0,
        "{callee_path} should stay on the precise path without sound fallback"
    );
    assert_eq!(chc_ctx.fallback_count, 0, "{callee_path} should not use demoted fallback");
    assert_eq!(
        chc_ctx.diagnostics.unhandled_call.get(),
        0,
        "{callee_path} should avoid the generic unhandled-call lane"
    );
    assert_eq!(
        chc_ctx.diagnostics.inferable_predicate.get(),
        0,
        "{callee_path} should not create inferable-predicate summaries"
    );
    assert_rule_contains_expr_kind(
        &chc_ctx.vc,
        callee_path,
        |e| matches!(e.value(), ExprValue::BvUDiv(_, _)),
        "bvudiv",
    );
}

#[test]
fn test_ptr_offset_from_unsigned_raw_method_dispatch_emits_bvudiv_without_fallbacks() {
    with_ptr_offset_method_dispatch(
        "probe_ptr_offset_from_unsigned_raw",
        assert_precise_ptr_offset_dispatch,
    );
}

#[test]
fn test_ptr_offset_from_unsigned_nonnull_method_dispatch_emits_bvudiv_without_fallbacks() {
    with_ptr_offset_method_dispatch(
        "probe_ptr_offset_from_unsigned_nonnull",
        assert_precise_ptr_offset_dispatch,
    );
}

#[test]
fn test_ptr_offset_from_unsigned_method_pipeline_avoids_unhandled_and_inferable_counters() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    reset_ptr_offset_method_counters();

    with_test_ay_ctx_for_source(PTR_OFFSET_METHOD_SOURCE, |ctx| {
        for fn_name in
            ["probe_ptr_offset_from_unsigned_raw", "probe_ptr_offset_from_unsigned_nonnull"]
        {
            let instance = find_instance_by_suffix(ctx.tcx, fn_name);
            let body = instance.body().expect("function body");
            let vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());

            assert_vc_structure(&vc, fn_name, body.blocks.len());
            assert_rule_contains_expr_kind(
                &vc,
                fn_name,
                |e| matches!(e.value(), ExprValue::BvUDiv(_, _)),
                "bvudiv",
            );
        }

        let unhandled_calls = crate::codegen_ay::take_unhandled_call_by_fn();
        for fn_name in
            ["probe_ptr_offset_from_unsigned_raw", "probe_ptr_offset_from_unsigned_nonnull"]
        {
            let fallback_count = get_chc_fallback_counts().get(fn_name).copied().unwrap_or(0);
            assert_eq!(
                fallback_count, 0,
                "{fn_name} should not record CHC fallback after method-path bridge"
            );

            let unhandled_count = unhandled_calls.get(fn_name).copied().unwrap_or(0);
            assert_eq!(
                unhandled_count, 0,
                "{fn_name} should not increment unhandled-call counters after method-path bridge"
            );
        }

        let inferable_count = crate::codegen_ay::take_inferable_predicate_count();
        assert_eq!(
            inferable_count, 0,
            "method-path offset_from_unsigned probes should keep inferable-predicate count at zero"
        );
    });

    reset_ptr_offset_method_counters();
}

#[test]
fn test_offset_from_unsigned_runtime_ptr_ge_full_pipeline_avoids_inferable_summary() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    reset_ptr_offset_method_counters();
    let _ = take_translation_drop_by_fn();

    with_test_ay_ctx_for_source(PTR_OFFSET_RUNTIME_GUARD_SOURCE, |ctx| {
        let fn_name = "probe_offset_non_power_two_runtime_guard";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            fn_name,
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        assert_vc_structure(&vc, fn_name, body.blocks.len());
        assert_rule_contains_expr_kind(
            &vc,
            fn_name,
            |e| matches!(e.value(), ExprValue::BvUDiv(_, _)),
            "bvudiv",
        );

        let inferable_decls: Vec<_> = vc
            .vars()
            .iter()
            .filter(|decl| decl.name.starts_with("P_inf_"))
            .map(|decl| decl.name.clone())
            .collect();
        assert!(
            inferable_decls.is_empty(),
            "{fn_name} should not emit inferable summaries after runtime_ptr_ge handling: {inferable_decls:?}"
        );

        let fallback_count = get_chc_fallback_counts().get(fn_name).copied().unwrap_or(0);
        assert_eq!(
            fallback_count, 0,
            "{fn_name} should have zero CHC fallback count after fn-inline helper recovery"
        );
    });

    assert_no_encoding_gap_drops_and_cleanup("probe_offset_non_power_two_runtime_guard");
}

// ═══════════════════════════════════════════════════════════════════════
// Combined vec-literal + runtime guard + offset_from_unsigned probe
// Part of #3783 D1: exact compiletest harness shape
// ═══════════════════════════════════════════════════════════════════════

/// C3: No inferable summaries present in the VC.
fn assert_no_inferable_summaries(vc: &trust_mc_core::chc::ChcVc, fn_name: &str) {
    let inferable_decls: Vec<_> = vc
        .vars()
        .iter()
        .filter(|decl| decl.name.starts_with("P_inf_"))
        .map(|decl| decl.name.clone())
        .collect();
    assert!(
        inferable_decls.is_empty(),
        "{fn_name} should not emit inferable summaries: {inferable_decls:?}"
    );
}

/// C5: The VC body or head mentions the concrete literal length 2 as a BV64 constant.
fn assert_vc_contains_literal_two_bv64(vc: &trust_mc_core::chc::ChcVc, fn_name: &str) {
    let has_literal_two =
        vc.rules.iter().any(|rule| {
            let in_body = rule.body.constraints.iter().any(|c| {
            constraint_tree_contains(c, &|e| matches!(
                e.value(),
                ExprValue::BitVecConst { value, width } if *value == 2u64.into() && *width == 64
            ))
        });
            let in_head = rule.head.args.iter().any(|a| {
            constraint_tree_contains(a, &|e| matches!(
                e.value(),
                ExprValue::BitVecConst { value, width } if *value == 2u64.into() && *width == 64
            ))
        });
            in_body || in_head
        });
    assert!(
        has_literal_two,
        "{fn_name}: VC should contain the concrete vec literal length 2 as a BV64 constant. \
         The SliceIntoVec path may not be propagating the concrete array length."
    );
}

/// C1-C5: Assert precise-encoding invariants on the combined-probe VC.
/// (structure, bvudiv lowering, no inferable summaries, no CHC fallback, literal-2 BV).
fn assert_vec_literal_combined_precise_vc(
    vc: &trust_mc_core::chc::ChcVc,
    fn_name: &str,
    block_count: usize,
) {
    // C1: VC has valid structure
    assert_vc_structure(vc, fn_name, block_count);

    // C2: VC contains bvudiv (offset_from_unsigned lowering)
    assert_rule_contains_expr_kind(
        vc,
        fn_name,
        |e| matches!(e.value(), ExprValue::BvUDiv(_, _)),
        "bvudiv",
    );

    // C3: No inferable summaries
    assert_no_inferable_summaries(vc, fn_name);

    // C4: No CHC fallback
    let fallback_count = get_chc_fallback_counts().get(fn_name).copied().unwrap_or(0);
    assert_eq!(fallback_count, 0, "{fn_name} should have zero CHC fallback count");

    // C5: VC contains the concrete literal length 2 as a bitvec constant
    assert_vc_contains_literal_two_bv64(vc, fn_name);
}

/// Full-pipeline test for the exact `offset_non_power_two` compiletest shape:
/// `vec![[0u64; 3], [2u64; 3]]` + `kani::any_where` + `offset_from_unsigned`.
///
/// This connects the three separately-tested pieces (SliceIntoVec literal,
/// Vec::len capture in any_where, pointer offset dispatch) into one VC and
/// checks that the combined path stays on the precise encoding lane.
#[test]
fn test_vec_literal_offset_combined_full_pipeline_precise_encoding() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    reset_ptr_offset_method_counters();
    let _ = take_translation_drop_by_fn();

    with_test_ay_ctx_for_source(PTR_OFFSET_VEC_LITERAL_COMBINED_SOURCE, |ctx| {
        let fn_name = "probe_vec_literal_offset_combined";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            fn_name,
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        assert_vec_literal_combined_precise_vc(&vc, fn_name, body.blocks.len());
    });

    // C6-C8: No encoding-gap drops, no unhandled calls, no inferable predicates.
    // resume_abort is tolerated (vec! allocation can panic → Resume/Abort terminator
    // is conservatively over-approximated — sound, not an encoding gap).
    assert_no_encoding_gap_drops_and_cleanup("probe_vec_literal_offset_combined");
}
