// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Additional solver-backed semantic guards for `kani::any_where` follow-on regressions.

use super::common::*;
use crate::codegen_ay::emit_chc;

const ANY_WHERE_CAPTURE_ASSERT_SOURCE: &str = r#"
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

    pub fn probe_any_where_capture_assert() {
        let bound: u32 = 5;
        let x: u32 = kani::any_where(|v: &u32| *v < bound);
        assert!(x < bound);
    }
"#;

#[test]
fn test_any_where_scalar_capture_solver_produces_unsat() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    clear_chc_fallback_counts();
    let _ = take_translation_drop_by_fn();
    let _ = crate::codegen_ay::take_inferable_predicate_count();

    with_test_ay_ctx_for_source(ANY_WHERE_CAPTURE_ASSERT_SOURCE, |ctx| {
        let fn_name = "probe_any_where_capture_assert";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());

        assert!(!vc.rules.is_empty(), "{fn_name} should produce rules");
        assert!(has_any_constraints(&vc), "{fn_name} should constrain the VC");

        let inferable_decls: Vec<_> = vc
            .vars()
            .iter()
            .filter(|decl| decl.name.contains("P_inf"))
            .map(|decl| decl.name.clone())
            .collect();
        assert!(
            inferable_decls.is_empty(),
            "{fn_name} should inline scalar-capture any_where closure instead of emitting inferable summaries: {inferable_decls:?}"
        );

        let fallback_count = get_chc_fallback_counts().get(fn_name).copied().unwrap_or(0);
        assert_eq!(
            fallback_count, 0,
            "{fn_name} should avoid CHC fallback while lowering scalar-capture any_where"
        );

        let smt = emit_chc(&vc).to_string();
        let result = run_z3_on_smt2_with_timeout(&smt, 5);
        assert_eq!(
            result.as_deref(),
            Ok("unsat"),
            "shared-ref scalar captures in any_where must be concrete, not free CHC variables"
        );
    });

    let translation_drops = take_translation_drop_by_fn();
    let drop_count = translation_drops.get("probe_any_where_capture_assert").copied().unwrap_or(0);
    assert_eq!(
        drop_count, 0,
        "probe_any_where_capture_assert should have zero translation drops, map={translation_drops:?}"
    );

    clear_chc_fallback_counts();
    let _ = take_translation_drop_by_fn();
    let _ = crate::codegen_ay::take_inferable_predicate_count();
}

const ANY_ASSUME_VEC_LEN_ASSERT_SOURCE: &str = r#"
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
    }

    pub fn probe_any_assume_vec_len_assert() {
        let v = vec![1u32, 2, 3];
        let idx: usize = kani::any();
        kani::assume(idx < v.len());
        assert!(idx < 3);
    }
"#;

#[test]
fn test_any_assume_vec_len_solver_produces_unsat() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    clear_chc_fallback_counts();
    let _ = take_translation_drop_by_fn();
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
    let _ = crate::codegen_ay::take_inferable_predicate_count();

    with_test_ay_ctx_for_source(ANY_ASSUME_VEC_LEN_ASSERT_SOURCE, |ctx| {
        let fn_name = "probe_any_assume_vec_len_assert";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            fn_name,
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        assert!(!vc.rules.is_empty(), "{fn_name} should produce rules");
        assert!(has_any_constraints(&vc), "{fn_name} should constrain the VC");

        let inferable_decls: Vec<_> = vc
            .vars()
            .iter()
            .filter(|decl| decl.name.contains("P_inf"))
            .map(|decl| decl.name.clone())
            .collect();
        assert!(
            inferable_decls.is_empty(),
            "{fn_name} should not emit inferable summaries for plain any+assume+Vec::len: {inferable_decls:?}"
        );

        let fallback_count = get_chc_fallback_counts().get(fn_name).copied().unwrap_or(0);
        assert_eq!(
            fallback_count, 0,
            "{fn_name} should avoid CHC fallback on the any+assume+Vec::len path"
        );

        let smt = emit_chc(&vc).to_string();
        assert_z3_result(&smt, "unsat");
    });

    let translation_drops = take_translation_drop_by_fn();
    let translation_drop_sites = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
    let drop_count = translation_drops.get("probe_any_assume_vec_len_assert").copied().unwrap_or(0);
    let fn_reasons =
        translation_drop_sites.get("probe_any_assume_vec_len_assert").cloned().unwrap_or_default();
    let resume_abort_count = fn_reasons.get("resume_abort").copied().unwrap_or(0);
    let non_resume_drops = drop_count.saturating_sub(resume_abort_count);
    assert_eq!(
        non_resume_drops, 0,
        "probe_any_assume_vec_len_assert should have zero non-resume_abort translation drops. \
         total={drop_count}, resume_abort={resume_abort_count}, site_reasons={fn_reasons:?}"
    );

    clear_chc_fallback_counts();
    let _ = take_translation_drop_by_fn();
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
    let _ = crate::codegen_ay::take_inferable_predicate_count();
}
