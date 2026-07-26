// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Regression coverage for `tests/trust_mc/FunctionSymbols/main.rs`.

use super::common::*;
use crate::codegen_ay::emit_chc;

const FUNCTION_SYMBOLS_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![allow(unpredictable_function_pointer_comparisons)]

    pub fn probe_reify_fn_pointer() {
        assert!(poly::<usize> as fn() == poly::<usize> as fn());
        assert!(poly::<isize> as fn() != poly::<usize> as fn());
    }

    fn poly<T>() {}

    pub fn probe_fn_pointer_call() {
        assert_eq!(id(false), false);
        assert_eq!((id::<bool> as fn(bool) -> bool)(false), false);
        assert_eq!(id(true), true);
        assert_eq!((id::<bool> as fn(bool) -> bool)(true), true);
    }

    fn id<T>(x: T) -> T {
        x
    }

    struct Wrapper<T> {
        inner: T,
    }

    pub fn probe_fn_wrapper() {
        let w = Wrapper { inner: id::<bool> };
        assert!(w.inner as fn(bool) -> bool == id::<bool> as fn(bool) -> bool);
        assert_eq!((w.inner)(false), false);
        assert_eq!((w.inner)(true), true);
    }
"#;

fn assert_function_symbols_probe_is_non_degenerate(fn_name: &str) {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);

    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
    let _ = crate::codegen_ay::take_inferable_predicate_count();

    with_test_ay_ctx_for_source(FUNCTION_SYMBOLS_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            fn_name,
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        let (vc, _, diagnostics) = chc_ctx.translate_with_diagnostics();
        let smt = emit_chc(&vc).to_string();
        let translation_sites = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
        let fn_sites = translation_sites.get(fn_name).cloned().unwrap_or_default();

        let inferable_decls: Vec<_> = vc
            .vars()
            .iter()
            .filter(|decl| decl.name.starts_with("P_inf_"))
            .map(|decl| decl.name.clone())
            .collect();
        let has_p_inf_rule = vc.rules.iter().any(|rule| format!("{rule:?}").contains("P_inf_"));
        let has_error_rule = vc.rules.iter().any(|rule| rule.head.name.as_str() == "error");

        assert!(
            vc.relations.iter().any(|relation| relation.name == "error"),
            "{fn_name}: missing error relation"
        );
        assert!(
            vc.relations.iter().any(|relation| relation.name.contains("__bb0")),
            "{fn_name}: missing bb0 entry relation"
        );
        assert!(
            has_error_rule,
            "{fn_name} must keep an error-headed obligation; otherwise compiletest reports trivial_safe=no_error_rule"
        );
        assert_eq!(
            diagnostics.place_translation_drop.get(),
            0,
            "{fn_name} should not use demoted translation drops; sites={fn_sites:?}"
        );
        assert_eq!(
            diagnostics.inferable_predicate.get(),
            0,
            "{fn_name} should stay off inferable summaries"
        );
        assert!(
            inferable_decls.is_empty(),
            "{fn_name} should not emit P_inf_* declarations: {inferable_decls:?}"
        );
        assert!(
            !has_p_inf_rule,
            "{fn_name} should not reference P_inf_* summaries in emitted rules"
        );
        assert_z3_result(&smt, "unsat");
    });
}

#[test]
fn test_function_symbols_fn_pointer_call_keeps_error_obligation() {
    assert_function_symbols_probe_is_non_degenerate("probe_fn_pointer_call");
}

#[test]
fn test_function_symbols_fn_wrapper_keeps_error_obligation() {
    assert_function_symbols_probe_is_non_degenerate("probe_fn_wrapper");
}

#[test]
fn test_function_symbols_reify_fn_pointer_keeps_error_obligation() {
    assert_function_symbols_probe_is_non_degenerate("probe_reify_fn_pointer");
}
