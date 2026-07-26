// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Focused CHC regression tests for the non-Copy array consume family (#3984).
//!
//! The `for item in arr` loop on a non-Copy array desugars to:
//!   bb0: `IntoIterator::into_iter` → creates IntoIter
//!   bb2: `<IntoIter as Iterator>::next` (StubKind::IntoIterNext)
//!   bb5: `NonCopyWrapper::get`
//!
//! The `IntoIterNext` dispatch internally chains through:
//!   - `IndexRange::next` (collection lane)
//!   - Array-inner `OptionMap` pre-route (option_ptr dispatcher)
//!
//! These tests freeze the new dispatch paths at the `IntoIterNext` call level
//! and add a narrowness control proving generic `Option::map` still uses the
//! symbolic combinator.

#![allow(clippy::unwrap_used)]

use super::common::*;
use crate::codegen_ay::chc::chc_call_context::DispatchCallContext;
use crate::codegen_ay::chc::codegen_call::CallTerminator;
use crate::codegen_ay::stubs::StubKind;
use rustc_public::mir::TerminatorKind;

// ---------------------------------------------------------------------------
// Source probes
// ---------------------------------------------------------------------------

/// Non-Copy array consume: exercises IndexRange::next + OptionMap pre-route
/// internally when IntoIterNext is dispatched.
const NONCOPY_CONSUME_SOURCE: &str = r#"
    #![allow(dead_code)]

    struct NonCopyWrapper(u32);

    impl NonCopyWrapper {
        fn get(&self) -> u32 { self.0 }
    }

    pub fn probe_array_iter_noncopy_consume() -> [u32; 2] {
        let arr = [NonCopyWrapper(1), NonCopyWrapper(2)];
        let mut values = [0u32; 2];
        let mut idx = 0usize;
        for item in arr {
            values[idx] = item.get();
            idx += 1;
        }
        values
    }
"#;

/// Plain Option::map with no array iterator context.
const PLAIN_OPTION_MAP_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_plain_option_map(x: Option<u32>) -> Option<u32> {
        x.map(|v| v + 1)
    }
"#;

const ARRAY_ZST_REAL_FILE: &str = include_str!("../../../../../tests/trust_mc/Array/array-zst.rs");

fn strip_kani_attributes_for_unit_ctx(source: &str) -> String {
    let mut result = String::from(
        r#"
#![allow(dead_code)]
#![feature(register_tool)]
#![register_tool(kanitool)]

mod kani {
    pub trait Arbitrary: Sized {
        fn any() -> Self;
        fn any_array<const N: usize>() -> [Self; N];
    }

    #[inline(never)]
    pub fn any<T: Arbitrary>() -> T {
        T::any()
    }

    impl Arbitrary for u8 {
        #[inline(never)]
        fn any() -> Self {
            unsafe { any_raw_internal::<Self>() }
        }

        #[inline(never)]
        fn any_array<const N: usize>() -> [Self; N] {
            unsafe { any_raw_array::<Self, N>() }
        }
    }

    impl Arbitrary for () {
        #[inline(never)]
        fn any() -> Self {
            unsafe { any_raw_internal::<Self>() }
        }

        #[inline(never)]
        fn any_array<const N: usize>() -> [Self; N] {
            unsafe { any_raw_array::<Self, N>() }
        }
    }

    impl<T: Arbitrary, const N: usize> Arbitrary for [T; N] {
        #[inline(never)]
        fn any() -> Self {
            T::any_array::<N>()
        }

        fn any_array<const M: usize>() -> [Self; M] {
            panic!("nested any_array not used in array-zst regression probe")
        }
    }

    #[inline(never)]
    pub unsafe fn any_raw_internal<T: Copy>() -> T {
        any_raw::<T>()
    }

    #[inline(never)]
    pub unsafe fn any_raw_array<T: Copy, const N: usize>() -> [T; N] {
        any_raw::<[T; N]>()
    }

    #[kanitool::fn_marker = "AnyRawHook"]
    #[inline(never)]
    fn any_raw<T: Copy>() -> T {
        panic!("hooked by test MIR lowering")
    }
}

"#,
    );

    let mut skipping_check_zst_enum = false;
    let mut skip_brace_depth = 0i32;
    for line in source.lines() {
        let trimmed = line.trim();
        if skipping_check_zst_enum {
            skip_brace_depth += line.matches('{').count() as i32 - line.matches('}').count() as i32;
            if skip_brace_depth <= 0 {
                skipping_check_zst_enum = false;
            }
            continue;
        }
        if trimmed.starts_with("pub fn check_zst_enum()") {
            skipping_check_zst_enum = true;
            skip_brace_depth = line.matches('{').count() as i32 - line.matches('}').count() as i32;
            continue;
        }
        if trimmed.starts_with("#[kani::")
            || trimmed.starts_with("// kani-expect:")
            || trimmed.contains("kani::Arbitrary")
            || trimmed.starts_with("//!")
            || trimmed.starts_with("// Copyright")
            || trimmed.starts_with("// SPDX-License-Identifier:")
            || trimmed.starts_with("// Licensed under")
        {
            continue;
        }
        result.push_str(line);
        result.push('\n');
    }

    result
}

fn array_zst_real_file_source() -> String {
    strip_kani_attributes_for_unit_ctx(ARRAY_ZST_REAL_FILE)
}

fn assert_array_zst_real_file_has_no_prebuilt_fallback(fn_name: &str) {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    crate::codegen_ay::chc::clear_chc_fallback_counts();
    let _ = crate::codegen_ay::chc::take_translation_drop_by_fn();
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();

    let source = array_zst_real_file_source();
    with_test_ay_ctx_for_source(&source, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, ChcConfig::default());
        let (vc, _, diagnostics) = chc_ctx.translate_with_diagnostics();

        assert_vc_structure(&vc, fn_name, body.blocks.len());
        assert_eq!(
            diagnostics.unhandled_call.get(),
            0,
            "{fn_name} should translate without unhandled calls"
        );
        assert_eq!(
            crate::codegen_ay::chc::get_chc_fallback_counts().get(fn_name).copied().unwrap_or(0),
            0,
            "{fn_name} should not record CHC fallbacks on the real array-zst harness"
        );
    });

    let translation_sites = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
    let fn_reasons = translation_sites.get(fn_name).cloned().unwrap_or_default();
    assert_eq!(
        fn_reasons.get("call_dispatch_fallback_prebuilt").copied().unwrap_or(0),
        0,
        "{fn_name} should not hit prebuilt call fallback on the real array-zst harness, site_reasons={fn_reasons:?}"
    );
}

// ---------------------------------------------------------------------------
// Shared dispatch-call walker (same pattern as test_call_array_intoiter_identity)
// ---------------------------------------------------------------------------

fn with_dispatch_calls(
    source: &str,
    fn_name: &str,
    mut body: impl FnMut(&mut ChcCtx<'_, '_>, &DispatchCallContext<'_>) + Send,
) {
    with_test_ay_ctx_for_source(source, move |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let mir_body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &mir_body, fn_name, ChcConfig::default());
        chc_ctx.declare_block_relations();

        for (bb_idx, block) in mir_body.blocks.iter().enumerate() {
            let TerminatorKind::Call { func, args, destination, target, .. } =
                &block.terminator.kind
            else {
                continue;
            };
            let Some(target_bb) = *target else {
                continue;
            };

            let from_rel = chc_ctx.block_relations.get(&bb_idx).expect("source relation").clone();
            let output_args: Vec<_> = chc_ctx
                .state_var_mgr
                .state_vars
                .iter()
                .map(|(name, sort)| ay_bindings::Expr::var(name.to_string(), sort.clone()))
                .collect();
            let from_app = RelationApp::new(&from_rel, output_args);
            let stmt_constraints = [ay_bindings::Expr::bool_const(true)];
            let modified_locals = HashSet::new();
            let target_opt = Some(target_bb);
            let dcx = DispatchCallContext {
                bb_idx,
                func,
                args,
                destination,
                target: &target_opt,
                from_app: &from_app,
                stmt_constraints: &stmt_constraints,
                modified_locals: &modified_locals,
                callee_path: None,
            };

            body(&mut chc_ctx, &dcx);
        }
    });
}

// ---------------------------------------------------------------------------
// D2: IntoIterNext dispatch for non-Copy array — exercises IndexRange::next
//     and OptionMap pre-route internally
// ---------------------------------------------------------------------------

/// The `IntoIterNext` call for a non-Copy array should:
/// - be handled (not fall through to fn_inline or generic stub)
/// - emit transition rules
/// - not record sound fallbacks
/// - not increment stub_approximation (the OptionMap pre-route must fire)
#[test]
fn test_into_iter_next_noncopy_avoids_fallback_and_stub_approx() {
    let mut found = 0usize;
    with_dispatch_calls(
        NONCOPY_CONSUME_SOURCE,
        "probe_array_iter_noncopy_consume",
        |chc_ctx, dcx| {
            let Some(stub) = chc_ctx.detect_stub(dcx.func) else {
                return;
            };
            if stub != StubKind::IntoIterNext {
                return;
            }

            let before_fallback = chc_ctx.sound_fallback_count();
            let before_unhandled = chc_ctx.diagnostics.unhandled_call.get();
            let before_stub_approx = chc_ctx.diagnostics.stub_approximation.get();
            let before_rules = chc_ctx.vc.rules.len();

            assert!(
                chc_ctx.codegen_call_terminator(dcx),
                "IntoIterNext (non-Copy array) should be handled by call dispatch"
            );
            assert_eq!(
                chc_ctx.sound_fallback_count(),
                before_fallback,
                "IntoIterNext (non-Copy array) should not record a sound fallback"
            );
            assert_eq!(
                chc_ctx.diagnostics.unhandled_call.get(),
                before_unhandled,
                "IntoIterNext (non-Copy array) should not increment unhandled_call"
            );
            assert_eq!(
                chc_ctx.diagnostics.stub_approximation.get(),
                before_stub_approx,
                "IntoIterNext (non-Copy array) should not increment stub_approximation — \
                 the OptionMap pre-route must bypass the generic combinator"
            );
            assert!(
                chc_ctx.vc.rules.len() > before_rules,
                "IntoIterNext (non-Copy array) should emit at least one transition rule"
            );
            found += 1;
        },
    );

    assert_mir_pattern_found(found > 0, "IntoIterNext (non-Copy array)");
}

// ---------------------------------------------------------------------------
// D3: Full translate — non-Copy array consume produces clean VC
// ---------------------------------------------------------------------------

/// Full translation of the non-Copy consume probe should produce a VC with
/// no unhandled calls and no stub approximation increments.
#[test]
fn test_noncopy_consume_full_translate_no_stub_approximation() {
    with_test_ay_ctx_for_source(NONCOPY_CONSUME_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_array_iter_noncopy_consume");
        let body = instance.body().expect("function body");
        let chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_array_iter_noncopy_consume", ChcConfig::default());
        let (vc, _, diagnostics) = chc_ctx.translate_with_diagnostics();

        assert_vc_structure(&vc, "probe_array_iter_noncopy_consume", body.blocks.len());
        assert_eq!(
            diagnostics.unhandled_call.get(),
            0,
            "non-Copy array consume should not leave calls unhandled"
        );
        assert_eq!(
            diagnostics.stub_approximation.get(),
            0,
            "non-Copy array consume should not use any stub approximation — \
             the OptionMap pre-route should fire for the array-inner path"
        );
    });
}

// ---------------------------------------------------------------------------
// D4: Narrowness control — plain Option::map still uses generic combinator
// ---------------------------------------------------------------------------

#[test]
fn test_plain_option_map_uses_generic_combinator() {
    let mut found = 0usize;
    with_dispatch_calls(PLAIN_OPTION_MAP_SOURCE, "probe_plain_option_map", |chc_ctx, dcx| {
        let Some(stub) = chc_ctx.detect_stub(dcx.func) else {
            return;
        };
        if stub != StubKind::OptionMap {
            return;
        }

        let before_stub_approx = chc_ctx.diagnostics.stub_approximation.get();

        let handled = chc_ctx.codegen_call_terminator(dcx);
        assert!(handled, "plain Option::map should still be handled");
        assert!(
            chc_ctx.diagnostics.stub_approximation.get() > before_stub_approx,
            "plain Option::map should use the generic symbolic combinator \
                 (stub_approximation should increase)"
        );
        found += 1;
    });

    assert_mir_pattern_found(found > 0, "OptionMap (plain)");
}

#[test]
fn test_array_zst_real_file_zero_len_dispatch_has_no_fallbacking_calls() {
    assert_array_zst_real_file_has_no_prebuilt_fallback("check_zero_elems");
}

#[test]
fn test_array_zst_real_file_zst_dispatch_has_no_fallbacking_calls() {
    assert_array_zst_real_file_has_no_prebuilt_fallback("check_zst_elem");
}
