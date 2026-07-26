// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Regression tests for ptr-comparison helper inlining.
//!
//! Part of #4030: `compare_diff` / `compare_equal` in
//! `tests/trust_mc/PointerComparison/ptr_comparison.rs` exceed the shared 16-block
//! fn-inline gate and used to fall back to `P_inf_*` summaries. CHC needs a
//! narrow raw-pointer helper budget so these proof helpers stay precise.

use super::common::*;

const PTR_COMPARISON_INLINE_HELPER_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![allow(ambiguous_wide_pointer_comparisons)]
    use std::cmp::Ordering;

    fn compare_diff<T: ?Sized>(smaller: *const T, bigger: *const T) {
        assert_eq!(smaller.cmp(&bigger), Ordering::Less);
        assert_eq!(bigger.cmp(&smaller), Ordering::Greater);

        assert!(smaller < bigger);
        assert!(smaller <= bigger);
        assert!(bigger > smaller);
        assert!(bigger >= smaller);
        assert!(bigger != smaller);

        assert!(!(smaller > bigger));
        assert!(!(smaller >= bigger));
        assert!(!(bigger <= smaller));
        assert!(!(bigger < smaller));
        assert!(!(bigger == smaller));
        assert!(!(std::ptr::eq(bigger, smaller)));

        assert_eq!(smaller.min(bigger), smaller);
        assert_eq!(smaller.max(bigger), bigger);
        assert_eq!(bigger.min(smaller), smaller);
        assert_eq!(bigger.max(smaller), bigger);
    }

    fn compare_equal<T: ?Sized>(obj1: *const T, obj2: *const T) {
        assert_eq!(obj1.cmp(&obj2), Ordering::Equal);
        assert!(obj1 <= obj2);
        assert!(obj1 >= obj2);
        assert!(obj1 == obj2);

        assert!(!(obj1 > obj2));
        assert!(!(obj1 < obj2));
        assert!(!(obj1 != obj2));

        assert_eq!(obj1.min(obj2), obj1);
        assert_eq!(obj1.max(obj2), obj1);
    }

    fn check_clamp<T: ?Sized>(object: *const T, smaller: *const T, bigger: *const T) {
        assert_eq!(object.clamp(smaller, bigger), object);
        assert_eq!(object.clamp(smaller, object), object);
        assert_eq!(object.clamp(object, bigger), object);

        assert_eq!(object.clamp(bigger, bigger), bigger);
        assert_eq!(object.clamp(smaller, smaller), smaller);
    }

    pub fn probe_check_thin_ptr_harness() {
        let array = [0u8; 10];
        let first_ptr: *const u8 = &array[0];
        let second_ptr: *const u8 = &array[5];

        compare_diff(first_ptr, second_ptr);
        compare_equal(first_ptr, first_ptr);
        check_clamp(&array[5], &array[0], &array[9]);
    }

    pub fn probe_check_slice_len_harness() {
        let array = [0u8; 10];
        let first_ptr: *const [u8] = &array[0..2];
        let second_ptr: *const [u8] = &array[0..4];

        compare_diff(first_ptr, second_ptr);
        compare_equal(first_ptr, first_ptr);
        check_clamp::<[u8]>(&array[4..6], &array[4..5], &array[4..]);
    }

"#;

fn assert_ptr_comparison_helper_harness(source: &str, fn_name: &str) {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);

    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
    let _ = crate::codegen_ay::take_inferable_predicate_count();

    with_test_ay_ctx_for_source(source, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            fn_name,
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        let (vc, _, diagnostics) = chc_ctx.translate_with_diagnostics();
        let smt = crate::codegen_ay::emit_chc(&vc).to_string();
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

        assert_vc_structure(&vc, fn_name, body.blocks.len());
        assert!(
            has_error_rule,
            "{fn_name} should keep an error-headed CHC obligation so compiletest reports clean proof, not trivial_safe=no_error_rule"
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
fn test_ptr_comparison_helpers_inline_without_p_inf_summaries() {
    assert_ptr_comparison_helper_harness(
        PTR_COMPARISON_INLINE_HELPER_SOURCE,
        "probe_check_thin_ptr_harness",
    );
}

#[test]
fn test_ptr_comparison_slice_len_helper_preserves_wide_metadata() {
    assert_ptr_comparison_helper_harness(
        PTR_COMPARISON_INLINE_HELPER_SOURCE,
        "probe_check_slice_len_harness",
    );
}
