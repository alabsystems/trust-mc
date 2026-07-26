// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Regression tests for the `#3794` flattened-newtype translation-drop bucket.

use super::common::*;

const NEWTYPE_RECEIVER_SOURCE: &str = r#"
    #![allow(dead_code)]

    #[derive(Copy, Clone)]
    pub struct Wrapper(u8);

    impl Wrapper {
        fn value(&self) -> u8 {
            self.0
        }

        fn add(&self, rhs: u8) -> Wrapper {
            Wrapper(self.0.saturating_add(rhs))
        }
    }

    pub fn probe_newtype_bare_read(x: Wrapper) -> Wrapper {
        x
    }

    pub fn probe_newtype_receiver(x: Wrapper, rhs: u8) -> u8 {
        let y = x.add(rhs);
        y.value()
    }
"#;

fn reset_newtype_metadata() {
    clear_chc_fallback_counts();
    let _ = take_translation_drop_by_fn();
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
}

#[test]
fn test_translation_drop_newtype_bare_read_reconstructs_value() {
    with_test_ay_ctx_for_source(NEWTYPE_RECEIVER_SOURCE, |ctx| {
        let fn_name = "probe_newtype_bare_read";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, ChcConfig::default());
        chc_ctx.declare_block_relations();

        let newtype_local = 1usize;
        assert!(
            chc_ctx.flatten.flattened_tuple_locals.contains(&newtype_local),
            "{fn_name} precondition failed: Wrapper local should be flattened"
        );

        let result = chc_ctx.translate_place_with_modified(
            &Place { local: newtype_local, projection: vec![] },
            &HashSet::new(),
        );
        assert!(
            result.is_some(),
            "{fn_name} should reconstruct a bare read of the single-field newtype instead of dropping translation"
        );
    });
}

#[test]
fn test_translation_drop_newtype_receiver_pipeline_has_clean_metadata() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    reset_newtype_metadata();

    with_test_ay_ctx_for_source(NEWTYPE_RECEIVER_SOURCE, |ctx| {
        let fn_name = "probe_newtype_receiver";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());

        assert_vc_structure(&vc, fn_name, body.blocks.len());
        assert_relation_has_arg_sort(&vc, fn_name, |sort| sort.bitvec_width() == Some(8), "bv8");
        assert_has_nontrivial_transition_constraints(&vc, fn_name);
        assert_rule_contains_expr_kind(
            &vc,
            fn_name,
            |expr| matches!(expr.value(), ExprValue::Eq(_, _)),
            "Eq",
        );

        let fallback_count = get_chc_fallback_counts().get(fn_name).copied().unwrap_or(0);
        assert_eq!(
            fallback_count, 0,
            "{fn_name} should avoid CHC fallback while lowering the single-field newtype receiver path"
        );
    });

    let translation_drops = take_translation_drop_by_fn();
    let drop_count = translation_drops.get("probe_newtype_receiver").copied().unwrap_or(0);
    assert_eq!(
        drop_count, 0,
        "probe_newtype_receiver should have zero translation drops, map={translation_drops:?}"
    );

    let translation_sites = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
    assert!(
        !translation_sites.contains_key("probe_newtype_receiver"),
        "probe_newtype_receiver should not record translation-drop site reasons, map={translation_sites:?}"
    );

    reset_newtype_metadata();
}
