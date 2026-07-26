// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Regression tests for derived enum `PartialEq` dispatch and proof.
//!
//! Part of #3994: `niche_many_variants` must keep derived enum `PartialEq`
//! on a precise comparison path for borrowed operands without introducing
//! CHC fallback counters.

#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use crate::codegen_ay::emit_chc;
use rustc_public::mir::TerminatorKind;

const ENUM_PARTIAL_EQ_PROBE: &str = r#"
    #![allow(dead_code)]

    #[derive(Debug, PartialEq)]
    enum MyEnum {
        NoFields,
        DataFul(bool),
        UnitFields((), ()),
        ZSTField(ZeroSized),
        ZSTStruct { field: ZeroSized, unit: () },
    }

    #[derive(Debug, PartialEq)]
    struct ZeroSized {}

    impl ZeroSized {
        fn works(&self) -> bool {
            true
        }
    }

    impl MyEnum {
        fn create_unit() -> MyEnum {
            MyEnum::UnitFields((), ())
        }

        fn create_zst_field() -> MyEnum {
            MyEnum::ZSTField(ZeroSized {})
        }
    }

    pub fn check_niche_unit_fields() {
        let x = MyEnum::create_unit();
        assert_eq!(x, MyEnum::UnitFields((), ()));
        if let MyEnum::UnitFields(v, ..) = &x {
            assert_eq!(std::mem::size_of_val(v), 0);
        }
    }

    pub fn check_niche_zst_field() {
        let x = MyEnum::create_zst_field();
        assert_eq!(x, MyEnum::ZSTField(ZeroSized {}));
        if let MyEnum::ZSTField(field) = &x {
            assert!(field.works());
        }
    }
"#;

const PROBE_FN_NAMES: [&str; 2] = ["check_niche_unit_fields", "check_niche_zst_field"];

fn reset_enum_partial_eq_counters() {
    clear_chc_fallback_counts();
    let _ = take_translation_drop_by_fn();
    let _ = crate::codegen_ay::take_unhandled_call_by_fn();
}

#[test]
fn test_enum_partial_eq_call_is_detected_as_primitive_cmp_stub() {
    with_test_ay_ctx_for_source(ENUM_PARTIAL_EQ_PROBE, |ctx| {
        for fn_name in PROBE_FN_NAMES {
            let instance = find_instance_by_suffix(ctx.tcx, fn_name);
            let body = instance.body().expect("function body");
            let chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, ChcConfig::default());

            let primitive_cmp_paths: Vec<_> = body
                .blocks
                .iter()
                .filter_map(|block| match &block.terminator.kind {
                    TerminatorKind::Call { func, .. }
                        if chc_ctx
                            .detect_stub_matching(func, StubKind::is_primitive_cmp)
                            .is_some() =>
                    {
                        chc_ctx.resolve_callee_path(func)
                    }
                    _ => None,
                })
                .collect();

            assert_eq!(
                primitive_cmp_paths,
                vec!["<MyEnum as std::cmp::PartialEq>::eq".to_string()],
                "{fn_name} should route derived enum PartialEq through PrimitivePartialEqEq, paths={primitive_cmp_paths:?}"
            );
        }
    });
}

#[test]
fn test_enum_partial_eq_literal_assert_eq_proves_without_fallbacks() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    reset_enum_partial_eq_counters();

    with_test_ay_ctx_for_source(ENUM_PARTIAL_EQ_PROBE, |ctx| {
        for fn_name in PROBE_FN_NAMES {
            let instance = find_instance_by_suffix(ctx.tcx, fn_name);
            let body = instance.body().expect("function body");
            let (vc, _, diagnostics) = ChcCtx::new(ctx.tcx, &body, fn_name, ChcConfig::default())
                .translate_with_diagnostics();

            assert_vc_structure(&vc, fn_name, body.blocks.len());
            assert!(has_any_constraints(&vc), "{fn_name} should constrain the VC");
            assert_eq!(
                diagnostics.fallback_count.get(),
                0,
                "{fn_name} should not require sound fallback"
            );
            // Part of #4037: after the multi-variant Datatype constant encoding
            // fix, promoted enum literals now produce Datatype expressions that
            // match the reconstructed live variable. No translation drops expected.
            assert_eq!(
                diagnostics.place_translation_drop.get(),
                0,
                "{fn_name} unexpected place_translation_drop={} (expected 0 after #4037 fix)",
                diagnostics.place_translation_drop.get()
            );

            let smt = emit_chc(&vc).to_string();
            assert_z3_result(&smt, "unsat");
        }
    });

    let fallback_counts = get_chc_fallback_counts();
    let translation_drops = take_translation_drop_by_fn();
    let unhandled_calls = crate::codegen_ay::take_unhandled_call_by_fn();

    for fn_name in PROBE_FN_NAMES {
        let fallback_count = fallback_counts.get(fn_name).copied().unwrap_or(0);
        assert_eq!(
            fallback_count, 0,
            "{fn_name} should keep enum PartialEq on the precise path, fallback map={fallback_counts:?}"
        );

        let drop_count = translation_drops.get(fn_name).copied().unwrap_or(0);
        // ZST struct fields (e.g., ZeroSized{}) now translate cleanly via
        // Datatype structural equality — no translation drops for ZST
        // field comparisons. Previous tolerance of 1 drop for
        // check_niche_zst_field was a stale workaround.
        assert_eq!(
            drop_count, 0,
            "{fn_name} unexpected place-translation drops={drop_count} (expected 0), drops={translation_drops:?}"
        );

        let unhandled_count = unhandled_calls.get(fn_name).copied().unwrap_or(0);
        assert_eq!(
            unhandled_count, 0,
            "{fn_name} should not increment unhandled-call counters, map={unhandled_calls:?}"
        );
    }
}
