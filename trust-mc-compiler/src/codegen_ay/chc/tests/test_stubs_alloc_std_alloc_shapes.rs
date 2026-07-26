// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! MIR-backed std::alloc shape localizers split from test_stubs_alloc.rs so the
//! alloc pipeline probes stay discoverable without growing the main alloc-stub
//! module further.
//!
//! Part of #4049.

#![allow(clippy::unwrap_used)]

use super::common::*;

fn assert_std_alloc_alloc_array_roundtrip_retains_literals(vc: &trust_mc_core::chc::ChcVc) {
    let smt = crate::codegen_ay::emit_chc(vc).to_string();
    for literal in ["#x00000000", "#x0000000a", "#x00000014", "#x0000001e"] {
        assert!(
            any_constraint_str(vc, |constraint| {
                constraint.contains("store") && constraint.contains(literal)
            }),
            "std_alloc alloc-array roundtrip should retain literal store {literal} in the VC"
        );
        assert!(
            smt.contains(literal),
            "std_alloc alloc-array roundtrip should retain literal store {literal} through CHC emission"
        );
    }
}

#[test]
fn test_mir_std_alloc_alloc_array_roundtrip_has_no_chc_fallbacks() {
    // Exact MIR-backed localizer for tests/ay/std_alloc.rs::test_alloc_array.
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub unsafe fn probe_std_alloc_alloc_array_roundtrip() {
            let layout = std::alloc::Layout::array::<i32>(4).unwrap();
            let ptr = unsafe { std::alloc::alloc(layout) } as *mut i32;
            assert!(!ptr.is_null());

            unsafe { ptr.add(0).write(0) };
            unsafe { ptr.add(1).write(10) };
            unsafe { ptr.add(2).write(20) };
            unsafe { ptr.add(3).write(30) };

            assert!(unsafe { ptr.add(0).read() } == 0);
            assert!(unsafe { ptr.add(1).read() } == 10);
            assert!(unsafe { ptr.add(2).read() } == 20);
            assert!(unsafe { ptr.add(3).read() } == 30);

            unsafe { std::alloc::dealloc(ptr as *mut u8, layout) };
        }
    "#;

    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    clear_chc_fallback_counts();
    let _ = take_translation_drop_by_fn();

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let name = "probe_std_alloc_alloc_array_roundtrip";
        let instance = find_instance_by_suffix(ctx.tcx, name);
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            name,
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        assert_vc_structure(&vc, name, body.blocks.len());
        assert!(vc_rules_contain_var(&vc, "obj_valid__out"), "should update obj_valid__out");
        assert!(vc_rules_contain_var(&vc, "obj_size__out"), "should constrain obj_size__out");
        assert!(
            vc_rules_contain_var(&vc, "_probe_std_alloc_alloc_array_roundtrip_mem_i32__out"),
            "should constrain the i32 heap output array"
        );
        assert_std_alloc_alloc_array_roundtrip_retains_literals(&vc);

        let fallback_count = get_chc_fallback_counts().get(name).copied().unwrap_or(0);
        assert_eq!(
            fallback_count, 0,
            "alloc-array roundtrip should not increment CHC fallback count, got {fallback_count}"
        );

        let translation_drops = take_translation_drop_by_fn();
        let translation_drop_count = translation_drops.get(name).copied().unwrap_or(0);
        assert!(
            translation_drop_count <= 2,
            "alloc-array roundtrip should have at most 2 translation-drops, got {translation_drop_count}, map={translation_drops:?}"
        );
    });

    clear_chc_fallback_counts();
    let _ = take_translation_drop_by_fn();
}

#[test]
fn test_translate_rust_alloc_emits_explicit_alignment_constraint() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        use std::alloc::{alloc, Layout};

        pub unsafe fn probe_alloc_call() -> *mut u8 {
            let layout = Layout::from_size_align(16, 8).unwrap();
            unsafe { alloc(layout) }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_alloc_call");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_alloc_call",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        assert!(
            any_constraint_str(&vc, |constraint| {
                constraint.contains("bvurem") && constraint.contains("#x0000000000000008")
            }),
            "full MIR translation should make the base pointer alignment explicit for checked Layout::from_size_align(16, 8)"
        );
    });
}
