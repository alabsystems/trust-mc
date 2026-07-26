// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Regression tests for generic mem intrinsic fallback paths in
//! `stubs_util_intrinsics.rs`.
//!
//! Part of #2783: ensure generic `size_of::<T>` / `align_of::<T>` paths call
//! `record_fallback()` when `T` is unresolved at this translation stage.

#![allow(clippy::unwrap_used)]

use super::common::*;

fn find_local_item_by_suffix(tcx: TyCtxt<'_>, suffix: &str) -> rustc_public::CrateItem {
    let matches: Vec<_> = rustc_public::all_local_items()
        .into_iter()
        .filter(|item| {
            let def_id = rustc_public::rustc_internal::internal(tcx, item.def_id());
            let path = tcx.def_path_str(def_id);
            path == suffix || path.ends_with(&format!("::{suffix}"))
        })
        .collect();

    assert!(!matches.is_empty(), "missing item with suffix '{suffix}' in local crate");
    assert_eq!(matches.len(), 1, "ambiguous suffix '{suffix}' ({} matches)", matches.len());
    matches[0]
}

#[test]
fn test_generic_size_of_intrinsic_increments_sound_fallback_counter() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_size_of_generic<T>(_value: T) -> usize {
            core::mem::size_of::<T>()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let item = find_local_item_by_suffix(ctx.tcx, "probe_size_of_generic");
        let body = item.body().expect("generic function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_size_of_generic", ChcConfig::default());

        let mut saw_call = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && chc_ctx.detect_stub_matching(func, StubKind::is_mem_intrinsic)
                    == Some(StubKind::MemSizeOf)
            {
                saw_call = true;
                let before = chc_ctx.sound_fallback_count();
                let result = chc_ctx.translate_mem_intrinsic_call(StubKind::MemSizeOf, func);
                let after = chc_ctx.sound_fallback_count();

                assert!(
                    result.is_none(),
                    "generic size_of::<T> should fail closed when type is unresolved"
                );
                assert!(
                    after > before,
                    "generic size_of::<T> fallback should increment sound_fallback_count() \
                     (before={before}, after={after})"
                );
            }
        }

        assert_mir_pattern_found(saw_call, "generic mem::size_of call in MIR");
    });
}

#[test]
fn test_generic_align_of_intrinsic_increments_sound_fallback_counter() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_align_of_generic<T>(_value: T) -> usize {
            core::mem::align_of::<T>()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let item = find_local_item_by_suffix(ctx.tcx, "probe_align_of_generic");
        let body = item.body().expect("generic function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_align_of_generic", ChcConfig::default());

        let mut saw_call = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && chc_ctx.detect_stub_matching(func, StubKind::is_mem_intrinsic)
                    == Some(StubKind::MemAlignOf)
            {
                saw_call = true;
                let before = chc_ctx.sound_fallback_count();
                let result = chc_ctx.translate_mem_intrinsic_call(StubKind::MemAlignOf, func);
                let after = chc_ctx.sound_fallback_count();

                assert!(
                    result.is_none(),
                    "generic align_of::<T> should fail closed when type is unresolved"
                );
                assert!(
                    after > before,
                    "generic align_of::<T> fallback should increment sound_fallback_count() \
                     (before={before}, after={after})"
                );
            }
        }

        assert_mir_pattern_found(saw_call, "generic mem::align_of call in MIR");
    });
}
