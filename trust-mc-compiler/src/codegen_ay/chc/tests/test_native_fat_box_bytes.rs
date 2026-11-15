// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Native physical bytes are distinct from a logical dyn metadata sidecar.

use super::common::*;
use super::test_native_fat_box::SOURCE;
use crate::callee_body::CalleeBody;

#[test]
fn native_fat_box_data_word_is_not_a_zero_padded_native_pointer_image() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        for name in [
            "raw_words_safe",
            "raw_words_bug",
            "transmute_words_safe",
            "transmute_words_bug",
            "transmute_inline_safe",
            "transmute_inline_bug",
        ] {
            let body = find_instance_by_suffix(ctx.tcx, name).callee_body().unwrap();
            let chc = ChcCtx::new(
                ctx.tcx,
                &body,
                name,
                ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
            );
            let (vc, _, diagnostics) = chc.translate_with_diagnostics();
            let smt = crate::codegen_ay::emit_chc(&vc).to_string();
            let result = run_z3_on_smt2_with_timeout(&smt, 30);
            let reasons = crate::codegen_ay::take_translation_drop_site_reasons_by_fn()
                .remove(name)
                .unwrap_or_default();
            eprintln!(
                "FAT_BOX_BYTES {name}: {result:?}; fail_closed={}; reasons={reasons:?}",
                diagnostics.place_translation_drop.get()
            );
            if name.ends_with("bug") {
                assert!(
                    result.as_deref() != Ok("unsat")
                        || diagnostics.place_translation_drop.get() > 0,
                    "the native Box data and vtable words are both non-null; logical padding cannot prove this bug"
                );
            }
        }
    });
}
