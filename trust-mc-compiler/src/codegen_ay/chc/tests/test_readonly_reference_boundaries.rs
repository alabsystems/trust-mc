// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::common::*;
use crate::callee_body::CalleeBody;
use crate::codegen_ay::chc::codegen_ctx::{FallbackSoundness, fallback_soundness};

#[test]
fn projected_readonly_borrows_keep_rust_polarity_or_fail_closed() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
    let source =
        include_str!("../../../../../tools/soundness-duals/readonly_projected_reference_dual.rs")
            .replace("#[kani::proof]", "");
    with_test_ay_ctx_for_source(&source, |ctx| {
        let mut clean_wrong_models = Vec::new();
        for name in [
            "value_safe",
            "value_bug",
            "borrow_safe",
            "borrow_bug",
            "tuple_safe",
            "tuple_bug",
            "capture_safe",
            "capture_bug",
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
                "READONLY_REVIEW {name}: {result:?}; drop={}; reasons={reasons:?}",
                diagnostics.place_translation_drop.get()
            );
            let expected = if name.ends_with("safe") { "unsat" } else { "sat" };
            assert!(result.is_ok(), "{name}: solver failed: {result:?}");
            if result.as_deref() != Ok(expected)
                && !(diagnostics.place_translation_drop.get() > 0
                    && reasons
                        .keys()
                        .any(|reason| fallback_soundness(reason) == FallbackSoundness::FailClose))
            {
                let helper = if name.starts_with("value_") {
                    "by_value"
                } else if name.starts_with("borrow_") {
                    "by_borrow"
                } else if name.starts_with("tuple_") {
                    "by_tuple"
                } else {
                    "by_capture"
                };
                let helper_body = find_instance_by_suffix(ctx.tcx, helper).callee_body().unwrap();
                eprintln!("{name} helper MIR: {helper_body:#?}");
                clean_wrong_models.push(name);
            }
        }
        assert!(
            clean_wrong_models.is_empty(),
            "wrong readonly source models: {clean_wrong_models:?}"
        );
    });
}
