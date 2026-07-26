// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Focused semantic regression for the live `probe_zst_first` residual.
//!
//! Part of #4113: keep the exact `[(); 10]::first()` + `Some(&())` proof shape
//! in a small dedicated unit so failures expose SMT directly.

#![allow(clippy::unwrap_used)]

use super::common::*;
use crate::codegen_ay::emit_chc;

const ZST_SLICE_FIRST_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_zst_first_semantics(zst_array: [(); 10]) {
        assert_eq!(zst_array.len(), 10);
        assert_eq!(zst_array.first(), Some(&()));
    }
"#;

#[test]
fn test_zst_slice_first_semantics_proves_without_fallback() {
    with_test_ay_ctx_for_source(ZST_SLICE_FIRST_SOURCE, |ctx| {
        let fn_name = "probe_zst_first_semantics";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, ChcConfig::default());
        let (vc, _, diagnostics) = chc_ctx.translate_with_diagnostics();

        assert_vc_structure(&vc, fn_name, body.blocks.len());
        assert!(has_any_constraints(&vc), "{fn_name} should constrain the VC");
        assert_eq!(
            diagnostics.fallback_count.get(),
            0,
            "{fn_name} should stay on the precise slice::first path without demoted fallback"
        );
        assert!(
            diagnostics.sound_fallback_detail.is_empty(),
            "{fn_name} should not record categorized sound-fallback details: {:?}",
            diagnostics.sound_fallback_detail
        );
        assert_eq!(
            diagnostics.inferable_predicate.get(),
            0,
            "{fn_name} should not require inferable predicates"
        );

        let smt = emit_chc(&vc).to_string();
        assert_z3_result(&smt, "unsat");
    });
}
