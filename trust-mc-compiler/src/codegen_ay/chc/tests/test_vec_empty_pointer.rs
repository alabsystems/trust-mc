// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::common::*;
use super::test_trust_box_new::{mem_config, with_native_box_ctx};
use crate::callee_body::CalleeBody;

#[test]
fn native_empty_vec_uses_actual_alignment_and_retains_invalid_provenance() {
    let source = include_str!("../../../../../tools/soundness-duals/vec_empty_dangling_dual.rs")
        .replace("#[kani::proof]", "");
    with_native_box_ctx(&source, |ctx| {
        for extra in [false, true] {
            for name in [
                "empty_u8_address_safe",
                "empty_u8_address_bug",
                "empty_u64_address_safe",
                "empty_u64_address_bug",
                "empty_actual_layout_safe",
                "empty_actual_layout_bug",
                "zero_capacity_address_safe",
                "zero_capacity_dereference_bug",
                "empty_dereference_bug",
            ] {
                let body = find_instance_by_suffix(ctx.tcx, name).callee_body().unwrap();
                let config = ChcConfig { extra_pointer_checks: extra, ..mem_config() };
                let (mut vc, _, diagnostics) =
                    ChcCtx::new(ctx.tcx, &body, name, config).translate_with_diagnostics();
                let reasons = crate::codegen_ay::take_translation_drop_site_reasons_by_fn()
                    .remove(name)
                    .unwrap_or_default();
                let disabled =
                    crate::codegen_ay::context::chc_requires_unreduced_obligations(&vc, false);
                crate::codegen_ay::context::run_emit_time_chc_passes(&mut vc, disabled);
                let smt = crate::codegen_ay::emit_chc(&vc).to_string();
                let verdict = run_z3_on_smt2_with_timeout(&smt, 30);
                let expected = if name.ends_with("safe") { "unsat" } else { "sat" };
                eprintln!(
                    "EMPTY {name} extra={extra} guard={disabled} {verdict:?} reasons={reasons:?}"
                );
                if verdict.as_deref() != Ok(expected)
                    || !reasons.is_empty()
                    || diagnostics.place_translation_drop.get() != 0
                {
                    if let Some(dir) = std::env::var_os("MC_VEC_APPEND_ARTIFACT_DIR") {
                        let dir = std::path::Path::new(&dir);
                        std::fs::write(dir.join(format!("{extra}-{name}.smt2")), &smt).unwrap();
                        std::fs::write(
                            dir.join(format!("{extra}-{name}.mir")),
                            format!("{body:#?}"),
                        )
                        .unwrap();
                    }
                }
                assert_eq!(
                    verdict.as_deref(),
                    Ok(expected),
                    "{name} extra={extra}, guard={disabled}, reasons={reasons:?}"
                );
                assert!(reasons.is_empty(), "{name} extra={extra}: {reasons:?}");
                assert_eq!(diagnostics.place_translation_drop.get(), 0);
            }
        }
    });
}
