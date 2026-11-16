// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Native-MIR ordering and exemption controls for the raw buffer boundary.

use super::common::*;
use super::test_trust_box_new::{mem_config, with_native_box_ctx};
use crate::callee_body::CalleeBody;
use crate::kani_middle::std_abstraction::StdAbstraction;
use crate::kani_middle::transform::inline::{FunctionInlinePass, InlineConfig};

#[test]
fn native_vec_buffer_guard_covers_mutation_before_getter() {
    // This shim preserves an opaque raw-pointer call for the prescan test;
    // it does not test or claim Kani mem-handler semantics. The registered
    // CLI fixture above uses the actual kani::mem function.
    let source = format!(
        "mod kani {{ pub mod mem {{ #[inline(never)] pub fn can_dereference<T>(_: *const T) -> bool {{ true }} }} }}\n{}",
        include_str!("../../../../../tools/soundness-duals/vec_buffer_after_growth_dual.rs")
            .replace("#[kani::proof]", "")
    );
    with_native_box_ctx(&source, |ctx| {
        let abstraction = StdAbstraction::resolve(ctx.tcx);
        for depth in [0, 32] {
            for name in [
                "append_then_getter_read_refusal",
                "append_then_getter_extent_refusal",
                "push_then_getter_read_refusal",
                "index_then_getter_read_refusal",
                "mutation_then_move_then_getter_refusal",
                "mutation_then_aggregate_getter_refusal",
                "mutation_then_projected_move_getter_refusal",
                "mutation_then_owner_reference_getter_refusal",
                "mutation_then_raw_owner_getter_refusal",
                "local_shadow_name_then_getter_refusal",
                "local_shadow_raw_name_then_getter_refusal",
                "unchanged_aggregate_getter_safe",
                "unchanged_aggregate_getter_bug",
                "unchanged_projected_move_getter_safe",
                "unchanged_projected_move_getter_bug",
                "unchanged_getter_safe",
                "unchanged_getter_bug",
                "physical_store_then_fresh_getter_safe",
                "physical_store_then_fresh_getter_bug",
                "clear_then_fresh_getter_keeps_bytes_safe",
            ] {
                let instance = find_instance_by_suffix(ctx.tcx, name);
                let (_, body) = FunctionInlinePass::new(InlineConfig {
                    max_depth: depth,
                    chc_native_box_drop: true,
                    ..InlineConfig::default()
                })
                .transform_with_body_provider(
                    ctx.tcx,
                    instance.callee_body().unwrap(),
                    instance,
                    |callee| {
                        // Keep the opaque-call boundary at both depths.
                        if abstraction.abstracts_public_instance(ctx.tcx, callee)
                            || callee.name().contains("can_dereference")
                        {
                            None
                        } else {
                            callee.callee_body()
                        }
                    },
                );
                let context = ChcCtx::new(ctx.tcx, &body, name, mem_config());
                if name.ends_with("refusal") {
                    let (vc, _, _) = context.translate_with_diagnostics();
                    assert!(
                        !vc.approximation_identity_complete,
                        "raw buffer uncertainty must retain its refusal: {name} depth={depth}"
                    );
                } else {
                    // Positive controls check this prescan's exemptions only;
                    // the registered CLI rows keep strict semantic oracles.
                    context.book_vec_buffer_access_after_mutation();
                }
                let reasons = crate::codegen_ay::take_translation_drop_site_reasons_by_fn()
                    .remove(name)
                    .unwrap_or_default();
                let refused =
                    reasons.get("vec_buffer_access_after_mutation").copied().unwrap_or(0) > 0;
                assert_eq!(refused, name.ends_with("refusal"), "{name} depth={depth}: {reasons:?}");
            }
        }
    });
}
