// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Test code: unwrap is acceptable for assertions
#![allow(clippy::unwrap_used)]

use super::common::*;

#[test]
fn test_mut_projected_ref_requests_mem_promote() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_mut_projected_ref() {
            let mut arr = [1u8, 2u8];
            let r = &mut arr[0];
            *r = 3u8;
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_mut_projected_ref");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_mut_projected_ref", ChcConfig::default());
        let (_vc, action) = chc_ctx.translate();
        assert_eq!(
            action,
            super::super::MemPromoteAction::Promote,
            "mutable projected Ref/AddressOf should request mem-track promotion at Reg level"
        );
    });
}

#[test]
fn test_shared_projected_ref_stays_reg_level() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_shared_projected_ref() -> u8 {
            let arr = [7u8, 9u8];
            let r = &arr[0];
            *r
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_shared_projected_ref");
        let body = instance.body().expect("function body");

        let chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_shared_projected_ref", ChcConfig::default());
        let (_vc, action) = chc_ctx.translate();
        // Index projections (e.g., &arr[0]) cannot be handled by
        // extract_field_projections at Reg level — #2876 correctly
        // routes them through Mem-level addressing.
        assert_eq!(
            action,
            super::super::MemPromoteAction::Promote,
            "shared projected Ref with Index projection should request mem promotion \
             (extract_field_projections cannot handle Index projections)"
        );
    });
}

#[test]
fn test_shared_projected_ref_mem_promote_stays_off_demoted_fallback() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_shared_projected_ref_fallback_budget() -> *const u8 {
            let arr = [7u8, 9u8];
            let r = &arr[0];
            r
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance =
            find_instance_by_suffix(ctx.tcx, "probe_shared_projected_ref_fallback_budget");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_shared_projected_ref_fallback_budget",
            ChcConfig::default(),
        );
        let (_vc, action, diagnostics) = chc_ctx.translate_with_diagnostics();

        assert_eq!(
            action,
            super::super::MemPromoteAction::Promote,
            "shared projected Ref with Index projection should still request mem promotion"
        );
        assert_eq!(
            diagnostics.fallback_count.get(),
            0,
            "the discarded Reg-level pass should not count projected shared Ref promotion as a demoted fallback"
        );
    });
}

#[test]
fn test_box_deref_store_requests_mem_promote() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_box_deref_store() {
            let mut boxed = Box::new([1u32, 2u32, 3u32]);
            *boxed = [4u32, 5u32, 6u32];
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_box_deref_store");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_box_deref_store", ChcConfig::default());
        let (_vc, action) = chc_ctx.translate();
        assert_eq!(
            action,
            super::super::MemPromoteAction::Promote,
            "boxed deref stores should request mem-track promotion at Reg level"
        );
    });
}
