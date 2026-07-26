// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Regression tests for `RangeBounds::contains` call dispatch.
//!
//! Part of #3930: `char::any()` uses `(0xE000..=0x10FFFF).contains(&val)` to
//! guard Unicode scalar values. CHC already has a precise range-contains
//! lowering, but the generic overapprox dispatcher used to intercept the call
//! first and force a `true` result, incrementing `kani_mem_overapprox`.

#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;

fn mir_to_chc_default(
    tcx: TyCtxt<'_>,
    body: &rustc_public::mir::Body,
    fn_name: &str,
) -> trust_mc_core::chc::ChcVc {
    crate::codegen_ay::chc::mir_to_chc(
        tcx,
        body,
        fn_name,
        crate::codegen_ay::chc::ChcConfig::default(),
    )
}

const RANGE_INCLUSIVE_CONTAINS_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_range_inclusive_contains(item: u32) -> bool {
        (0xE000..=0x10FFFF).contains(&item)
    }
"#;

#[test]
fn test_range_inclusive_contains_uses_precise_dispatch() {
    with_test_ay_ctx_for_source(RANGE_INCLUSIVE_CONTAINS_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_range_inclusive_contains");
        let body = instance.body().expect("function body");

        let _ = crate::codegen_ay::take_kani_mem_overapprox_count();
        let vc = mir_to_chc_default(ctx.tcx, &body, "probe_range_inclusive_contains");

        assert_vc_structure(&vc, "probe_range_inclusive_contains", body.blocks.len());
        assert_eq!(
            crate::codegen_ay::take_kani_mem_overapprox_count(),
            0,
            "RangeInclusive::contains should use precise CHC lowering, not kani_mem_overapprox",
        );
        assert!(
            any_constraint_str(&vc, |c| {
                c.contains("0000e000")
                    && c.contains("0010ffff")
                    && (c.contains("bvule") || c.contains("bvsle"))
            }),
            "RangeInclusive::contains should emit explicit bound comparisons"
        );
    });
}

const CHAR_ANY_GUARD_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![feature(register_tool)]
    #![register_tool(kanitool)]

    mod kani {
        #[kanitool::fn_marker = "AnyRawHook"]
        fn any_raw<T: Copy>() -> T {
            panic!("model-only marker function")
        }

        pub unsafe fn any_raw_internal<T: Copy>() -> T {
            any_raw::<T>()
        }

        #[kanitool::fn_marker = "AssumeHook"]
        pub fn assume(_cond: bool) {}
    }

    pub fn probe_char_any_guard() -> u32 {
        let val = unsafe { kani::any_raw_internal::<u32>() };
        kani::assume(val <= 0xD7FF || (0xE000..=0x10FFFF).contains(&val));
        val
    }
"#;

#[test]
fn test_char_any_guard_avoids_range_contains_demote() {
    with_test_ay_ctx_for_source(CHAR_ANY_GUARD_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_char_any_guard");
        let body = instance.body().expect("function body");

        let _ = crate::codegen_ay::take_kani_mem_overapprox_count();
        let vc = mir_to_chc_default(ctx.tcx, &body, "probe_char_any_guard");

        assert_vc_structure(&vc, "probe_char_any_guard", body.blocks.len());
        assert_eq!(
            crate::codegen_ay::take_kani_mem_overapprox_count(),
            0,
            "char::any()-style RangeInclusive::contains guard should not increment kani_mem_overapprox",
        );
        // The short-circuit `||` in `val <= 0xD7FF || (range).contains(&val)`
        // splits the bounds across basic blocks/rules, so check each bound
        // individually rather than requiring all three in one constraint.
        assert!(
            any_constraint_str(&vc, |c| c.contains("0000d7ff")),
            "char::any()-style guard should retain 0xD7FF upper bound",
        );
        assert!(
            any_constraint_str(&vc, |c| c.contains("0000e000")),
            "char::any()-style guard should retain 0xE000 range start",
        );
        assert!(
            any_constraint_str(&vc, |c| c.contains("0010ffff")),
            "char::any()-style guard should retain 0x10FFFF range end",
        );
    });
}
