// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Regression tests for #3936: inline alias-update map for caller-visible
//! arg writes. Verifies that when an inlined function mutates its second
//! (or later) `&mut` argument, the caller sees the update.
//!
//! Part of #3936 D6.

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;

/// Probe: a function that only writes through its second `&mut` argument.
/// After inlining, the caller must see `y == 7` (not the original `y == 2`).
const SECOND_ARG_WRITEBACK_PROBE: &str = r#"
    #![allow(dead_code)]

    fn overwrite_second(_x: &mut i32, y: &mut i32) {
        *y = 7;
    }

    pub fn probe_second_arg_writeback() {
        let mut x = 1i32;
        let mut y = 2i32;
        overwrite_second(&mut x, &mut y);
        assert!(x == 1);
        assert!(y == 7);
    }
"#;

#[test]
fn test_second_arg_writeback_produces_vc() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    clear_chc_fallback_counts();

    with_test_ay_ctx_for_source(SECOND_ARG_WRITEBACK_PROBE, |ctx| {
        let fn_name = "probe_second_arg_writeback";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());

        assert!(!vc.relations.is_empty(), "should produce relations");
        assert!(!vc.rules.is_empty(), "should produce rules");

        // The assertions should NOT trigger the __assert_fail_inline fallback.
        // If they do, the inline body translation could not resolve the second
        // arg update and fell back to nondeterministic values.
        assert!(
            !vc_error_rules_contain_var(&vc, "__assert_fail_inline"),
            "second-arg writeback should not produce __assert_fail_inline fallback"
        );
    });
}
