// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Regression tests for #3967: closure alias-update writeback for tuple args.
//!
//! Confirms that direct closure dispatch writes back all returned alias updates,
//! including tuple args beyond local1 and combined env + tuple updates.

#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;

const CLOSURE_SECOND_ARG_WRITEBACK_PROBE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_closure_second_arg_writeback() {
        let mut x = 1i32;
        let mut y = 2i32;
        let f = |_a: &mut i32, b: &mut i32| {
            *b = 7;
        };
        f(&mut x, &mut y);
        assert!(x == 1);
        assert!(y == 7);
    }
"#;

const CLOSURE_ENV_AND_SECOND_ARG_WRITEBACK_PROBE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_closure_env_and_second_arg_writeback() {
        let mut x = 1i32;
        let mut y1 = 2i32;
        let mut y2 = 3i32;
        let mut counter = 10i32;
        let mut f = |_a: &mut i32, b: &mut i32| {
            counter += 1;
            *b = 7;
            counter
        };
        let first = f(&mut x, &mut y1);
        let second = f(&mut x, &mut y2);
        assert!(first == 11);
        assert!(second == 12);
        assert!(y1 == 7);
        assert!(y2 == 7);
    }
"#;

fn assert_closure_alias_update_probe(source: &str, fn_name: &str) {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    clear_chc_fallback_counts();

    with_test_ay_ctx_for_source(source, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());

        assert!(!vc.relations.is_empty(), "should produce relations");
        assert!(!vc.rules.is_empty(), "should produce rules");
        assert!(
            !vc_error_rules_contain_var(&vc, "__assert_fail_inline"),
            "{fn_name} should not produce __assert_fail_inline fallback"
        );
    });
}

#[test]
fn test_closure_second_arg_writeback_produces_vc() {
    assert_closure_alias_update_probe(
        CLOSURE_SECOND_ARG_WRITEBACK_PROBE,
        "probe_closure_second_arg_writeback",
    );
}

#[test]
fn test_closure_env_and_second_arg_writeback_produces_vc() {
    assert_closure_alias_update_probe(
        CLOSURE_ENV_AND_SECOND_ARG_WRITEBACK_PROBE,
        "probe_closure_env_and_second_arg_writeback",
    );
}
