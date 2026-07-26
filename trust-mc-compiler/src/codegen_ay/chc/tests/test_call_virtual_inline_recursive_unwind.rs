// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::super::common::*;

const RECURSIVE_SUM_PROBE: &str = r#"
    #![allow(dead_code)]

    pub fn recursive_sum(n: u32) -> u32 {
        if n == 0 {
            0
        } else {
            n + recursive_sum(n - 1)
        }
    }
"#;

/// Part of #4058 D4: With `unwinding_assertions: false` (default over-approx),
/// recursive exhaustion emits `__recursive_unwind_exhausted`.
#[test]
fn test_recursive_inline_exhaustion_overapprox() {
    with_test_ay_ctx_for_source(RECURSIVE_SUM_PROBE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "recursive_sum");
        let body = instance.body().expect("function body");
        let cfg = ChcConfig {
            recursive_unwind_depth: 2,
            unwinding_assertions: false,
            ..ChcConfig::default()
        };
        let vc = mir_to_chc_with_instance(ctx.tcx, &body, instance, "recursive_sum", cfg);

        assert!(!vc.rules.is_empty(), "recursive_sum should produce rules");
        assert!(
            any_constraint_str(&vc, |s| s.contains("__recursive_unwind_exhausted")),
            "unwinding_assertions=false should use the over-approximation exhaustion path"
        );
        assert!(
            !any_constraint_str(&vc, |s| s.contains("__assert_fail_inline_recursive_unwind")),
            "unwinding_assertions=false must NOT emit an inline assert guard"
        );
    });
}

/// Part of #4058 D4: With `unwinding_assertions: true` (fail-closed),
/// recursive exhaustion emits `__assert_fail_inline_recursive_unwind`.
#[test]
fn test_recursive_inline_exhaustion_unwinding_assertion() {
    with_test_ay_ctx_for_source(RECURSIVE_SUM_PROBE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "recursive_sum");
        let body = instance.body().expect("function body");
        let cfg = ChcConfig {
            recursive_unwind_depth: 2,
            unwinding_assertions: true,
            ..ChcConfig::default()
        };
        let vc = mir_to_chc_with_instance(ctx.tcx, &body, instance, "recursive_sum", cfg);

        assert!(!vc.rules.is_empty(), "recursive_sum should produce rules");
        assert!(
            any_constraint_str(&vc, |s| s.contains("__assert_fail_inline_recursive_unwind")),
            "unwinding_assertions=true should emit an inline assert guard for recursive exhaustion"
        );
        assert!(
            !any_constraint_str(&vc, |s| s.contains("__recursive_unwind_exhausted")),
            "unwinding_assertions=true must NOT use the over-approximation path"
        );
    });
}
