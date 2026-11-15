// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Regression tests for inline `Intrinsic(Assume)` across `SwitchInt`.

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
mod test_call_virtual_inline_assume_switchint_contracts;

use crate::codegen_ay::chc::call::inline_body::translate_inline_body;
use ay_bindings::{Expr, ExprValue};
use rustc_public::mir::{StatementKind, TerminatorKind};
use std::collections::HashMap;

const INTRINSIC_ASSUME_SWITCHINT_INLINE_PROBE: &str = r#"
    #![allow(dead_code)]
    #![allow(internal_features)]
    #![feature(core_intrinsics)]

    pub fn probe_inline_intrinsic_assume_switch(flag: bool) -> u8 {
        unsafe { core::intrinsics::assume(flag); }
        if flag { 1 } else { 2 }
    }
"#;

#[test]
fn test_inline_intrinsic_assume_is_checked_across_switchint_translation() {
    with_test_ay_ctx_for_source(INTRINSIC_ASSUME_SWITCHINT_INLINE_PROBE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_inline_intrinsic_assume_switch");
        let body = instance.body().expect("function body");
        assert!(
            body.blocks.iter().any(|bb| {
                bb.statements.iter().any(|stmt| {
                    matches!(
                        stmt.kind,
                        StatementKind::Intrinsic(rustc_public::mir::NonDivergingIntrinsic::Assume(
                            _
                        ))
                    )
                })
            }),
            "probe must contain an Intrinsic::Assume statement"
        );
        assert!(
            body.blocks
                .iter()
                .any(|bb| matches!(bb.terminator.kind, TerminatorKind::SwitchInt { .. })),
            "probe must contain a SwitchInt terminator"
        );

        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_inline_intrinsic_assume_switch",
            ChcConfig::default(),
        );
        chc_ctx.declare_block_relations();

        let params = vec![Expr::bool_const(false)];
        chc_ctx.mark_inline_field_reads(&body, &params, 0);
        let inline_result = translate_inline_body(
            &mut chc_ctx,
            &body,
            &params,
            0,
            &HashMap::new(),
            Some(instance),
            0,
        )
        .expect("inline body should translate");

        // `intrinsics::assume(P)` is CHECKED, as Kani ("Rust intrinsic assumption
        // failed"), not assumed: the walk records a deferred check and keeps
        // translating across the SwitchInt instead of pruning the return value.
        let assume_checks: Vec<_> = inline_result
            .deferred_checks
            .iter()
            .filter(|c| c.message.as_deref() == Some("Rust intrinsic assumption failed"))
            .collect();
        assert_eq!(assume_checks.len(), 1, "one assume check");
        assert!(
            assume_checks[0].kind == trust_mc_core::violation::PropertyKind::Assumption,
            "assume check has Kani's class `assume`"
        );
        assert!(
            !constraint_tree_contains(&inline_result.value, &|expr| {
                matches!(expr.value(), ExprValue::Var { name } if name.contains("__assume_pruned_inline"))
            }),
            "a checked intrinsic assume does not prune the returned value, got {:?}",
            inline_result.value
        );
    });
}
