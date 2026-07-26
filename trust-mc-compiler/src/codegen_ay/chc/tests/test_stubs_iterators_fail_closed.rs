// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Focused fail-closed regressions for iterator stubs.
//! Part of #2497 Batch 5 fallback hardening.

#![allow(clippy::unwrap_used)]

use std::collections::HashSet;

use super::common::*;

/// CheckedAddUnsigned non-bitvec/int operands use deterministic zero fallback.
#[test]
fn test_translate_checked_add_unsigned_non_bitvec_operands_use_zero_fallback() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_checked_add_unsigned_bool_arg(a: i32, b: u32, flag: bool) -> Option<i32> {
            if flag {
                a.checked_add_unsigned(b)
            } else {
                a.checked_add_unsigned(b)
            }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_checked_add_unsigned_bool_arg");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_checked_add_unsigned_bool_arg",
            ChcConfig::default(),
        );
        chc_ctx.declare_block_relations();

        let dest_local = 0;
        assert!(
            chc_ctx.flatten.flattened_tuple_locals.contains(&dest_local),
            "destination local should be flattened"
        );

        let bool_operand_lhs = rustc_public::mir::Operand::Copy(rustc_public::mir::Place {
            local: 3,
            projection: vec![],
        });
        let bool_operand_rhs = rustc_public::mir::Operand::Copy(rustc_public::mir::Place {
            local: 3,
            projection: vec![],
        });
        let modified: HashSet<usize> = HashSet::new();

        let result = chc_ctx.translate_iterator_intrinsic_call(
            StubKind::CheckedAddUnsigned,
            &[bool_operand_lhs, bool_operand_rhs],
            &modified,
            Some(dest_local),
        );
        assert!(
            result.is_some(),
            "CheckedAddUnsigned should produce payload expression for flattened destination"
        );
        let result = result.unwrap();
        assert!(
            result.sort().is_bitvec(),
            "fallback payload should be a bitvector, got {:?}",
            result.sort()
        );
        let smt = result.to_string();
        assert!(
            !smt.contains("checked_add_lhs") && !smt.contains("checked_add_rhs"),
            "fallback should avoid symbolic checked_add_* vars, got: {smt}"
        );
    });
}
