// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Regression tests for `stub_dispatch_simple.rs` routing.
//!
//! Part of #3141: MemSizeOf/MemAlignOf moved to try_codegen_alloc_layout_stub
//! which has access to the func operand to extract the generic type arg T.
//! The simple stub dispatcher now returns None for these stubs.

use super::*;
use crate::codegen_ay::stubs::StubKind;

const PROBE_SOURCE: &str = r#"
pub fn size_of_probe() -> usize { 8 }
"#;

const PTR_IS_NULL_SOURCE: &str = r#"
pub fn ptr_is_null_probe(p: *const u32) -> bool {
    p.is_null()
}
"#;

fn assert_ptr_is_null_expr(expr: &Expr) {
    let is_zero_ptr = |candidate: &Expr| {
        matches!(
            candidate.value(),
            ExprValue::BitVecConst { value, width }
                if *width == POINTER_WIDTH && value == &BigInt::from(0u8)
        )
    };

    match expr.value() {
        ExprValue::Eq(lhs, rhs) => {
            assert!(
                is_zero_ptr(lhs) || is_zero_ptr(rhs),
                "ptr::is_null should compare against a null pointer, got {:?}",
                expr.value()
            );
        }
        other => panic!("expected ptr::is_null equality, got {other:?}"),
    }
}

// =============================================================================
// MemSizeOf / MemAlignOf — routed to alloc_layout handler (Part of #3141)
// =============================================================================

/// MemSizeOf is no longer handled by try_codegen_simple_stub (Part of #3141).
/// It's now routed to try_codegen_alloc_layout_stub which extracts the generic
/// type arg T from the func operand for correct layout computation.
#[test]
fn test_mem_size_of_not_handled_by_simple_stub() {
    with_test_ay_ctx_for_source(PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "size_of_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = local_place(0);
        let result = codegen.try_codegen_simple_stub(
            StubKind::MemSizeOf,
            &[],
            &dest,
            Some(1),
            "core::mem::size_of",
        );

        assert_eq!(result, None, "MemSizeOf should NOT be handled by simple stub dispatcher");
    });
}

/// MemAlignOf is no longer handled by try_codegen_simple_stub (Part of #3141).
#[test]
fn test_mem_align_of_not_handled_by_simple_stub() {
    with_test_ay_ctx_for_source(PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "size_of_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = local_place(0);
        let result = codegen.try_codegen_simple_stub(
            StubKind::MemAlignOf,
            &[],
            &dest,
            Some(3),
            "core::mem::align_of",
        );

        assert_eq!(result, None, "MemAlignOf should NOT be handled by simple stub dispatcher");
    });
}

#[test]
fn test_ptr_is_null_simple_stub_compares_pointer_to_zero() {
    with_test_ay_ctx_for_source(PTR_IS_NULL_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "ptr_is_null_probe");
        let body = instance.body().expect("function body");

        for (stub, callee_path) in [
            (StubKind::PtrIsNull, "core::ptr::const_ptr::<u32>::is_null"),
            (StubKind::PtrIsNullRuntime, "core::ptr::const_ptr::<u32>::is_null::runtime"),
        ] {
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

            let dest = local_place(0);
            let before = codegen.ctx.program.commands().len();
            let result = codegen.try_codegen_simple_stub(
                stub,
                &[local_operand(1)],
                &dest,
                Some(1),
                callee_path,
            );

            assert_eq!(result, Some(Some(1)), "{stub:?} should be handled by simple stub dispatch");

            let dest_base = codegen.ssa_base_name(&dest);
            let dest_expr = codegen
                .current_env
                .get(dest_base.as_str())
                .expect("destination should be assigned");
            let added = &codegen.ctx.program.commands()[before..];
            let rhs =
                extract_ssa_rhs(added, dest_expr).expect("should find SSA-defining assertion");
            assert!(rhs.sort().is_bool(), "PtrIsNull result should be Bool");
            assert_ptr_is_null_expr(&rhs);
        }
    });
}
