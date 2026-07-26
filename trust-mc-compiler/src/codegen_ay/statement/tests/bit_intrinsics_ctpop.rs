// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Focused ctpop intrinsic codegen regressions.

use super::*;

const BIT_PROBE_SOURCE: &str = r#"
pub fn bit_probe(x: u32, n: u32) -> u32 { x.rotate_left(n) }
"#;

fn seed_local(
    codegen: &mut StatementCodegen<'_, '_, '_>,
    local_idx: usize,
    value: Expr,
) -> Operand {
    let fn_name =
        codegen.ctx.current_fn().map_or_else(|| "unknown".to_string(), |f| f.name.clone());
    let base_name = format!("{}::local_{}", fn_name, local_idx);
    codegen.env_update(base_name, value);
    Operand::Copy(Place { local: local_idx, projection: vec![] })
}

fn assigned_expr_for_place(
    codegen: &mut StatementCodegen<'_, '_, '_>,
    place: &Place,
) -> Option<Expr> {
    let base = codegen.ssa_base_name(place);
    codegen.env_lookup(&base).cloned()
}

fn latest_assignment_rhs(codegen: &StatementCodegen<'_, '_, '_>) -> Expr {
    let constraint = codegen
        .ctx
        .bmc_vc
        .constraints
        .last()
        .expect("expected assignment constraint after codegen");
    match constraint.value() {
        ExprValue::Eq(_, rhs) => rhs.clone(),
        other => panic!("expected assignment equality constraint, got {other:?}"),
    }
}

/// Test codegen_ctpop on narrow input still returns BV32.
#[test]
fn test_codegen_ctpop_u8_returns_bv32_with_narrow_accumulator() {
    with_test_ay_ctx_for_source(BIT_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bit_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let op_x = seed_local(&mut codegen, 1, Expr::var("sym_u8", Sort::bitvec(8)));
        let dest = Place { local: 0, projection: vec![] };

        let result = codegen.codegen_ctpop(&[op_x], &dest, Some(17));
        assert_eq!(result, Some(17));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("ctpop u8 should assign destination");
        assert_eq!(dest_expr.sort().bitvec_width(), Some(32));

        let rhs = latest_assignment_rhs(&codegen);
        match rhs.value() {
            ExprValue::BvZeroExtend { expr: inner, extra_bits } => {
                assert_eq!(*extra_bits, 28);
                assert_eq!(inner.sort().bitvec_width(), Some(4));
            }
            other => panic!("ctpop u8 should zero-extend a 4-bit accumulator, got {other:?}"),
        }
    });
}
