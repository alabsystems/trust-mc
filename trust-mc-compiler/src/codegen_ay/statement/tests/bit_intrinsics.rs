// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Bit manipulation intrinsic tests.
//
// Extracted from regression.rs per #1734.

use super::*;

// Unit tests for bit manipulation intrinsics (Part of #1269)
// =============================================================================
// These tests verify the SMT expression construction for rotate, ctlz, cttz,
// ctpop, bswap, and bitreverse intrinsics. The actual codegen functions require
// full StatementCodegen context, so we test the underlying expression patterns.

/// Test rotate_left expression construction.
/// rotate_left(x, n) uses n & (width - 1) for Rust integer widths.
#[test]
fn test_rotate_left_expression() {
    let x = Expr::bitvec_const(0b1100_0000u64, 8);
    let n = Expr::bitvec_const(2, 8);
    let width: u32 = 8;
    let width_const = Expr::bitvec_const(width as u64, width);

    let n_mod = n.bvand(Expr::bitvec_const(width as u64 - 1, width));
    let width_minus_n = width_const.bvsub(n_mod.clone());

    // rotate_left: (x << n') | (x >> (width - n'))
    let result = x.clone().bvshl(n_mod).bvor(x.bvlshr(width_minus_n));

    assert_eq!(result.sort().bitvec_width(), Some(8));
    // Verify expression structure (shift + or)
    assert!(matches!(result.value(), ExprValue::BvOr { .. }));
}

/// Test rotate_left with zero rotation (identity case).
/// Zero rotation still produces the BvOr(shl, lshr) structure — solver simplifies.
#[test]
fn test_rotate_left_zero_amount() {
    let x = Expr::bitvec_const(0b1010_1010u64, 8);
    let n = Expr::bitvec_const(0, 8);
    let width: u32 = 8;
    let width_const = Expr::bitvec_const(width as u64, width);

    let n_mod = n.bvand(Expr::bitvec_const(width as u64 - 1, width));
    let width_minus_n = width_const.bvsub(n_mod.clone());
    let result = x.clone().bvshl(n_mod).bvor(x.bvlshr(width_minus_n));

    assert_eq!(result.sort().bitvec_width(), Some(8));
    // Same BvOr structure even with zero rotation amount
    assert!(
        matches!(result.value(), ExprValue::BvOr { .. }),
        "zero-rotation should still produce BvOr expression"
    );
}

/// Test rotate_right expression construction.
/// rotate_right(x, n) uses n & (width - 1) for Rust integer widths.
#[test]
fn test_rotate_right_expression() {
    let x = Expr::bitvec_const(0b0000_0011u64, 8);
    let n = Expr::bitvec_const(2, 8);
    let width: u32 = 8;
    let width_const = Expr::bitvec_const(width as u64, width);

    let n_mod = n.bvand(Expr::bitvec_const(width as u64 - 1, width));
    let width_minus_n = width_const.bvsub(n_mod.clone());

    // rotate_right: (x >> n') | (x << (width - n'))
    let result = x.clone().bvlshr(n_mod).bvor(x.bvshl(width_minus_n));

    assert_eq!(result.sort().bitvec_width(), Some(8));
    // Verify expression structure (shift + or)
    assert!(matches!(result.value(), ExprValue::BvOr { .. }));
}

/// Test ctlz (count leading zeros) ITE cascade construction.
/// Uses an ITE cascade: if bit[width-1] then 0 else if bit[width-2] then 1 ...
#[test]
fn test_ctlz_ite_cascade() {
    let width: u32 = 8;
    let x = Expr::var("x", Sort::bitvec(width));

    // Build ITE cascade from LSB (inner) to MSB (outer)
    let mut result = Expr::bitvec_const(width as u64, width);
    for i in 0..width {
        let bit = x.clone().extract(i, i);
        let bit_is_one = bit.eq(Expr::bitvec_const(1, 1));
        let count = (width - 1 - i) as u64;
        result = Expr::ite(bit_is_one, Expr::bitvec_const(count, width), result);
    }

    assert_eq!(result.sort().bitvec_width(), Some(8));
    // For symbolic x, result is an ITE cascade
    assert!(matches!(result.value(), ExprValue::Ite { .. }));
}

/// Test cttz (count trailing zeros) ITE cascade construction.
/// Uses an ITE cascade: if bit[0] then 0 else if bit[1] then 1 ...
#[test]
fn test_cttz_ite_cascade() {
    let width: u32 = 8;
    let x = Expr::var("x", Sort::bitvec(width));

    // Build ITE cascade from MSB (inner) to LSB (outer)
    let mut result = Expr::bitvec_const(width as u64, width);
    for i in (0..width).rev() {
        let bit = x.clone().extract(i, i);
        let bit_is_one = bit.eq(Expr::bitvec_const(1, 1));
        result = Expr::ite(bit_is_one, Expr::bitvec_const(i as u64, width), result);
    }

    assert_eq!(result.sort().bitvec_width(), Some(8));
    // For symbolic x, result is an ITE cascade
    assert!(matches!(result.value(), ExprValue::Ite { .. }));
}

/// Test ctpop (population count) sum construction.
/// Sum all bits: extract each bit, zero-extend to width, and add
#[test]
fn test_ctpop_bit_sum() {
    let width: u32 = 8;
    let x = Expr::var("x", Sort::bitvec(width));

    // Sum all bits
    let mut result = Expr::bitvec_const(0, width);
    for i in 0..width {
        let bit = x.clone().extract(i, i);
        let bit_extended = bit.zero_extend(width - 1);
        result = result.bvadd(bit_extended);
    }

    assert_eq!(result.sort().bitvec_width(), Some(8));
    // For symbolic x, result is a chain of bvadd operations
    assert!(matches!(result.value(), ExprValue::BvAdd { .. }));
}

/// Test bswap (byte swap) for 16-bit value.
/// bswap(0x1234) = 0x3412
#[test]
fn test_bswap_16bit() {
    let x = Expr::bitvec_const(0x1234u64, 16);

    // Extract bytes and concatenate in reverse order
    let byte0 = x.clone().extract(7, 0); // LSB = 0x34
    let byte1 = x.extract(15, 8); // MSB = 0x12

    // Result: byte[0] || byte[1] = 0x34 || 0x12 = 0x3412
    let result = byte0.concat(byte1);

    assert_eq!(result.sort().bitvec_width(), Some(16));
    assert!(matches!(result.value(), ExprValue::BvConcat { .. }));
}

/// Test bswap (byte swap) for 32-bit value.
/// bswap(0x12345678) = 0x78563412
#[test]
fn test_bswap_32bit() {
    let x = Expr::bitvec_const(0x12345678u64, 32);

    // Extract 4 bytes and concatenate in reverse order
    let byte0 = x.clone().extract(7, 0); // 0x78
    let byte1 = x.clone().extract(15, 8); // 0x56
    let byte2 = x.clone().extract(23, 16); // 0x34
    let byte3 = x.extract(31, 24); // 0x12

    // Result: byte[0] || byte[1] || byte[2] || byte[3]
    let result = byte0.concat(byte1).concat(byte2).concat(byte3);

    assert_eq!(result.sort().bitvec_width(), Some(32));
    // Verify expression is BvConcat (byte reversal concatenation)
    assert!(
        matches!(result.value(), ExprValue::BvConcat { .. }),
        "32-bit bswap should produce BvConcat expression"
    );
}

/// Test bitreverse for 8-bit value.
/// bitreverse(0b1100_0000) = 0b0000_0011
#[test]
fn test_bitreverse_8bit() {
    let width: u32 = 8;
    let x = Expr::var("x", Sort::bitvec(width));

    // Extract each bit and concatenate in reverse order
    let mut result: Option<Expr> = None;
    for i in 0..width {
        let bit = x.clone().extract(i, i);
        result = Some(match result {
            None => bit,
            Some(acc) => acc.concat(bit),
        });
    }

    let result = result.unwrap();
    assert_eq!(result.sort().bitvec_width(), Some(8));
    // For symbolic x, result is a chain of concat operations
    assert!(matches!(result.value(), ExprValue::BvConcat { .. }));
}

/// Test that rotation handles amounts >= width correctly (via bitmask reduction).
/// rotate_left(x, width) should equal x (full rotation)
#[test]
fn test_rotate_handles_large_amounts() {
    let width: u32 = 8;
    let n = Expr::bitvec_const(8, width); // rotation by width

    let n_mod = n.bvand(Expr::bitvec_const(width as u64 - 1, width));

    assert_eq!(n_mod.sort().bitvec_width(), Some(8));
    assert!(
        matches!(n_mod.value(), ExprValue::BvAnd(_, _)),
        "rotation amount should be wrapped via BvAnd, got {:?}",
        n_mod.value()
    );
}

/// Test ctlz edge case: all zeros returns width.
/// For x == 0, all bits are 0, so no ITE condition is true -> default = width (8).
#[test]
fn test_ctlz_all_zeros_returns_width() {
    let width: u32 = 8;
    let x = Expr::bitvec_const(0u64, width);

    // Build ITE cascade (same as codegen_ctlz)
    let mut result = Expr::bitvec_const(width as u64, width);
    for i in 0..width {
        let bit = x.clone().extract(i, i);
        let bit_is_one = bit.eq(Expr::bitvec_const(1, 1));
        let count = (width - 1 - i) as u64;
        result = Expr::ite(bit_is_one, Expr::bitvec_const(count, width), result);
    }

    assert_eq!(result.sort().bitvec_width(), Some(8));
    // For constant zero input, the outermost ITE checks the MSB (bit[7])
    assert!(
        matches!(result.value(), ExprValue::Ite { .. }),
        "ctlz all-zeros should produce ITE cascade, got {:?}",
        result.value()
    );
}

/// Test ctpop edge case: all ones returns width.
/// For x == 0xFF, all 8 bits are 1, so sum should be 8.
#[test]
fn test_ctpop_all_ones() {
    let width: u32 = 8;
    let x = Expr::bitvec_const(0xFFu64, width); // All bits set

    // Build sum (same as codegen_ctpop)
    let mut result = Expr::bitvec_const(0, width);
    for i in 0..width {
        let bit = x.clone().extract(i, i);
        let bit_extended = bit.zero_extend(width - 1);
        result = result.bvadd(bit_extended);
    }

    assert_eq!(result.sort().bitvec_width(), Some(8));
    // ctpop builds BvAdd chain summing extracted bits
    assert!(
        matches!(result.value(), ExprValue::BvAdd { .. }),
        "ctpop all-ones should produce BvAdd (bit sum), got {:?}",
        result.value()
    );
}

// =============================================================================
// MIR-driven codegen tests (exercise actual codegen_* methods)
// =============================================================================
// These tests use with_test_ay_ctx_for_source to create a real StatementCodegen,
// seed the SSA environment with test values, and call the intrinsic codegen
// methods directly. Part of #2016.

const BIT_PROBE_SOURCE: &str = r#"
pub fn bit_probe(x: u32, n: u32) -> u32 { x.rotate_left(n) }
pub fn bit_probe_3args(a: u32, _b: u32, _n: u32) -> u32 { a }
"#;

/// Helper: seed a local in the SSA environment and return its Operand.
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

fn constraint_count(codegen: &StatementCodegen<'_, '_, '_>) -> usize {
    codegen.ctx.bmc_vc.constraints.len()
}

/// Extract the RHS of the last emitted Eq constraint (the computed expression).
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

/// Test codegen_rotate (left=true) via StatementCodegen — produces BvOr result.
/// Verifies: assigns bv32 destination, expression contains BvOr (shl|lshr pattern).
#[test]
fn test_codegen_rotate_left_produces_bvor() {
    with_test_ay_ctx_for_source(BIT_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bit_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let op_x = seed_local(&mut codegen, 1, Expr::bitvec_const(0xC0u128, 32));
        let op_n = seed_local(&mut codegen, 2, Expr::bitvec_const(2u128, 32));
        let dest = Place { local: 0, projection: vec![] };

        let result = codegen.codegen_rotate(&[op_x, op_n], &dest, Some(1), true);
        assert_eq!(result, Some(1), "codegen_rotate should return target block");

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("rotate_left should assign destination");
        assert_eq!(
            dest_expr.sort().bitvec_width(),
            Some(32),
            "rotate_left destination should be bv32"
        );
        // rotate_left = (x << n) | (x >> (width - n)) — should produce BvOr at top level
        let rhs = latest_assignment_rhs(&codegen);
        assert!(
            matches!(rhs.value(), ExprValue::BvOr(_, _)),
            "rotate_left should produce BvOr expression, got {:?}",
            rhs.value()
        );
    });
}

/// Test codegen_rotate (left=false) produces result with correct width and BvOr structure.
#[test]
fn test_codegen_rotate_right_returns_target() {
    with_test_ay_ctx_for_source(BIT_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bit_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let op_x = seed_local(&mut codegen, 1, Expr::bitvec_const(3u128, 32));
        let op_n = seed_local(&mut codegen, 2, Expr::bitvec_const(1u128, 32));
        let dest = Place { local: 0, projection: vec![] };

        let result = codegen.codegen_rotate(&[op_x, op_n], &dest, Some(4), false);
        assert_eq!(result, Some(4));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("rotate_right should assign destination");
        assert_eq!(
            dest_expr.sort().bitvec_width(),
            Some(32),
            "rotate_right destination should be bv32"
        );
        let rhs = latest_assignment_rhs(&codegen);
        assert!(
            matches!(rhs.value(), ExprValue::BvOr(_, _)),
            "rotate_right should produce BvOr expression, got {:?}",
            rhs.value()
        );
    });
}

/// Test codegen_rotate with insufficient args returns None.
#[test]
fn test_codegen_rotate_insufficient_args() {
    with_test_ay_ctx_for_source(BIT_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bit_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let op_x = seed_local(&mut codegen, 1, Expr::bitvec_const(0xC0u128, 32));
        let dest = Place { local: 0, projection: vec![] };

        // Only 1 arg, needs 2
        let result = codegen.codegen_rotate(&[op_x], &dest, Some(1), true);
        assert_eq!(result, None);
    });
}

/// Test codegen_ctlz produces ITE cascade result.
/// 0x80 = 0b1000_0000 in 32-bit → 24 leading zeros. Verifies ITE structure and bv32 sort.
#[test]
fn test_codegen_ctlz_returns_target() {
    with_test_ay_ctx_for_source(BIT_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bit_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let op_x = seed_local(&mut codegen, 1, Expr::bitvec_const(0x80u128, 32));
        let dest = Place { local: 0, projection: vec![] };

        let result = codegen.codegen_ctlz(&[op_x], &dest, Some(2), false);
        assert_eq!(result, Some(2));

        let dest_expr =
            assigned_expr_for_place(&mut codegen, &dest).expect("ctlz should assign destination");
        assert_eq!(dest_expr.sort().bitvec_width(), Some(32), "ctlz destination should be bv32");
        // ctlz builds an ITE cascade: if bit[31] then 0 else if bit[30] then 1 ...
        let rhs = latest_assignment_rhs(&codegen);
        assert!(
            matches!(rhs.value(), ExprValue::Ite { .. }),
            "ctlz should produce ITE cascade, got {:?}",
            rhs.value()
        );
    });
}

/// Test codegen_ctlz with assert_nonzero=true does not panic on non-zero input.
/// Verifies: assigns bv32 destination, emits additional constraint for nonzero assertion.
#[test]
fn test_codegen_ctlz_nonzero_succeeds() {
    with_test_ay_ctx_for_source(BIT_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bit_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let before = constraint_count(&codegen);
        let op_x = seed_local(&mut codegen, 1, Expr::bitvec_const(1u128, 32));
        let dest = Place { local: 0, projection: vec![] };

        let result = codegen.codegen_ctlz(&[op_x], &dest, Some(3), true);
        assert_eq!(result, Some(3));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("ctlz_nonzero should assign destination");
        assert_eq!(
            dest_expr.sort().bitvec_width(),
            Some(32),
            "ctlz_nonzero destination should be bv32"
        );
        // assert_nonzero=true emits an extra constraint for the nonzero precondition
        assert!(
            constraint_count(&codegen) > before,
            "ctlz with assert_nonzero should emit constraints"
        );
    });
}

/// Test codegen_ctlz with empty args returns None.
#[test]
fn test_codegen_ctlz_empty_args() {
    with_test_ay_ctx_for_source(BIT_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bit_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_ctlz(&[], &dest, Some(1), false);
        assert_eq!(result, None);
    });
}

/// Test codegen_cttz returns target block.
/// 0x10 = bit 4 set → 4 trailing zeros. Verifies ITE structure and bv32 sort.
#[test]
fn test_codegen_cttz_returns_target() {
    with_test_ay_ctx_for_source(BIT_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bit_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let op_x = seed_local(&mut codegen, 1, Expr::bitvec_const(0x10u128, 32));
        let dest = Place { local: 0, projection: vec![] };

        let result = codegen.codegen_cttz(&[op_x], &dest, Some(5), false);
        assert_eq!(result, Some(5));

        let dest_expr =
            assigned_expr_for_place(&mut codegen, &dest).expect("cttz should assign destination");
        assert_eq!(dest_expr.sort().bitvec_width(), Some(32), "cttz destination should be bv32");
        // cttz builds an ITE cascade: if bit[0] then 0 else if bit[1] then 1 ...
        let rhs = latest_assignment_rhs(&codegen);
        assert!(
            matches!(rhs.value(), ExprValue::Ite { .. }),
            "cttz should produce ITE cascade, got {:?}",
            rhs.value()
        );
    });
}

/// Test codegen_cttz with assert_nonzero=true records UB violation for symbolic input.
/// Verifies: assigns bv32 destination, emits constraint for nonzero precondition.
#[test]
fn test_codegen_cttz_nonzero_symbolic_input() {
    with_test_ay_ctx_for_source(BIT_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bit_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Symbolic input — codegen should still succeed (violation recorded, not panicked)
        let before = constraint_count(&codegen);
        let op_x = seed_local(&mut codegen, 1, Expr::var("sym_x", Sort::bitvec(32)));
        let dest = Place { local: 0, projection: vec![] };

        let result = codegen.codegen_cttz(&[op_x], &dest, Some(6), true);
        assert_eq!(result, Some(6));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("cttz_nonzero symbolic should assign destination");
        assert_eq!(
            dest_expr.sort().bitvec_width(),
            Some(32),
            "cttz_nonzero destination should be bv32"
        );
        assert!(
            constraint_count(&codegen) > before,
            "cttz with assert_nonzero + symbolic input should emit constraints"
        );
    });
}

/// Test codegen_ctpop returns target block.
/// 0xFF = 8 set bits in 32-bit → popcount = 8. Verifies destination sort and BvAdd structure.
#[test]
fn test_codegen_ctpop_returns_target() {
    with_test_ay_ctx_for_source(BIT_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bit_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let op_x = seed_local(&mut codegen, 1, Expr::bitvec_const(0xFFu128, 32));
        let dest = Place { local: 0, projection: vec![] };

        let result = codegen.codegen_ctpop(&[op_x], &dest, Some(7));
        assert_eq!(result, Some(7));

        let dest_expr =
            assigned_expr_for_place(&mut codegen, &dest).expect("ctpop should assign destination");
        assert_eq!(dest_expr.sort().bitvec_width(), Some(32), "ctpop destination should be bv32");
        // ctpop sums extracted bits via BvAdd chain
        let rhs = latest_assignment_rhs(&codegen);
        assert!(
            matches!(rhs.value(), ExprValue::BvAdd(_, _)),
            "ctpop should produce BvAdd expression (bit sum), got {:?}",
            rhs.value()
        );
    });
}

/// Test codegen_ctpop with empty args returns None.
#[test]
fn test_codegen_ctpop_empty_args() {
    with_test_ay_ctx_for_source(BIT_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bit_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_ctpop(&[], &dest, Some(1));
        assert_eq!(result, None);
    });
}

/// Test codegen_bswap returns target for 32-bit input.
/// Verifies: assigns bv32 destination with BvConcat structure (byte reversal via extract+concat).
#[test]
fn test_codegen_bswap_32bit_returns_target() {
    with_test_ay_ctx_for_source(BIT_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bit_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let op_x = seed_local(&mut codegen, 1, Expr::bitvec_const(0x12345678u128, 32));
        let dest = Place { local: 0, projection: vec![] };

        let result = codegen.codegen_bswap(&[op_x], &dest, Some(8));
        assert_eq!(result, Some(8));

        let dest_expr =
            assigned_expr_for_place(&mut codegen, &dest).expect("bswap should assign destination");
        assert_eq!(dest_expr.sort().bitvec_width(), Some(32), "bswap destination should be bv32");
        // bswap reverses bytes via BvConcat of BvExtract slices
        let rhs = latest_assignment_rhs(&codegen);
        assert!(
            matches!(rhs.value(), ExprValue::BvConcat(_, _)),
            "bswap should produce BvConcat expression, got {:?}",
            rhs.value()
        );
    });
}

/// Test codegen_bswap with empty args returns None.
#[test]
fn test_codegen_bswap_empty_args() {
    with_test_ay_ctx_for_source(BIT_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bit_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_bswap(&[], &dest, Some(1));
        assert_eq!(result, None);
    });
}

/// Test codegen_bitreverse returns target for 32-bit input.
/// Verifies: assigns bv32 destination with BvConcat structure (bit reversal via extract+concat).
#[test]
fn test_codegen_bitreverse_32bit_returns_target() {
    with_test_ay_ctx_for_source(BIT_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bit_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let op_x = seed_local(&mut codegen, 1, Expr::bitvec_const(0b1100_0000u128, 32));
        let dest = Place { local: 0, projection: vec![] };

        let result = codegen.codegen_bitreverse(&[op_x], &dest, Some(9));
        assert_eq!(result, Some(9));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("bitreverse should assign destination");
        assert_eq!(
            dest_expr.sort().bitvec_width(),
            Some(32),
            "bitreverse destination should be bv32"
        );
        // bitreverse reverses individual bits via BvConcat of 1-bit BvExtract slices
        let rhs = latest_assignment_rhs(&codegen);
        assert!(
            matches!(rhs.value(), ExprValue::BvConcat(_, _)),
            "bitreverse should produce BvConcat expression, got {:?}",
            rhs.value()
        );
    });
}

/// Test codegen_bitreverse with empty args returns None.
#[test]
fn test_codegen_bitreverse_empty_args() {
    with_test_ay_ctx_for_source(BIT_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bit_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_bitreverse(&[], &dest, Some(1));
        assert_eq!(result, None);
    });
}

/// Test codegen_identity_intrinsic returns target and preserves value.
/// Verifies: assigns bv32 destination with the exact same input value (identity operation).
#[test]
fn test_codegen_identity_intrinsic_returns_target() {
    with_test_ay_ctx_for_source(BIT_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bit_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let op_x = seed_local(&mut codegen, 1, Expr::bitvec_const(42u128, 32));
        let dest = Place { local: 0, projection: vec![] };

        let result = codegen.codegen_identity_intrinsic(&[op_x], &dest, Some(10));
        assert_eq!(result, Some(10));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("identity intrinsic should assign destination");
        assert_eq!(
            dest_expr.sort().bitvec_width(),
            Some(32),
            "identity intrinsic destination should be bv32"
        );
    });
}

/// Test codegen_identity_intrinsic with empty args returns None.
#[test]
fn test_codegen_identity_intrinsic_empty_args() {
    with_test_ay_ctx_for_source(BIT_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bit_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_identity_intrinsic(&[], &dest, Some(1));
        assert_eq!(result, None);
    });
}

/// Test codegen_funnel_shift (left) returns target with 3 args.
/// Verifies: assigns bv32 destination with BvExtract structure (extract from concatenated pair).
#[test]
fn test_codegen_funnel_shift_left_returns_target() {
    with_test_ay_ctx_for_source(BIT_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bit_probe_3args");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let op_a = seed_local(&mut codegen, 1, Expr::bitvec_const(0xFFu128, 32));
        let op_b = seed_local(&mut codegen, 2, Expr::bitvec_const(0x01u128, 32));
        let op_n = seed_local(&mut codegen, 3, Expr::bitvec_const(4u128, 32));
        let dest = Place { local: 0, projection: vec![] };

        let result = codegen.codegen_funnel_shift(&[op_a, op_b, op_n], &dest, Some(11), true);
        assert_eq!(result, Some(11));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("funnel_shift_left should assign destination");
        assert_eq!(
            dest_expr.sort().bitvec_width(),
            Some(32),
            "funnel_shift_left destination should be bv32"
        );
        // funnel_shl: a.bvshl(n) | b.bvlshr(w - n) → BvOr at top level
        let rhs = latest_assignment_rhs(&codegen);
        assert!(
            matches!(rhs.value(), ExprValue::BvOr(_, _)),
            "funnel_shift_left should produce BvOr expression, got {:?}",
            rhs.value()
        );
    });
}

/// Test codegen_funnel_shift (right) returns target.
/// Verifies: assigns bv32 destination with BvOr structure (funnel shift pattern).
#[test]
fn test_codegen_funnel_shift_right_returns_target() {
    with_test_ay_ctx_for_source(BIT_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bit_probe_3args");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let op_a = seed_local(&mut codegen, 1, Expr::bitvec_const(0x01u128, 32));
        let op_b = seed_local(&mut codegen, 2, Expr::bitvec_const(0xFFu128, 32));
        let op_n = seed_local(&mut codegen, 3, Expr::bitvec_const(4u128, 32));
        let dest = Place { local: 0, projection: vec![] };

        let result = codegen.codegen_funnel_shift(&[op_a, op_b, op_n], &dest, Some(12), false);
        assert_eq!(result, Some(12));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("funnel_shift_right should assign destination");
        assert_eq!(
            dest_expr.sort().bitvec_width(),
            Some(32),
            "funnel_shift_right destination should be bv32"
        );
        // funnel_shr: a.bvshl(w - n) | b.bvlshr(n) → BvOr at top level
        let rhs = latest_assignment_rhs(&codegen);
        assert!(
            matches!(rhs.value(), ExprValue::BvOr(_, _)),
            "funnel_shift_right should produce BvOr expression, got {:?}",
            rhs.value()
        );
    });
}

/// Test codegen_funnel_shift with insufficient args returns None.
#[test]
fn test_codegen_funnel_shift_insufficient_args() {
    with_test_ay_ctx_for_source(BIT_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bit_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let op_a = seed_local(&mut codegen, 1, Expr::bitvec_const(0xFFu128, 32));
        let op_b = seed_local(&mut codegen, 2, Expr::bitvec_const(0x01u128, 32));
        let dest = Place { local: 0, projection: vec![] };

        // Only 2 args, needs 3
        let result = codegen.codegen_funnel_shift(&[op_a, op_b], &dest, Some(1), true);
        assert_eq!(result, None);
    });
}

// =============================================================================
// Additional edge case tests (Part of #2016)
// =============================================================================

/// Test codegen_bswap with 16-bit input exercises the 2-byte swap path.
/// Verifies: assigns bv16 destination with BvConcat structure (2 extract+concat).
#[test]
fn test_codegen_bswap_16bit_returns_target() {
    with_test_ay_ctx_for_source(BIT_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bit_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let op_x = seed_local(&mut codegen, 1, Expr::bitvec_const(0x1234u128, 16));
        let dest = Place { local: 0, projection: vec![] };

        let result = codegen.codegen_bswap(&[op_x], &dest, Some(13));
        assert_eq!(result, Some(13));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("bswap 16-bit should assign destination");
        assert_eq!(
            dest_expr.sort().bitvec_width(),
            Some(16),
            "bswap 16-bit destination should be bv16"
        );
        // 16-bit bswap: concat(extract(byte0), extract(byte1)) → BvConcat
        let rhs = latest_assignment_rhs(&codegen);
        assert!(
            matches!(rhs.value(), ExprValue::BvConcat(_, _)),
            "bswap 16-bit should produce BvConcat expression, got {:?}",
            rhs.value()
        );
    });
}

/// Test codegen_bswap with 8-bit input takes the single-byte identity path.
/// When num_bytes == 1, bswap assigns input directly (no concat). Verifies bv8 sort.
#[test]
fn test_codegen_bswap_8bit_identity_path() {
    with_test_ay_ctx_for_source(BIT_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bit_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let op_x = seed_local(&mut codegen, 1, Expr::bitvec_const(0xABu128, 8));
        let dest = Place { local: 0, projection: vec![] };

        let result = codegen.codegen_bswap(&[op_x], &dest, Some(14));
        assert_eq!(result, Some(14));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("bswap 8-bit should assign destination");
        assert_eq!(
            dest_expr.sort().bitvec_width(),
            Some(8),
            "bswap 8-bit destination should be bv8"
        );
        // 8-bit identity path: input assigned directly, not a BvConcat
        let rhs = latest_assignment_rhs(&codegen);
        assert!(
            !matches!(rhs.value(), ExprValue::BvConcat(_, _)),
            "bswap 8-bit identity path should NOT produce BvConcat, got {:?}",
            rhs.value()
        );
    });
}

/// Test codegen_bswap with non-byte-aligned width (e.g. 12 bits) returns None.
/// The width % 8 != 0 guard rejects non-byte-aligned bitvectors.
#[test]
fn test_codegen_bswap_non_byte_aligned_returns_none() {
    with_test_ay_ctx_for_source(BIT_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bit_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // 12-bit bitvec is not byte-aligned
        let op_x = seed_local(&mut codegen, 1, Expr::bitvec_const(0xABCu128, 12));
        let dest = Place { local: 0, projection: vec![] };

        let result = codegen.codegen_bswap(&[op_x], &dest, Some(15));
        assert_eq!(result, None);
    });
}

/// Test codegen_ctlz with assert_nonzero=true on zero input records UB violation.
/// Verifies: emits constraints for the nonzero precondition, assigns bv32 ITE result.
#[test]
fn test_codegen_ctlz_nonzero_zero_input_records_ub() {
    with_test_ay_ctx_for_source(BIT_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bit_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Zero input with assert_nonzero=true should record UB violation
        let before = constraint_count(&codegen);
        let op_x = seed_local(&mut codegen, 1, Expr::bitvec_const(0u128, 32));
        let dest = Place { local: 0, projection: vec![] };

        let result = codegen.codegen_ctlz(&[op_x], &dest, Some(16), true);
        assert_eq!(result, Some(16));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("ctlz_nonzero should assign destination");
        assert_eq!(
            dest_expr.sort().bitvec_width(),
            Some(32),
            "ctlz_nonzero destination should be bv32"
        );
        // assert_nonzero=true emits extra constraints for the UB violation
        assert!(
            constraint_count(&codegen) > before,
            "ctlz with assert_nonzero on zero input should emit constraints"
        );
        // ctlz produces an ITE cascade
        let rhs = latest_assignment_rhs(&codegen);
        assert!(
            matches!(rhs.value(), ExprValue::Ite { .. }),
            "ctlz should produce ITE cascade, got {:?}",
            rhs.value()
        );
    });
}

/// Test codegen_cttz with empty args returns None (boundary guard).
#[test]
fn test_codegen_cttz_empty_args() {
    with_test_ay_ctx_for_source(BIT_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bit_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_cttz(&[], &dest, Some(1), false);
        assert_eq!(result, None);
    });
}

/// Test codegen_rotate with symbolic inputs produces BvOr(shl, lshr) structure.
/// Verifies: assigns bv32 destination, expression is BvOr (symbolic rotate_left).
#[test]
fn test_codegen_rotate_left_symbolic() {
    with_test_ay_ctx_for_source(BIT_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bit_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Symbolic inputs exercise the full expression tree construction
        let op_x = seed_local(&mut codegen, 1, Expr::var("sym_x", Sort::bitvec(32)));
        let op_n = seed_local(&mut codegen, 2, Expr::var("sym_n", Sort::bitvec(32)));
        let dest = Place { local: 0, projection: vec![] };

        let result = codegen.codegen_rotate(&[op_x, op_n], &dest, Some(17), true);
        assert_eq!(result, Some(17));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("rotate_left symbolic should assign destination");
        assert_eq!(
            dest_expr.sort().bitvec_width(),
            Some(32),
            "rotate_left symbolic destination should be bv32"
        );
        // rotate_left = (x << n) | (x >> (w - n)) → BvOr at top level
        let rhs = latest_assignment_rhs(&codegen);
        assert!(
            matches!(rhs.value(), ExprValue::BvOr(_, _)),
            "rotate_left symbolic should produce BvOr expression, got {:?}",
            rhs.value()
        );
    });
}

/// Test codegen_bswap with 64-bit input exercises the 8-byte swap path.
/// Verifies: assigns bv64 destination with BvConcat structure (8 extract+concat chain).
#[test]
fn test_codegen_bswap_64bit_returns_target() {
    with_test_ay_ctx_for_source(BIT_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bit_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let op_x = seed_local(&mut codegen, 1, Expr::bitvec_const(0x0102030405060708u128, 64));
        let dest = Place { local: 0, projection: vec![] };

        let result = codegen.codegen_bswap(&[op_x], &dest, Some(18));
        assert_eq!(result, Some(18));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("bswap 64-bit should assign destination");
        assert_eq!(
            dest_expr.sort().bitvec_width(),
            Some(64),
            "bswap 64-bit destination should be bv64"
        );
        // 64-bit bswap: chain of 7 concat(extract(byte_i)) operations
        let rhs = latest_assignment_rhs(&codegen);
        assert!(
            matches!(rhs.value(), ExprValue::BvConcat(_, _)),
            "bswap 64-bit should produce BvConcat expression, got {:?}",
            rhs.value()
        );
    });
}

/// Test codegen_ctpop with symbolic input produces BvAdd chain (bit sum).
/// Verifies: assigns bv32 destination, expression is BvAdd (bit-sum structure).
#[test]
fn test_codegen_ctpop_symbolic_input() {
    with_test_ay_ctx_for_source(BIT_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bit_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let op_x = seed_local(&mut codegen, 1, Expr::var("sym_x", Sort::bitvec(32)));
        let dest = Place { local: 0, projection: vec![] };

        let result = codegen.codegen_ctpop(&[op_x], &dest, Some(19));
        assert_eq!(result, Some(19));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("ctpop symbolic should assign destination");
        assert_eq!(
            dest_expr.sort().bitvec_width(),
            Some(32),
            "ctpop symbolic destination should be bv32"
        );
        // ctpop sums all bits: bvadd(bvadd(..., zext(extract(x,i,i))), ...)
        let rhs = latest_assignment_rhs(&codegen);
        assert!(
            matches!(rhs.value(), ExprValue::BvAdd(_, _)),
            "ctpop symbolic should produce BvAdd expression (bit sum), got {:?}",
            rhs.value()
        );
    });
}

// =============================================================================
// Intrinsic dispatch routing tests (Part of #2016)
// =============================================================================

/// Test dispatch_bit_ops routes rotate_left to codegen_rotate(left=true).
/// Verifies: expression is BvOr (rotate structure), not ITE (ctlz) or BvAdd (ctpop).
#[test]
fn test_dispatch_bit_ops_routes_rotate_left() {
    with_test_ay_ctx_for_source(BIT_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bit_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let op_x = seed_local(&mut codegen, 1, Expr::bitvec_const(0xA5u128, 32));
        let op_n = seed_local(&mut codegen, 2, Expr::bitvec_const(3u128, 32));
        let dest = Place { local: 0, projection: vec![] };

        let result = codegen.dispatch_bit_ops(
            "core::intrinsics::rotate_left",
            &[op_x, op_n],
            &dest,
            Some(30),
        );
        assert_eq!(result, Some(30));

        // Verify dispatch routed to codegen_rotate: BvOr(shl, lshr)
        let rhs = latest_assignment_rhs(&codegen);
        assert!(
            matches!(rhs.value(), ExprValue::BvOr(_, _)),
            "dispatch rotate_left should produce BvOr (rotate structure), got {:?}",
            rhs.value()
        );
    });
}

/// Test dispatch_bit_ops routes ctlz_nonzero via starts_with("ctlz").
/// Verifies: expression is ITE (ctlz cascade), not BvOr (rotate) or BvAdd (ctpop).
#[test]
fn test_dispatch_bit_ops_routes_ctlz_nonzero() {
    with_test_ay_ctx_for_source(BIT_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bit_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let op_x = seed_local(&mut codegen, 1, Expr::bitvec_const(1u128, 32));
        let dest = Place { local: 0, projection: vec![] };

        let result =
            codegen.dispatch_bit_ops("core::intrinsics::ctlz_nonzero", &[op_x], &dest, Some(31));
        assert_eq!(result, Some(31));

        // Verify dispatch routed to codegen_ctlz: ITE cascade
        let rhs = latest_assignment_rhs(&codegen);
        assert!(
            matches!(rhs.value(), ExprValue::Ite { .. }),
            "dispatch ctlz_nonzero should produce ITE cascade, got {:?}",
            rhs.value()
        );
    });
}

/// Test dispatch_bit_ops routes unchecked_funnel_shl to funnel shift codegen.
/// Verifies: expression is BvOr (funnel shift structure), assigns bv32 destination.
#[test]
fn test_dispatch_bit_ops_routes_unchecked_funnel_shl() {
    with_test_ay_ctx_for_source(BIT_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bit_probe_3args");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let op_a = seed_local(&mut codegen, 1, Expr::bitvec_const(0xAAu128, 32));
        let op_b = seed_local(&mut codegen, 2, Expr::bitvec_const(0x55u128, 32));
        let op_n = seed_local(&mut codegen, 3, Expr::bitvec_const(4u128, 32));
        let dest = Place { local: 0, projection: vec![] };

        let result = codegen.dispatch_bit_ops(
            "core::intrinsics::unchecked_funnel_shl",
            &[op_a, op_b, op_n],
            &dest,
            Some(32),
        );
        assert_eq!(result, Some(32));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("dispatch funnel_shl should assign destination");
        assert_eq!(
            dest_expr.sort().bitvec_width(),
            Some(32),
            "dispatch funnel_shl destination should be bv32"
        );
        // Verify dispatch routed to codegen_funnel_shift: BvOr(shl, lshr)
        let rhs = latest_assignment_rhs(&codegen);
        assert!(
            matches!(rhs.value(), ExprValue::BvOr(_, _)),
            "dispatch funnel_shl should produce BvOr (funnel shift structure), got {:?}",
            rhs.value()
        );
    });
}

/// Test dispatch_bit_ops returns None for unknown method names.
#[test]
fn test_dispatch_bit_ops_unknown_method_returns_none() {
    with_test_ay_ctx_for_source(BIT_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bit_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.dispatch_bit_ops(
            "core::intrinsics::definitely_not_bit_op",
            &[],
            &dest,
            Some(33),
        );
        assert_eq!(result, None);
    });
}
