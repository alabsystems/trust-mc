// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Atomic intrinsic MIR-driven tests.
//!
//! Tests for codegen_atomic_load, codegen_atomic_store, codegen_atomic_exchange,
//! codegen_atomic_cxchg, codegen_atomic_fetch_binop, codegen_atomic_fetch_nand,
//! and codegen_atomic_fetch_minmax.
//!
//! Part of #2016 (test coverage for arithmetic_atomic.rs, 399 lines, 0 tests).

use super::*;
use rustc_public::mir::BinOp;

// Probe source: functions that accept raw pointers and scalars for atomic ops.
// Each function gives us specific MIR local types for constructing Operands.
//
// Locals for each probe:
//   atomic_load_probe:    0=ret(*mut u32), 1=ptr(*mut u32)
//   atomic_store_probe:   0=ret(), 1=ptr(*mut u32), 2=val(u32)
//   atomic_xchg_probe:    0=ret(u32), 1=ptr(*mut u32), 2=val(u32)
//   atomic_cxchg_probe:   0=ret((u32,bool)), 1=ptr(*mut u32), 2=expected(u32), 3=new(u32)
//   atomic_binop_probe:   0=ret(u32), 1=ptr(*mut u32), 2=operand(u32)
//   atomic_u8_probe:      0=ret(u8), 1=ptr(*mut u8), 2=val(u8)
//   atomic_u64_probe:     0=ret(u64), 1=ptr(*mut u64), 2=val(u64)
const ATOMIC_PROBE_SOURCE: &str = r#"
pub fn atomic_load_probe(ptr: *mut u32) -> u32 {
    unsafe { *ptr }
}

pub fn atomic_store_probe(ptr: *mut u32, val: u32) {
    unsafe { *ptr = val; }
}

pub fn atomic_xchg_probe(ptr: *mut u32, val: u32) -> u32 {
    unsafe { core::ptr::replace(ptr, val) }
}

pub fn atomic_cxchg_probe(ptr: *mut u32, expected: u32, new: u32) -> u32 {
    let _ = expected;
    unsafe { core::ptr::replace(ptr, new) }
}

pub fn atomic_binop_probe(ptr: *mut u32, operand: u32) -> u32 {
    let _ = operand;
    unsafe { *ptr }
}

pub fn atomic_u8_probe(ptr: *mut u8, val: u8) -> u8 {
    let _ = val;
    unsafe { *ptr }
}

pub fn atomic_u64_probe(ptr: *mut u64, val: u64) -> u64 {
    let _ = val;
    unsafe { *ptr }
}

pub fn simple_atomic_probe() {}
"#;

/// Seed argument locals into SSA environment with symbolic variables.
fn seed_atomic_args(codegen: &mut StatementCodegen<'_, '_, '_>, body: &rustc_public::mir::Body) {
    for (idx, local_decl) in body.arg_locals().iter().enumerate() {
        let local_idx = idx + 1;
        let local = Local::from(local_idx);
        let place = Place { local, projection: vec![] };
        let base = codegen.ssa_base_name(&place);
        if let Some(sort) = StatementCodegen::infer_sort_from_ty(local_decl.ty) {
            codegen.env_update(base, Expr::var(format!("arg_{local_idx}"), sort));
        } else {
            // Raw pointers may not have a direct sort — seed as bv64 (pointer width)
            codegen.env_update(
                base,
                Expr::var(format!("arg_{local_idx}"), Sort::bitvec(POINTER_WIDTH)),
            );
        }
    }
}

/// Look up the expression currently assigned to a MIR Place via SSA env.
fn assigned_expr_for_place(
    codegen: &mut StatementCodegen<'_, '_, '_>,
    place: &Place,
) -> Option<Expr> {
    let base = codegen.ssa_base_name(place);
    codegen.env_lookup(&base).cloned()
}

/// Return the number of emitted constraints so far.
fn constraint_count(codegen: &StatementCodegen<'_, '_, '_>) -> usize {
    codegen.ctx.bmc_vc.constraints.len()
}

// =============================================================================
// codegen_atomic_load tests
// =============================================================================

/// Test atomic load returns target and assigns a bv32 expression to dest.
#[test]
fn test_atomic_load_returns_target() {
    with_test_ay_ctx_for_source(ATOMIC_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "atomic_load_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_atomic_args(&mut codegen, &body);

        let ptr_place = Place { local: 1, projection: vec![] };
        let args = vec![Operand::Copy(ptr_place)];
        let dest = Place { local: 0, projection: vec![] };
        let pre_constraints = constraint_count(&codegen);

        let result = codegen.codegen_atomic_load(&args, &dest, Some(5));
        assert_eq!(result, Some(5), "atomic_load should return target block");

        // Verify destination was assigned with correct sort width
        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("atomic_load should assign destination expression");
        assert_eq!(
            dest_expr.sort().bitvec_width(),
            Some(32),
            "atomic_load of *mut u32 should produce bv32 destination"
        );
        // Verify SSA constraint was emitted
        assert!(
            constraint_count(&codegen) > pre_constraints,
            "atomic_load should emit at least one SSA assignment constraint"
        );
    });
}

/// Test atomic load with empty args returns None (guard path).
#[test]
fn test_atomic_load_empty_args_returns_none() {
    with_test_ay_ctx_for_source(ATOMIC_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "simple_atomic_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_atomic_load(&[], &dest, Some(5));
        assert_eq!(result, None, "atomic_load with empty args should return None");
    });
}

/// Test atomic load with None target passes through.
#[test]
fn test_atomic_load_none_target() {
    with_test_ay_ctx_for_source(ATOMIC_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "atomic_load_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_atomic_args(&mut codegen, &body);

        let ptr_place = Place { local: 1, projection: vec![] };
        let args = vec![Operand::Copy(ptr_place)];
        let dest = Place { local: 0, projection: vec![] };

        let result = codegen.codegen_atomic_load(&args, &dest, None);
        // Should succeed but return None target
        // (codegen_atomic_load returns `target` which is None)
        assert_eq!(result, None);
    });
}

// =============================================================================
// codegen_atomic_store tests
// =============================================================================

/// Test atomic store returns target and mutates the memory model.
#[test]
fn test_atomic_store_returns_target() {
    with_test_ay_ctx_for_source(ATOMIC_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "atomic_store_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_atomic_args(&mut codegen, &body);

        let ptr_place = Place { local: 1, projection: vec![] };
        let val_place = Place { local: 2, projection: vec![] };
        let args = vec![Operand::Copy(ptr_place), Operand::Copy(val_place)];
        let mem_before = codegen.ctx.memory().to_string();

        let result = codegen.codegen_atomic_store(&args, Some(7));
        assert_eq!(result, Some(7), "atomic_store should return target block");

        // Verify memory model was mutated (store_memory_bytes writes to the memory array)
        let mem_after = codegen.ctx.memory().to_string();
        assert_ne!(mem_before, mem_after, "atomic_store should modify the memory model expression");
        // The memory expression should contain a store operation
        assert!(
            mem_after.contains("store"),
            "atomic_store should produce a store(...) memory expression"
        );
    });
}

/// Test atomic store with insufficient args returns target (no-op fallback).
#[test]
fn test_atomic_store_insufficient_args_returns_target() {
    with_test_ay_ctx_for_source(ATOMIC_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "atomic_load_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Only one arg when two needed — fail-closed
        let result = codegen.codegen_atomic_store(&[], Some(9));
        assert_eq!(result, None, "atomic_store with <2 args must fail-closed (#2497)");
    });
}

// =============================================================================
// codegen_atomic_exchange tests
// =============================================================================

/// Test atomic exchange returns target, assigns old value to dest (bv32), and emits store.
#[test]
fn test_atomic_exchange_returns_target() {
    with_test_ay_ctx_for_source(ATOMIC_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "atomic_xchg_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_atomic_args(&mut codegen, &body);

        let ptr_place = Place { local: 1, projection: vec![] };
        let val_place = Place { local: 2, projection: vec![] };
        let args = vec![Operand::Copy(ptr_place), Operand::Copy(val_place)];
        let dest = Place { local: 0, projection: vec![] };
        let pre_constraints = constraint_count(&codegen);

        let result = codegen.codegen_atomic_exchange(&args, &dest, Some(3));
        assert_eq!(result, Some(3), "atomic_exchange should return target block");

        // Verify destination assigned with old value (bv32 for u32)
        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("atomic_exchange should assign destination (old value)");
        assert_eq!(
            dest_expr.sort().bitvec_width(),
            Some(32),
            "atomic_exchange old value should be bv32 for *mut u32"
        );
        // Verify constraints emitted: load + SSA assignment + store
        assert!(
            constraint_count(&codegen) > pre_constraints,
            "atomic_exchange should emit load and store constraints"
        );
        // Verify memory model was mutated by the store of the new value
        let mem = codegen.ctx.memory().to_string();
        assert!(
            mem.contains("store"),
            "atomic_exchange should produce a store(...) in memory model, got {mem}"
        );
    });
}

/// Test atomic exchange with insufficient args returns None.
#[test]
fn test_atomic_exchange_insufficient_args_returns_none() {
    with_test_ay_ctx_for_source(ATOMIC_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "atomic_load_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_atomic_exchange(&[], &dest, Some(3));
        assert_eq!(result, None, "atomic_exchange with <2 args should return None");
    });
}

// =============================================================================
// codegen_atomic_cxchg tests
// =============================================================================

/// Test atomic compare-exchange returns target and assigns two-field structure to dest.
/// Field 0 is the old value (bv32), field 1 is a success flag (ITE expression, bv8).
#[test]
fn test_atomic_cxchg_returns_target() {
    with_test_ay_ctx_for_source(ATOMIC_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "atomic_cxchg_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_atomic_args(&mut codegen, &body);

        let ptr_place = Place { local: 1, projection: vec![] };
        let expected_place = Place { local: 2, projection: vec![] };
        let new_place = Place { local: 3, projection: vec![] };
        let args =
            vec![Operand::Copy(ptr_place), Operand::Copy(expected_place), Operand::Copy(new_place)];
        let dest = Place { local: 0, projection: vec![] };
        let pre_constraints = constraint_count(&codegen);

        let result = codegen.codegen_atomic_cxchg(&args, &dest, Some(10));
        assert_eq!(result, Some(10), "atomic_cxchg should return target block");

        // cxchg emits multiple constraints: load, field.0 assign, field.1 assign, conditional store
        assert!(
            constraint_count(&codegen) >= pre_constraints + 2,
            "atomic_cxchg should emit at least 2 constraints (field assignments + store)"
        );
        // Verify memory model contains ITE for conditional store (only store if old == expected)
        let mem = codegen.ctx.memory().to_string();
        assert!(mem.contains("ite"), "cxchg should emit conditional ITE store, got {mem}");
        // Verify field.0 (old value) and field.1 (success flag) were assigned
        let old_base = format!("{}.0", codegen.ssa_base_name(&dest));
        let success_base = format!("{}.1", codegen.ssa_base_name(&dest));
        assert!(codegen.env_lookup(&old_base).is_some(), "cxchg should assign field.0 (old value)");
        assert!(
            codegen.env_lookup(&success_base).is_some(),
            "cxchg should assign field.1 (success flag)"
        );
    });
}

/// Test atomic compare-exchange with insufficient args returns None.
#[test]
fn test_atomic_cxchg_insufficient_args_returns_none() {
    with_test_ay_ctx_for_source(ATOMIC_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "atomic_store_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = Place { local: 0, projection: vec![] };
        // Only 2 args when 3 needed
        let ptr_place = Place { local: 1, projection: vec![] };
        let val_place = Place { local: 2, projection: vec![] };
        let args = vec![Operand::Copy(ptr_place), Operand::Copy(val_place)];
        let result = codegen.codegen_atomic_cxchg(&args, &dest, Some(10));
        assert_eq!(result, None, "atomic_cxchg with <3 args should return None");
    });
}

// =============================================================================
// codegen_atomic_fetch_binop tests (Add, Sub, BitAnd, BitOr, BitXor)
// =============================================================================

/// Test atomic fetch_add returns target, assigns bv32 old value to dest, emits constraints.
#[test]
fn test_atomic_fetch_add_returns_target() {
    with_test_ay_ctx_for_source(ATOMIC_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "atomic_binop_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_atomic_args(&mut codegen, &body);

        let ptr_place = Place { local: 1, projection: vec![] };
        let operand_place = Place { local: 2, projection: vec![] };
        let args = vec![Operand::Copy(ptr_place), Operand::Copy(operand_place)];
        let dest = Place { local: 0, projection: vec![] };
        let pre_constraints = constraint_count(&codegen);

        let result = codegen.codegen_atomic_fetch_binop(&args, &dest, Some(4), BinOp::Add);
        assert_eq!(result, Some(4), "atomic fetch_add should return target block");

        // Verify destination assigned with old value (bv32)
        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("fetch_add should assign old value to destination");
        assert_eq!(
            dest_expr.sort().bitvec_width(),
            Some(32),
            "fetch_add old value should be bv32 for u32"
        );
        // Verify constraints emitted: load + SSA assign + store
        assert!(
            constraint_count(&codegen) > pre_constraints,
            "fetch_add should emit load, assignment, and store constraints"
        );
        // Verify memory model contains bvadd operation from the store
        let mem = codegen.ctx.memory().to_string();
        assert!(
            mem.contains("bvadd"),
            "fetch_add should store bvadd(old, operand) to memory, got {mem}"
        );
    });
}

/// Test atomic fetch_sub returns target, assigns bv32 dest, emits constraints.
#[test]
fn test_atomic_fetch_sub_returns_target() {
    with_test_ay_ctx_for_source(ATOMIC_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "atomic_binop_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_atomic_args(&mut codegen, &body);

        let ptr_place = Place { local: 1, projection: vec![] };
        let operand_place = Place { local: 2, projection: vec![] };
        let args = vec![Operand::Copy(ptr_place), Operand::Copy(operand_place)];
        let dest = Place { local: 0, projection: vec![] };
        let pre_constraints = constraint_count(&codegen);

        let result = codegen.codegen_atomic_fetch_binop(&args, &dest, Some(4), BinOp::Sub);
        assert_eq!(result, Some(4), "atomic fetch_sub should return target block");

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("fetch_sub should assign old value to destination");
        assert_eq!(
            dest_expr.sort().bitvec_width(),
            Some(32),
            "fetch_sub old value should be bv32 for u32"
        );
        assert!(constraint_count(&codegen) > pre_constraints, "fetch_sub should emit constraints");
        // Verify memory model contains bvsub operation from the store
        let mem = codegen.ctx.memory().to_string();
        assert!(
            mem.contains("bvsub"),
            "fetch_sub should store bvsub(old, operand) to memory, got {mem}"
        );
    });
}

/// Test atomic fetch_and (bitwise AND) returns target, assigns bv32 dest.
#[test]
fn test_atomic_fetch_and_returns_target() {
    with_test_ay_ctx_for_source(ATOMIC_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "atomic_binop_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_atomic_args(&mut codegen, &body);

        let ptr_place = Place { local: 1, projection: vec![] };
        let operand_place = Place { local: 2, projection: vec![] };
        let args = vec![Operand::Copy(ptr_place), Operand::Copy(operand_place)];
        let dest = Place { local: 0, projection: vec![] };
        let pre_constraints = constraint_count(&codegen);

        let result = codegen.codegen_atomic_fetch_binop(&args, &dest, Some(4), BinOp::BitAnd);
        assert_eq!(result, Some(4), "atomic fetch_and should return target block");

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("fetch_and should assign old value to destination");
        assert_eq!(
            dest_expr.sort().bitvec_width(),
            Some(32),
            "fetch_and old value should be bv32 for u32"
        );
        assert!(constraint_count(&codegen) > pre_constraints, "fetch_and should emit constraints");
        // Verify memory model contains bvand operation from the store
        let mem = codegen.ctx.memory().to_string();
        assert!(
            mem.contains("bvand"),
            "fetch_and should store bvand(old, operand) to memory, got {mem}"
        );
    });
}

/// Test atomic fetch_or (bitwise OR) returns target, assigns bv32 dest.
#[test]
fn test_atomic_fetch_or_returns_target() {
    with_test_ay_ctx_for_source(ATOMIC_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "atomic_binop_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_atomic_args(&mut codegen, &body);

        let ptr_place = Place { local: 1, projection: vec![] };
        let operand_place = Place { local: 2, projection: vec![] };
        let args = vec![Operand::Copy(ptr_place), Operand::Copy(operand_place)];
        let dest = Place { local: 0, projection: vec![] };
        let pre_constraints = constraint_count(&codegen);

        let result = codegen.codegen_atomic_fetch_binop(&args, &dest, Some(4), BinOp::BitOr);
        assert_eq!(result, Some(4), "atomic fetch_or should return target block");

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("fetch_or should assign old value to destination");
        assert_eq!(
            dest_expr.sort().bitvec_width(),
            Some(32),
            "fetch_or old value should be bv32 for u32"
        );
        assert!(constraint_count(&codegen) > pre_constraints, "fetch_or should emit constraints");
        // Verify memory model contains bvor operation from the store
        let mem = codegen.ctx.memory().to_string();
        assert!(
            mem.contains("bvor"),
            "fetch_or should store bvor(old, operand) to memory, got {mem}"
        );
    });
}

/// Test atomic fetch_xor (bitwise XOR) returns target, assigns bv32 dest.
#[test]
fn test_atomic_fetch_xor_returns_target() {
    with_test_ay_ctx_for_source(ATOMIC_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "atomic_binop_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_atomic_args(&mut codegen, &body);

        let ptr_place = Place { local: 1, projection: vec![] };
        let operand_place = Place { local: 2, projection: vec![] };
        let args = vec![Operand::Copy(ptr_place), Operand::Copy(operand_place)];
        let dest = Place { local: 0, projection: vec![] };
        let pre_constraints = constraint_count(&codegen);

        let result = codegen.codegen_atomic_fetch_binop(&args, &dest, Some(4), BinOp::BitXor);
        assert_eq!(result, Some(4), "atomic fetch_xor should return target block");

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("fetch_xor should assign old value to destination");
        assert_eq!(
            dest_expr.sort().bitvec_width(),
            Some(32),
            "fetch_xor old value should be bv32 for u32"
        );
        assert!(constraint_count(&codegen) > pre_constraints, "fetch_xor should emit constraints");
        // Verify memory model contains bvxor operation from the store
        let mem = codegen.ctx.memory().to_string();
        assert!(
            mem.contains("bvxor"),
            "fetch_xor should store bvxor(old, operand) to memory, got {mem}"
        );
    });
}

/// Test atomic fetch_binop with insufficient args returns None.
#[test]
fn test_atomic_fetch_binop_insufficient_args_returns_none() {
    with_test_ay_ctx_for_source(ATOMIC_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "atomic_load_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_atomic_fetch_binop(&[], &dest, Some(4), BinOp::Add);
        assert_eq!(result, None, "atomic fetch_binop with <2 args should return None");
    });
}

// =============================================================================
// codegen_atomic_fetch_nand tests
// =============================================================================

/// Test atomic fetch_nand returns target, assigns bv32 old value, emits constraints.
#[test]
fn test_atomic_fetch_nand_returns_target() {
    with_test_ay_ctx_for_source(ATOMIC_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "atomic_binop_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_atomic_args(&mut codegen, &body);

        let ptr_place = Place { local: 1, projection: vec![] };
        let operand_place = Place { local: 2, projection: vec![] };
        let args = vec![Operand::Copy(ptr_place), Operand::Copy(operand_place)];
        let dest = Place { local: 0, projection: vec![] };
        let pre_constraints = constraint_count(&codegen);

        let result = codegen.codegen_atomic_fetch_nand(&args, &dest, Some(6));
        assert_eq!(result, Some(6), "atomic fetch_nand should return target block");

        // Verify destination assigned with old value (bv32)
        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("fetch_nand should assign old value to destination");
        assert_eq!(
            dest_expr.sort().bitvec_width(),
            Some(32),
            "fetch_nand old value should be bv32 for u32"
        );
        // Verify constraints emitted: load + SSA assign + NAND store
        assert!(
            constraint_count(&codegen) > pre_constraints,
            "fetch_nand should emit load, assignment, and store constraints"
        );
        // Verify memory model contains NAND pattern: bvnot(bvand(...))
        let mem = codegen.ctx.memory().to_string();
        assert!(
            mem.contains("bvnot"),
            "fetch_nand should store bvnot(bvand(old, operand)) to memory, got {mem}"
        );
        assert!(
            mem.contains("bvand"),
            "fetch_nand NAND composition should include bvand, got {mem}"
        );
    });
}

/// Test atomic fetch_nand with insufficient args returns None.
#[test]
fn test_atomic_fetch_nand_insufficient_args_returns_none() {
    with_test_ay_ctx_for_source(ATOMIC_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "atomic_load_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_atomic_fetch_nand(&[], &dest, Some(6));
        assert_eq!(result, None, "atomic fetch_nand with <2 args should return None");
    });
}

// =============================================================================
// codegen_atomic_fetch_minmax tests
// =============================================================================

/// Test atomic signed max returns target, assigns bv32 old value, emits constraints.
#[test]
fn test_atomic_fetch_max_signed_returns_target() {
    with_test_ay_ctx_for_source(ATOMIC_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "atomic_binop_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_atomic_args(&mut codegen, &body);

        let ptr_place = Place { local: 1, projection: vec![] };
        let operand_place = Place { local: 2, projection: vec![] };
        let args = vec![Operand::Copy(ptr_place), Operand::Copy(operand_place)];
        let dest = Place { local: 0, projection: vec![] };
        let pre_constraints = constraint_count(&codegen);

        let result = codegen.codegen_atomic_fetch_minmax(&args, &dest, Some(8), true, true);
        assert_eq!(result, Some(8), "atomic signed max should return target block");

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("signed max should assign old value to destination");
        assert_eq!(
            dest_expr.sort().bitvec_width(),
            Some(32),
            "signed max old value should be bv32 for u32"
        );
        assert!(constraint_count(&codegen) > pre_constraints, "signed max should emit constraints");
        // Verify memory model contains signed greater-than comparison (bvsgt) in ITE
        let mem = codegen.ctx.memory().to_string();
        assert!(mem.contains("bvsgt"), "signed max should use bvsgt comparison, got {mem}");
        assert!(
            mem.contains("ite"),
            "signed max should use ITE for conditional selection, got {mem}"
        );
    });
}

/// Test atomic signed min returns target, assigns bv32 old value.
#[test]
fn test_atomic_fetch_min_signed_returns_target() {
    with_test_ay_ctx_for_source(ATOMIC_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "atomic_binop_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_atomic_args(&mut codegen, &body);

        let ptr_place = Place { local: 1, projection: vec![] };
        let operand_place = Place { local: 2, projection: vec![] };
        let args = vec![Operand::Copy(ptr_place), Operand::Copy(operand_place)];
        let dest = Place { local: 0, projection: vec![] };
        let pre_constraints = constraint_count(&codegen);

        let result = codegen.codegen_atomic_fetch_minmax(&args, &dest, Some(8), false, true);
        assert_eq!(result, Some(8), "atomic signed min should return target block");

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("signed min should assign old value to destination");
        assert_eq!(
            dest_expr.sort().bitvec_width(),
            Some(32),
            "signed min old value should be bv32 for u32"
        );
        assert!(constraint_count(&codegen) > pre_constraints, "signed min should emit constraints");
        // Verify memory model contains signed less-than comparison (bvslt) in ITE
        let mem = codegen.ctx.memory().to_string();
        assert!(mem.contains("bvslt"), "signed min should use bvslt comparison, got {mem}");
        assert!(
            mem.contains("ite"),
            "signed min should use ITE for conditional selection, got {mem}"
        );
    });
}

/// Test atomic unsigned max returns target, assigns bv32 old value.
#[test]
fn test_atomic_fetch_max_unsigned_returns_target() {
    with_test_ay_ctx_for_source(ATOMIC_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "atomic_binop_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_atomic_args(&mut codegen, &body);

        let ptr_place = Place { local: 1, projection: vec![] };
        let operand_place = Place { local: 2, projection: vec![] };
        let args = vec![Operand::Copy(ptr_place), Operand::Copy(operand_place)];
        let dest = Place { local: 0, projection: vec![] };
        let pre_constraints = constraint_count(&codegen);

        let result = codegen.codegen_atomic_fetch_minmax(&args, &dest, Some(8), true, false);
        assert_eq!(result, Some(8), "atomic unsigned max should return target block");

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("unsigned max should assign old value to destination");
        assert_eq!(
            dest_expr.sort().bitvec_width(),
            Some(32),
            "unsigned max old value should be bv32 for u32"
        );
        assert!(
            constraint_count(&codegen) > pre_constraints,
            "unsigned max should emit constraints"
        );
        // Verify memory model contains unsigned greater-than comparison (bvugt) in ITE
        let mem = codegen.ctx.memory().to_string();
        assert!(mem.contains("bvugt"), "unsigned max should use bvugt comparison, got {mem}");
        assert!(
            mem.contains("ite"),
            "unsigned max should use ITE for conditional selection, got {mem}"
        );
    });
}

/// Test atomic unsigned min returns target, assigns bv32 old value.
#[test]
fn test_atomic_fetch_min_unsigned_returns_target() {
    with_test_ay_ctx_for_source(ATOMIC_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "atomic_binop_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_atomic_args(&mut codegen, &body);

        let ptr_place = Place { local: 1, projection: vec![] };
        let operand_place = Place { local: 2, projection: vec![] };
        let args = vec![Operand::Copy(ptr_place), Operand::Copy(operand_place)];
        let dest = Place { local: 0, projection: vec![] };
        let pre_constraints = constraint_count(&codegen);

        let result = codegen.codegen_atomic_fetch_minmax(&args, &dest, Some(8), false, false);
        assert_eq!(result, Some(8), "atomic unsigned min should return target block");

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("unsigned min should assign old value to destination");
        assert_eq!(
            dest_expr.sort().bitvec_width(),
            Some(32),
            "unsigned min old value should be bv32 for u32"
        );
        assert!(
            constraint_count(&codegen) > pre_constraints,
            "unsigned min should emit constraints"
        );
        // Verify memory model contains unsigned less-than comparison (bvult) in ITE
        let mem = codegen.ctx.memory().to_string();
        assert!(mem.contains("bvult"), "unsigned min should use bvult comparison, got {mem}");
        assert!(
            mem.contains("ite"),
            "unsigned min should use ITE for conditional selection, got {mem}"
        );
    });
}

/// Test atomic fetch_minmax with insufficient args returns None.
#[test]
fn test_atomic_fetch_minmax_insufficient_args_returns_none() {
    with_test_ay_ctx_for_source(ATOMIC_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "atomic_load_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_atomic_fetch_minmax(&[], &dest, Some(8), true, true);
        assert_eq!(result, None, "atomic fetch_minmax with <2 args should return None");
    });
}

// =============================================================================
// Cross-width tests: Verify atomics work with u8 and u64 types
// =============================================================================

/// Test atomic load with u8 pointer type assigns bv8 destination.
#[test]
fn test_atomic_load_u8_returns_target() {
    with_test_ay_ctx_for_source(ATOMIC_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "atomic_u8_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_atomic_args(&mut codegen, &body);

        let ptr_place = Place { local: 1, projection: vec![] };
        let args = vec![Operand::Copy(ptr_place)];
        let dest = Place { local: 0, projection: vec![] };

        let result = codegen.codegen_atomic_load(&args, &dest, Some(20));
        assert_eq!(result, Some(20), "atomic_load with u8 pointer should return target");

        // Verify destination sort matches u8 width
        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("atomic_load u8 should assign destination");
        assert_eq!(
            dest_expr.sort().bitvec_width(),
            Some(8),
            "atomic_load of *mut u8 should produce bv8 destination"
        );
    });
}

/// Test atomic load with u64 pointer type assigns bv64 destination.
#[test]
fn test_atomic_load_u64_returns_target() {
    with_test_ay_ctx_for_source(ATOMIC_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "atomic_u64_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_atomic_args(&mut codegen, &body);

        let ptr_place = Place { local: 1, projection: vec![] };
        let args = vec![Operand::Copy(ptr_place)];
        let dest = Place { local: 0, projection: vec![] };

        let result = codegen.codegen_atomic_load(&args, &dest, Some(21));
        assert_eq!(result, Some(21), "atomic_load with u64 pointer should return target");

        // Verify destination sort matches u64 width
        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("atomic_load u64 should assign destination");
        assert_eq!(
            dest_expr.sort().bitvec_width(),
            Some(64),
            "atomic_load of *mut u64 should produce bv64 destination"
        );
    });
}

/// Test atomic store with u8 pointer type modifies the memory model.
#[test]
fn test_atomic_store_u8_returns_target() {
    with_test_ay_ctx_for_source(ATOMIC_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "atomic_u8_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_atomic_args(&mut codegen, &body);

        let ptr_place = Place { local: 1, projection: vec![] };
        let val_place = Place { local: 2, projection: vec![] };
        let args = vec![Operand::Copy(ptr_place), Operand::Copy(val_place)];
        let mem_before = codegen.ctx.memory().to_string();

        let result = codegen.codegen_atomic_store(&args, Some(22));
        assert_eq!(result, Some(22), "atomic_store with u8 pointer should return target");

        // Verify memory model was mutated
        let mem_after = codegen.ctx.memory().to_string();
        assert_ne!(mem_before, mem_after, "atomic_store u8 should modify the memory model");
    });
}

/// Test atomic fetch_add with u64 width assigns bv64 destination.
#[test]
fn test_atomic_fetch_add_u64_returns_target() {
    with_test_ay_ctx_for_source(ATOMIC_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "atomic_u64_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_atomic_args(&mut codegen, &body);

        let ptr_place = Place { local: 1, projection: vec![] };
        let operand_place = Place { local: 2, projection: vec![] };
        let args = vec![Operand::Copy(ptr_place), Operand::Copy(operand_place)];
        let dest = Place { local: 0, projection: vec![] };
        let pre_constraints = constraint_count(&codegen);

        let result = codegen.codegen_atomic_fetch_binop(&args, &dest, Some(23), BinOp::Add);
        assert_eq!(result, Some(23), "atomic fetch_add with u64 should return target");

        // Verify destination sort matches u64 width
        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("fetch_add u64 should assign destination");
        assert_eq!(
            dest_expr.sort().bitvec_width(),
            Some(64),
            "fetch_add of u64 should produce bv64 destination"
        );
        assert!(
            constraint_count(&codegen) > pre_constraints,
            "fetch_add u64 should emit constraints"
        );
    });
}

/// Test atomic fetch_nand with u8 width assigns bv8 destination.
#[test]
fn test_atomic_fetch_nand_u8_returns_target() {
    with_test_ay_ctx_for_source(ATOMIC_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "atomic_u8_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_atomic_args(&mut codegen, &body);

        let ptr_place = Place { local: 1, projection: vec![] };
        let operand_place = Place { local: 2, projection: vec![] };
        let args = vec![Operand::Copy(ptr_place), Operand::Copy(operand_place)];
        let dest = Place { local: 0, projection: vec![] };
        let pre_constraints = constraint_count(&codegen);

        let result = codegen.codegen_atomic_fetch_nand(&args, &dest, Some(24));
        assert_eq!(result, Some(24), "atomic fetch_nand with u8 should return target");

        // Verify destination sort matches u8 width
        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("fetch_nand u8 should assign destination");
        assert_eq!(
            dest_expr.sort().bitvec_width(),
            Some(8),
            "fetch_nand of u8 should produce bv8 destination"
        );
        assert!(
            constraint_count(&codegen) > pre_constraints,
            "fetch_nand u8 should emit constraints"
        );
    });
}
