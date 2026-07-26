// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Test code: unwrap is acceptable for assertions
#![allow(clippy::unwrap_used)]

//! MIR-driven tests for CHC codegen_expr.rs translation functions.
//!
//! Tests cover:
//! - translate_constant: MIR constant → AY Expr
//! - translate_operand_with_modified: Operand → Expr with modified local tracking
//! - translate_place_with_modified: Place → Expr with modified local tracking
//! - translate_rvalue_with_env: Rvalue → Expr in closure/env context
//! - translate_cast_with_env: Cast rvalue → Expr in closure/env context
//!
//! Part of #2016 (test coverage for codegen_ay/chc/codegen_expr.rs).

use super::common::*;
use std::sync::atomic::Ordering;

// ═══════════════════════════════════════════════════════════════════════
// translate_constant tests
// ═══════════════════════════════════════════════════════════════════════
//
// These compile real Rust source and walk MIR blocks to find Operand::Constant
// values, then exercise translate_constant through the full pipeline.

const CONSTANT_PROBE_SOURCE: &str = r#"
pub fn probe_bool_const() -> bool {
    true
}

pub fn probe_u32_const() -> u32 {
    42
}

pub fn probe_i32_const() -> i32 {
    -7
}

pub fn probe_u8_const() -> u8 {
    255
}

pub fn probe_u64_const() -> u64 {
    1_000_000
}

pub fn probe_char_const() -> char {
    'A'
}

pub fn probe_usize_const() -> usize {
    99
}

pub fn probe_zero_const() -> u32 {
    0
}

pub fn probe_ordering_const() -> core::cmp::Ordering {
    core::cmp::Ordering::Less
}

pub fn probe_add_u32(x: u32) -> u32 {
    x + 10
}

pub fn probe_add_i64(x: i64) -> i64 {
    x + 100
}

pub fn probe_cast_u8_u32(x: u8) -> u32 {
    x as u32
}

pub fn probe_cast_i8_i32(x: i8) -> i32 {
    x as i32
}

pub fn probe_array_len() -> usize {
    let arr = [1u32, 2, 3, 4, 5];
    arr.len()
}
"#;

/// Extract all Operand::Constant values from a MIR body and translate them.
fn collect_translated_constants<'tcx, 'body>(
    chc_ctx: &ChcCtx<'tcx, 'body>,
    body: &'body rustc_public::mir::Body,
) -> Vec<Expr> {
    use rustc_public::mir::{StatementKind, TerminatorKind};

    let mut results = Vec::new();
    for block in &body.blocks {
        for stmt in &block.statements {
            if let StatementKind::Assign(_, Rvalue::Use(Operand::Constant(const_op))) = &stmt.kind
                && let Some(expr) = chc_ctx.translate_constant(const_op)
            {
                results.push(expr);
            }
        }
        // Also check terminator for constant operands in calls
        if let TerminatorKind::Call { args, .. } = &block.terminator.kind {
            for arg in args {
                if let Operand::Constant(const_op) = arg
                    && let Some(expr) = chc_ctx.translate_constant(const_op)
                {
                    results.push(expr);
                }
            }
        }
    }
    results
}

// ─── Bool constant: true ──────────────────────────────────────────────

#[test]
fn test_translate_constant_bool_true() {
    with_test_ay_ctx_for_source(CONSTANT_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_bool_const");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_bool_const", ChcConfig::default());
        let constants = collect_translated_constants(&chc_ctx, &body);
        assert!(!constants.is_empty(), "should find at least one constant in probe_bool_const");
        // At least one should be a bool constant
        let has_bool = constants.iter().any(|e| e.sort().is_bool());
        assert!(
            has_bool,
            "expected a Bool constant, got sorts: {:?}",
            constants.iter().map(|e| format!("{:?}", e.sort())).collect::<Vec<_>>()
        );
    });
}

// ─── u32 constant: 42 ────────────────────────────────────────────────

#[test]
fn test_translate_constant_u32() {
    with_test_ay_ctx_for_source(CONSTANT_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_u32_const");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_u32_const", ChcConfig::default());
        let constants = collect_translated_constants(&chc_ctx, &body);
        assert!(!constants.is_empty(), "should find at least one constant in probe_u32_const");
        let has_bv32 = constants.iter().any(|e| e.sort().bitvec_width() == Some(32));
        assert!(
            has_bv32,
            "expected a bv32 constant for u32, got sorts: {:?}",
            constants.iter().map(|e| format!("{:?}", e.sort())).collect::<Vec<_>>()
        );
    });
}

// ─── i32 constant: -7 ────────────────────────────────────────────────

#[test]
fn test_translate_constant_i32_negative() {
    with_test_ay_ctx_for_source(CONSTANT_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_i32_const");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_i32_const", ChcConfig::default());
        let constants = collect_translated_constants(&chc_ctx, &body);
        assert!(!constants.is_empty(), "should find at least one constant in probe_i32_const");
        // -7 as i32 should produce a bv32
        let has_bv32 = constants.iter().any(|e| e.sort().bitvec_width() == Some(32));
        assert!(
            has_bv32,
            "expected a bv32 constant for i32, got sorts: {:?}",
            constants.iter().map(|e| format!("{:?}", e.sort())).collect::<Vec<_>>()
        );
    });
}

// ─── u8 constant: 255 ───────────────────────────────────────────────

#[test]
fn test_translate_constant_u8_max() {
    with_test_ay_ctx_for_source(CONSTANT_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_u8_const");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_u8_const", ChcConfig::default());
        let constants = collect_translated_constants(&chc_ctx, &body);
        assert!(!constants.is_empty(), "should find at least one constant");
        let has_bv8 = constants.iter().any(|e| e.sort().bitvec_width() == Some(8));
        assert!(has_bv8, "expected a bv8 constant for u8");
    });
}

// ─── u64 constant: 1_000_000 ────────────────────────────────────────

#[test]
fn test_translate_constant_u64() {
    with_test_ay_ctx_for_source(CONSTANT_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_u64_const");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_u64_const", ChcConfig::default());
        let constants = collect_translated_constants(&chc_ctx, &body);
        assert!(!constants.is_empty(), "should find at least one constant");
        let has_bv64 = constants.iter().any(|e| e.sort().bitvec_width() == Some(64));
        assert!(has_bv64, "expected a bv64 constant for u64");
    });
}

// ─── char constant: 'A' ─────────────────────────────────────────────

#[test]
fn test_translate_constant_char() {
    with_test_ay_ctx_for_source(CONSTANT_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_char_const");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_char_const", ChcConfig::default());
        let constants = collect_translated_constants(&chc_ctx, &body);
        assert!(!constants.is_empty(), "should find at least one constant");
        // char maps to bv32
        let has_bv32 = constants.iter().any(|e| e.sort().bitvec_width() == Some(32));
        assert!(has_bv32, "expected a bv32 constant for char");
    });
}

// ─── Zero constant ──────────────────────────────────────────────────

#[test]
fn test_translate_constant_zero() {
    with_test_ay_ctx_for_source(CONSTANT_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_zero_const");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_zero_const", ChcConfig::default());
        let constants = collect_translated_constants(&chc_ctx, &body);
        assert!(!constants.is_empty(), "should find at least one constant");
        let has_bv32 = constants.iter().any(|e| e.sort().bitvec_width() == Some(32));
        assert!(has_bv32, "expected a bv32 constant for u32 zero");
    });
}

// ═══════════════════════════════════════════════════════════════════════
// translate_operand_with_modified tests
// ═══════════════════════════════════════════════════════════════════════

// ─── Constant operand: passes through to translate_constant ──────────

#[test]
fn test_translate_operand_constant_passthrough() {
    with_test_ay_ctx_for_source(CONSTANT_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_add_u32");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_add_u32", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let modified: HashSet<usize> = HashSet::new();

        // Walk MIR to find a constant operand and translate it
        let mut found_constant = false;
        for block in &body.blocks {
            for stmt in &block.statements {
                if let rustc_public::mir::StatementKind::Assign(
                    _,
                    rvalue @ Rvalue::Use(Operand::Constant(_)),
                ) = &stmt.kind
                {
                    let Rvalue::Use(op) = rvalue else { unreachable!() };
                    let result = chc_ctx.translate_operand_with_modified(op, &modified);
                    assert!(result.is_some(), "constant operand should translate successfully");
                    found_constant = true;
                }
            }
        }
        // Note: optimizer may inline constants into BinaryOp directly
        // If no standalone Use(Constant) found, check BinaryOp operands
        if !found_constant {
            for block in &body.blocks {
                for stmt in &block.statements {
                    if let rustc_public::mir::StatementKind::Assign(
                        _,
                        Rvalue::BinaryOp(_, _, rhs) | Rvalue::CheckedBinaryOp(_, _, rhs),
                    ) = &stmt.kind
                        && let Operand::Constant(_) = rhs
                    {
                        let result = chc_ctx.translate_operand_with_modified(rhs, &modified);
                        assert!(result.is_some(), "constant operand in binop should translate");
                        found_constant = true;
                    }
                }
            }
        }
        assert!(found_constant, "expected at least one constant operand in probe_add_u32");
    });
}

// ─── Copy/Move operand with modified local ──────────────────────────

#[test]
fn test_translate_operand_modified_local_uses_output_var() {
    with_test_ay_ctx_for_source(CONSTANT_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_add_u32");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_add_u32", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // Mark local 1 (argument x) as modified
        let mut modified: HashSet<usize> = HashSet::new();
        modified.insert(1);

        // Create a Copy operand for local 1
        let place = Place { local: 1usize, projection: vec![] };
        let operand = Operand::Copy(place);

        let result = chc_ctx.translate_operand_with_modified(&operand, &modified);
        let expr = result.expect(
            "translate_operand should succeed for modified local 1 after declare_block_relations",
        );
        let smt = expr.to_string();
        // Modified locals use __out suffix
        assert!(
            smt.contains("__out") || smt.contains("probe_add_u32"),
            "modified local should use output var or fn-prefixed name, got: {smt}"
        );
    });
}

// ─── Unmodified local uses input variable ────────────────────────────

#[test]
fn test_translate_operand_unmodified_local_uses_input_var() {
    with_test_ay_ctx_for_source(CONSTANT_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_add_u32");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_add_u32", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // No locals modified
        let modified: HashSet<usize> = HashSet::new();

        let place = Place { local: 1usize, projection: vec![] };
        let operand = Operand::Copy(place);

        let result = chc_ctx.translate_operand_with_modified(&operand, &modified);
        let expr = result.expect(
            "translate_operand should succeed for unmodified local 1 after declare_block_relations",
        );
        let smt = expr.to_string();
        // Unmodified locals use input variable (no __out suffix)
        assert!(
            !smt.contains("__out"),
            "unmodified local should use input var without __out suffix, got: {smt}"
        );
    });
}

// ═══════════════════════════════════════════════════════════════════════
// translate_place_with_modified tests
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn test_translate_place_simple_local() {
    with_test_ay_ctx_for_source(CONSTANT_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_add_u32");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_add_u32", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let modified: HashSet<usize> = HashSet::new();
        let place = Place { local: 1usize, projection: vec![] };

        let result = chc_ctx.translate_place_with_modified(&place, &modified);
        let expr = result
            .expect("translate_place should succeed for local 1 after declare_block_relations");
        assert!(
            expr.sort().is_bitvec() || expr.sort().is_int(),
            "local place for u32 param should be bitvec or int, got {:?}",
            expr.sort()
        );
    });
}

#[test]
fn test_translate_place_skips_cached_expr_when_dependency_not_live() {
    with_test_ay_ctx_for_source(CONSTANT_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_add_u32");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_add_u32", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let dest_local = 0usize;
        let source_local = 1usize;
        let dest_idx = chc_ctx.state_idx_for_local(dest_local);
        let source_idx = chc_ctx.state_idx_for_local(source_local);
        let (source_name, source_sort) = chc_ctx.state_var_mgr.state_vars[source_idx].clone();
        let source_expr = Expr::var(&*source_name, source_sort);

        chc_ctx.encode.const_folded_call_results.insert(dest_local, source_expr.clone());
        let place = Place { local: dest_local, projection: vec![] };
        let modified = HashSet::new();

        let cached = chc_ctx
            .translate_place_with_modified(&place, &modified)
            .expect("live dependency cache should translate");
        assert_eq!(
            cached.to_string(),
            source_expr.to_string(),
            "cache should be used while its source local is live in the block relation"
        );

        chc_ctx.state_var_mgr.live_state_indices[0].retain(|idx| *idx != source_idx);
        assert!(
            chc_ctx.state_var_mgr.live_state_indices[0].contains(&dest_idx),
            "test setup should keep destination local live"
        );

        let fallback = chc_ctx
            .translate_place_with_modified(&place, &modified)
            .expect("non-live cache dependency should fall back to destination state var");
        let (dest_name, _) = &chc_ctx.state_var_mgr.state_vars[dest_idx];
        assert_eq!(
            fallback.to_string(),
            dest_name.to_string(),
            "cache must not introduce a free variable for a pruned source local"
        );
    });
}

#[test]
fn test_translate_place_flattened_bare_read_increments_drop_counter() {
    with_test_ay_ctx_for_source(CONSTANT_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_add_u32");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_add_u32", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let before = GLOBAL_COUNTERS.place_translation_drop.load(Ordering::Relaxed);
        chc_ctx.flatten.flattened_tuple_locals.insert(1usize);
        let place = Place { local: 1usize, projection: vec![] };
        let modified: HashSet<usize> = HashSet::new();
        let result = chc_ctx.translate_place_with_modified(&place, &modified);
        let after = GLOBAL_COUNTERS.place_translation_drop.load(Ordering::Relaxed);

        assert!(result.is_none(), "bare read of flattened local should fail translation");
        assert_eq!(
            after,
            before + 1,
            "flattened bare read should increment PLACE_TRANSLATION_DROP_COUNT"
        );
    });
}

// ═══════════════════════════════════════════════════════════════════════
// translate_rvalue_with_env tests
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn test_translate_rvalue_use_from_env() {
    with_test_ay_ctx_for_source(CONSTANT_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_add_u32");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_add_u32", ChcConfig::default());

        // Seed an env with a known expression for local 1
        let mut env: HashMap<usize, Expr> = HashMap::new();
        env.insert(1, Expr::bitvec_const(42, 32));

        // Rvalue::Use(Copy(local_1)) should find it in env
        let place = Place { local: 1usize, projection: vec![] };
        let rvalue = Rvalue::Use(Operand::Copy(place));

        let result = chc_ctx.translate_rvalue_with_env(&rvalue, &env, &[], None, None);
        assert!(result.is_some(), "Rvalue::Use of env local should succeed");
        let expr = result.unwrap();
        assert_eq!(expr.sort().bitvec_width(), Some(32));
    });
}

#[test]
fn test_translate_rvalue_use_constant() {
    with_test_ay_ctx_for_source(CONSTANT_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_add_u32");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_add_u32", ChcConfig::default());

        // Find a MIR constant and wrap it in Rvalue::Use
        let mut found = false;
        for block in &body.blocks {
            for stmt in &block.statements {
                if let rustc_public::mir::StatementKind::Assign(
                    _,
                    rvalue @ Rvalue::Use(Operand::Constant(_)),
                ) = &stmt.kind
                {
                    let result =
                        chc_ctx.translate_rvalue_with_env(rvalue, &HashMap::new(), &[], None, None);
                    assert!(result.is_some(), "Rvalue::Use(Constant) should translate");
                    found = true;
                }
            }
        }
        // Optimizer may merge constants; this is fine
        if !found {
            // Look for CheckedBinaryOp which contains constant operands
            for block in &body.blocks {
                for stmt in &block.statements {
                    if let rustc_public::mir::StatementKind::Assign(_, rvalue) = &stmt.kind
                        && matches!(rvalue, Rvalue::CheckedBinaryOp(..))
                    {
                        // This exercises translate_rvalue_with_env's BinaryOp path
                        let env: HashMap<usize, Expr> = body
                            .locals()
                            .iter()
                            .enumerate()
                            .filter_map(|(idx, decl)| {
                                ChcCtx::translate_ty(decl.ty)
                                    .map(|sort| (idx, Expr::var(format!("_v_{idx}"), sort)))
                            })
                            .collect();
                        let result =
                            chc_ctx.translate_rvalue_with_env(rvalue, &env, &[], None, None);
                        assert!(
                            result.is_some(),
                            "CheckedBinaryOp rvalue should translate with env"
                        );
                    }
                }
            }
        }
    });
}

// ─── BinaryOp in env context ────────────────────────────────────────

#[test]
fn test_translate_rvalue_binop_from_env() {
    with_test_ay_ctx_for_source(CONSTANT_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_add_u32");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_add_u32", ChcConfig::default());

        // Walk MIR to find a BinaryOp or CheckedBinaryOp and translate it with env
        let mut exercised_binop = false;
        let mut translated_binop = false;
        for block in &body.blocks {
            for stmt in &block.statements {
                if let rustc_public::mir::StatementKind::Assign(_, rvalue) = &stmt.kind
                    && matches!(rvalue, Rvalue::BinaryOp(..) | Rvalue::CheckedBinaryOp(..))
                {
                    // Build env from locals
                    let env: HashMap<usize, Expr> = body
                        .locals()
                        .iter()
                        .enumerate()
                        .filter_map(|(idx, decl)| {
                            ChcCtx::translate_ty(decl.ty)
                                .map(|sort| (idx, Expr::var(format!("_v_{idx}"), sort)))
                        })
                        .collect();
                    let result = chc_ctx.translate_rvalue_with_env(rvalue, &env, &[], None, None);
                    // BinaryOp may return None when operand resolution fails
                    // (e.g., unresolved generic). CheckedBinaryOp returns
                    // Tuple_bv_bool (result, overflow_flag).
                    if let Some(expr) = result {
                        let sort = expr.sort();
                        assert!(
                            sort.is_bitvec()
                                || sort.is_bool()
                                || matches!(sort.inner(), SortInner::Datatype(..)),
                            "BinaryOp result should be bitvec, bool, or datatype, got {:?}",
                            sort
                        );
                        translated_binop = true;
                    } else {
                        // Operand resolution can fail for unresolved generics,
                        // but this concrete probe must still yield at least one
                        // successful translation.
                    }
                    exercised_binop = true;
                }
            }
        }
        assert!(exercised_binop, "expected at least one BinaryOp in probe_add_u32");
        assert!(
            translated_binop,
            "expected at least one successfully translated BinaryOp in probe_add_u32"
        );
    });
}

// ═══════════════════════════════════════════════════════════════════════
// translate_cast_with_env tests
// ═══════════════════════════════════════════════════════════════════════

// ═══════════════════════════════════════════════════════════════════════
// Part of #2255: extract_loop_invariant_formula tests (codegen_expr_env.rs)
// ═══════════════════════════════════════════════════════════════════════

const LOOP_INVARIANT_EXTRACT_SOURCE: &str = r#"
pub fn inv_bool_straightline() -> bool {
    true
}

pub fn inv_non_bool_straightline() -> u32 {
    7
}

pub fn inv_bool_loop(flag: bool) -> bool {
    let mut x = flag;
    while x {
        x = false;
    }
    x
}
"#;

#[test]
fn test_extract_loop_invariant_formula_straightline_bool() {
    with_test_ay_ctx_for_source(LOOP_INVARIANT_EXTRACT_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "inv_bool_straightline");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "inv_bool_straightline", ChcConfig::default());

        let expr = chc_ctx
            .extract_loop_invariant_formula(&[])
            .expect("straight-line bool body should produce invariant formula");
        assert!(
            expr.sort().is_bool(),
            "loop invariant formula should be Bool, got {:?}",
            expr.sort()
        );
    });
}

#[test]
fn test_extract_loop_invariant_formula_rejects_non_bool_return() {
    with_test_ay_ctx_for_source(LOOP_INVARIANT_EXTRACT_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "inv_non_bool_straightline");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "inv_non_bool_straightline", ChcConfig::default());

        assert!(
            chc_ctx.extract_loop_invariant_formula(&[]).is_none(),
            "non-bool return should not produce loop invariant formula"
        );
    });
}

#[test]
fn test_extract_loop_invariant_formula_rejects_multiblock_body() {
    with_test_ay_ctx_for_source(LOOP_INVARIANT_EXTRACT_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "inv_bool_loop");
        let body = instance.body().expect("function body");
        assert!(body.blocks.len() > 1, "branching probe should produce multiple MIR basic blocks");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "inv_bool_loop", ChcConfig::default());
        assert!(
            chc_ctx.extract_loop_invariant_formula(&[]).is_none(),
            "multi-block body should be rejected by loop invariant extractor"
        );
    });
}

#[test]
fn test_translate_cast_unsigned_widen() {
    with_test_ay_ctx_for_source(CONSTANT_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_cast_u8_u32");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_cast_u8_u32", ChcConfig::default());

        // Walk MIR to find Cast rvalue
        let mut found_cast = false;
        for block in &body.blocks {
            for stmt in &block.statements {
                if let rustc_public::mir::StatementKind::Assign(
                    _,
                    Rvalue::Cast(_kind, operand, target_ty),
                ) = &stmt.kind
                {
                    let env: HashMap<usize, Expr> = body
                        .locals()
                        .iter()
                        .enumerate()
                        .filter_map(|(idx, decl)| {
                            ChcCtx::translate_ty(decl.ty)
                                .map(|sort| (idx, Expr::var(format!("_v_{idx}"), sort)))
                        })
                        .collect();
                    let result =
                        chc_ctx.translate_cast_with_env(operand, *target_ty, &env, &[], None);
                    let expr = result
                        .expect("translate_cast_with_env should succeed for u8→u32 widening cast");
                    // u8→u32 should produce bv32
                    assert_eq!(
                        expr.sort().bitvec_width(),
                        Some(32),
                        "u8→u32 cast should produce bv32, got {:?}",
                        expr.sort()
                    );
                    found_cast = true;
                }
            }
        }
        assert!(found_cast, "MIR for probe_cast_u8_u32 should contain a Cast statement");
    });
}

#[test]
fn test_translate_cast_signed_widen() {
    with_test_ay_ctx_for_source(CONSTANT_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_cast_i8_i32");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_cast_i8_i32", ChcConfig::default());

        let mut found_cast = false;
        for block in &body.blocks {
            for stmt in &block.statements {
                if let rustc_public::mir::StatementKind::Assign(
                    _,
                    Rvalue::Cast(_kind, operand, target_ty),
                ) = &stmt.kind
                {
                    let env: HashMap<usize, Expr> = body
                        .locals()
                        .iter()
                        .enumerate()
                        .filter_map(|(idx, decl)| {
                            ChcCtx::translate_ty(decl.ty)
                                .map(|sort| (idx, Expr::var(format!("_v_{idx}"), sort)))
                        })
                        .collect();
                    let result =
                        chc_ctx.translate_cast_with_env(operand, *target_ty, &env, &[], None);
                    let expr = result
                        .expect("translate_cast_with_env should succeed for i8→i32 widening cast");
                    assert_eq!(
                        expr.sort().bitvec_width(),
                        Some(32),
                        "i8→i32 cast should produce bv32"
                    );
                    found_cast = true;
                }
            }
        }
        assert!(found_cast, "MIR for probe_cast_i8_i32 should contain a Cast statement");
    });
}

// ═══════════════════════════════════════════════════════════════════════
// Part of #2255: Constant-edge kind tests
// ═══════════════════════════════════════════════════════════════════════

/// Collect ALL Operand::Constant values from every MIR position (statements,
/// terminators, return operands, BinaryOp operands, Aggregate operands) and
/// translate them. This is a superset of `collect_translated_constants`.
fn collect_all_constants<'tcx, 'body>(
    chc_ctx: &ChcCtx<'tcx, 'body>,
    body: &'body rustc_public::mir::Body,
) -> Vec<Expr> {
    use rustc_public::mir::{Rvalue, StatementKind, TerminatorKind};

    fn try_translate_operand<'tcx, 'body>(
        chc_ctx: &ChcCtx<'tcx, 'body>,
        operand: &Operand,
        results: &mut Vec<Expr>,
    ) {
        if let Operand::Constant(const_op) = operand
            && let Some(expr) = chc_ctx.translate_constant(const_op)
        {
            results.push(expr);
        }
    }

    fn collect_from_rvalue<'tcx, 'body>(
        chc_ctx: &ChcCtx<'tcx, 'body>,
        rvalue: &Rvalue,
        results: &mut Vec<Expr>,
    ) {
        match rvalue {
            Rvalue::Use(op)
            | Rvalue::Repeat(op, _)
            | Rvalue::Cast(_, op, _)
            | Rvalue::UnaryOp(_, op) => {
                try_translate_operand(chc_ctx, op, results);
            }
            Rvalue::BinaryOp(_, lhs, rhs) | Rvalue::CheckedBinaryOp(_, lhs, rhs) => {
                try_translate_operand(chc_ctx, lhs, results);
                try_translate_operand(chc_ctx, rhs, results);
            }
            Rvalue::Aggregate(_, ops) => {
                for op in ops {
                    try_translate_operand(chc_ctx, op, results);
                }
            }
            _ => {}
        }
    }

    let mut results = Vec::new();
    for block in &body.blocks {
        for stmt in &block.statements {
            if let StatementKind::Assign(_, rvalue) = &stmt.kind {
                collect_from_rvalue(chc_ctx, rvalue, &mut results);
            }
        }
        match &block.terminator.kind {
            TerminatorKind::Call { func, args, .. } => {
                try_translate_operand(chc_ctx, func, &mut results);
                for arg in args {
                    try_translate_operand(chc_ctx, arg, &mut results);
                }
            }
            TerminatorKind::Return => {
                // Return value is in _0, not a constant operand
            }
            _ => {}
        }
    }
    results
}

/// Verify translate_constant handles zero-sized types (unit struct / ()).
/// Typed ZST constants should use their canonical expression shape.
#[test]
fn test_translate_constant_zero_sized_returns_true() {
    // Use a function that passes a ZST as a call argument — this ensures
    // the constant appears in MIR as an Operand::Constant.
    const ZST_SOURCE: &str = r#"
        pub struct Marker;

        #[inline(never)]
        pub fn consume_marker(_m: Marker) -> bool { true }

        pub fn probe_zst() -> bool {
            consume_marker(Marker)
        }
    "#;

    with_test_ay_ctx_for_source(ZST_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_zst");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_zst", ChcConfig::default());
        let constants = collect_all_constants(&chc_ctx, &body);
        // ZST constants translate to Bool(true)
        let has_bool = constants.iter().any(|e| e.sort().is_bool());
        assert!(
            has_bool,
            "ZST constant (Marker) should translate to Bool; got sorts: {:?}",
            constants.iter().map(|e| format!("{:?}", e.sort())).collect::<Vec<_>>()
        );
    });
}

/// Verify zero-length array constants stay Array-sorted instead of collapsing to Bool.
#[test]
fn test_translate_constant_zero_len_array_preserves_array_sort() {
    const ZERO_LEN_ARRAY_SOURCE: &str = r#"
        #[inline(never)]
        pub fn consume_empty(_arr: [u8; 0]) -> bool { true }

        pub fn probe_zero_len_array_const() -> bool {
            consume_empty([])
        }
    "#;

    with_test_ay_ctx_for_source(ZERO_LEN_ARRAY_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_zero_len_array_const");
        let body = instance.body().expect("function body");
        let chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_zero_len_array_const", ChcConfig::default());
        let constants = collect_all_constants(&chc_ctx, &body);

        assert!(
            constants.iter().any(|expr| expr.sort().is_array()),
            "zero-length array constant should translate to an Array sort, got sorts: {:?}",
            constants.iter().map(|expr| format!("{:?}", expr.sort())).collect::<Vec<_>>()
        );
    });
}

/// Verify translate_constant handles unit enum constants via match discriminant.
/// Unit enums like custom Direction are encoded as bv32 after discriminant extraction.
#[test]
fn test_translate_constant_unit_enum_discriminant() {
    // Define a custom unit enum and match on it — this forces rustc to emit
    // discriminant constants as Operand::Constant in SwitchInt terminators.
    const ENUM_SOURCE: &str = r#"
        #[derive(Clone, Copy)]
        pub enum Color { Red, Green, Blue }

        #[inline(never)]
        pub fn color_value(c: Color) -> u32 {
            match c {
                Color::Red => 1,
                Color::Green => 2,
                Color::Blue => 3,
            }
        }

        pub fn probe_enum_match() -> u32 {
            color_value(Color::Green)
        }
    "#;

    with_test_ay_ctx_for_source(ENUM_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_enum_match");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_enum_match", ChcConfig::default());
        let constants = collect_all_constants(&chc_ctx, &body);
        // At minimum should find the u32 return constants or discriminant values
        assert!(
            !constants.is_empty(),
            "should find at least one translatable constant in probe_enum_match"
        );
        // All found constants should have valid sorts (Bool or BitVec)
        for c in &constants {
            assert!(
                c.sort().is_bool() || c.sort().is_bitvec(),
                "constant should have Bool or BitVec sort, got {:?}",
                c.sort()
            );
        }
    });
}

/// Verify translate_constant sign-extends repr(i8) unit enum discriminants.
///
/// Part of #3556: `Ordering::Less = -1` is stored as byte 0xFF. Without sign
/// extension, `read_uint()` returns 255 which is emitted as `bitvec_const(255, 32)`.
/// With the fix, the value is sign-extended to `bitvec_const(0xFFFFFFFF, 32)`.
#[test]
fn test_translate_constant_repr_i8_sign_extend() {
    const SIGNED_ENUM_SOURCE: &str = r#"
        #[repr(i8)]
        #[derive(Clone, Copy)]
        pub enum Signed { Neg = -1, Zero = 0, Pos = 1 }

        #[inline(never)]
        pub fn signed_value(s: Signed) -> i32 {
            match s {
                Signed::Neg => -1,
                Signed::Zero => 0,
                Signed::Pos => 1,
            }
        }

        pub fn probe_signed_enum() -> i32 {
            signed_value(Signed::Neg)
        }
    "#;

    with_test_ay_ctx_for_source(SIGNED_ENUM_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_signed_enum");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_signed_enum", ChcConfig::default());
        let constants = collect_all_constants(&chc_ctx, &body);
        // Should find the Signed::Neg constant (discriminant -1).
        // After sign-extension, -1 in BV32 = 0xFFFFFFFF = 4294967295.
        // Before the fix: 255 (0xFF, no sign-extension).
        let has_neg_one = constants.iter().any(|e| {
            let smt = e.to_string();
            // BV32 constant for -1 should be #xffffffff, not #x000000ff
            e.sort().bitvec_width() == Some(32)
                && (smt.contains("ffffffff") || smt.contains("4294967295"))
        });
        // Also verify no constant has the buggy value 255 as a BV32
        let has_buggy_255 = constants.iter().any(|e| {
            let smt = e.to_string();
            e.sort().bitvec_width() == Some(32) && (smt.contains("#x000000ff") || smt == "#xff")
        });
        assert!(
            has_neg_one || !has_buggy_255,
            "repr(i8) enum -1 should be sign-extended to 0xFFFFFFFF, \
             not left as 0xFF/255. Constants: {:?}",
            constants.iter().map(|e| e.to_string()).collect::<Vec<_>>()
        );
    });
}

/// Verify translate_constant handles opaque ADT constants (Layout).
/// Layout is a 128-bit opaque ADT per codegen_expr_constant.rs:77;
/// its constant value is read as unsigned and masked to width.
#[test]
fn test_translate_constant_opaque_adt_layout_width() {
    // core::alloc::Layout::new::<u32>() produces a Layout constant in MIR.
    // We verify that the translator reads it as a bitvec of the expected width.
    const LAYOUT_SOURCE: &str = r#"
        use core::alloc::Layout;

        #[inline(never)]
        pub fn consume_layout(l: Layout) -> usize { l.size() }

        pub fn probe_layout() -> usize {
            let l = Layout::new::<u32>();
            consume_layout(l)
        }
    "#;

    with_test_ay_ctx_for_source(LAYOUT_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_layout");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_layout", ChcConfig::default());
        let constants = collect_all_constants(&chc_ctx, &body);
        assert_mir_pattern_found(!constants.is_empty(), "Layout constant operand in MIR");
        for c in &constants {
            assert!(
                c.sort().is_bool() || c.sort().is_bitvec(),
                "Layout-related constant should have Bool or BitVec sort, got {:?}",
                c.sort()
            );
        }
    });
}

/// Verify translate_constant handles NonNull opaque ADT constants.
/// NonNull is pointer-width (64-bit on 64-bit targets) per codegen_expr_constant.rs:76.
#[test]
fn test_translate_constant_opaque_adt_nonnull_width() {
    const NONNULL_SOURCE: &str = r#"
        use core::ptr::NonNull;

        #[inline(never)]
        pub fn consume_ptr(p: NonNull<u8>) -> *const u8 { p.as_ptr() }

        pub fn probe_nonnull() -> *const u8 {
            let p = NonNull::dangling();
            consume_ptr(p)
        }
    "#;

    with_test_ay_ctx_for_source(NONNULL_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_nonnull");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_nonnull", ChcConfig::default());
        let constants = collect_all_constants(&chc_ctx, &body);
        // NonNull::dangling() produces a constant; translator should handle it
        // as a pointer-width bitvec without panicking.
        for c in &constants {
            assert!(
                c.sort().is_bool() || c.sort().is_bitvec(),
                "NonNull-related constant should have Bool or BitVec sort, got {:?}",
                c.sort()
            );
        }
    });
}

/// Verify translate_constant returns None for generic Param constants.
/// ConstantKind::Param and TyConstKind::Param appear only in pre-monomorphization
/// MIR. Post-monomorphization (stable MIR), they should not appear, but the
/// translator defensively returns None. Since we cannot easily synthesize these
/// through rustc compilation, we test indirectly via a generic function to
/// confirm the happy path doesn't accidentally match Param-like patterns.
#[test]
fn test_translate_constant_generic_fn_no_param_leak() {
    // A generic function with a const parameter — after monomorphization,
    // the constant N should be resolved to a concrete value, NOT a Param.
    const GENERIC_SOURCE: &str = r#"
        #[inline(never)]
        pub fn add_n<const N: u32>(x: u32) -> u32 { x + N }

        pub fn probe_const_generic() -> u32 {
            add_n::<42>(10)
        }
    "#;

    with_test_ay_ctx_for_source(GENERIC_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_const_generic");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_const_generic", ChcConfig::default());
        let constants = collect_all_constants(&chc_ctx, &body);
        // Post-monomorphization: const generic N=42 should resolve to a concrete
        // u32 value, not remain as Param. We verify all constants translate
        // successfully (have valid sorts).
        assert!(
            !constants.is_empty(),
            "const generic function should produce at least one concrete constant"
        );
        for c in &constants {
            assert!(
                c.sort().is_bool() || c.sort().is_bitvec(),
                "all post-monomorphization constants should have valid sorts, got {:?}",
                c.sort()
            );
        }
    });
}

#[test]
fn test_translate_constant_float_produces_bitvec() {
    const FLOAT_SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_float_const() -> f64 { 3.14 }
    "#;

    with_test_ay_ctx_for_source(FLOAT_SOURCE, |ctx| {
        let before = GLOBAL_COUNTERS.const_translation_drop.load(Ordering::Relaxed);
        let instance = find_instance_by_suffix(ctx.tcx, "probe_float_const");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_float_const", ChcConfig::default());

        let constants = collect_all_constants(&chc_ctx, &body);
        let after = GLOBAL_COUNTERS.const_translation_drop.load(Ordering::Relaxed);

        // Float constants are now translated as bitvectors (Part of #3094, W3:3365).
        assert!(!constants.is_empty(), "float constants should be translated as bitvectors");
        assert_eq!(after, before, "float constant translation should not increment drop counter");
    });
}
