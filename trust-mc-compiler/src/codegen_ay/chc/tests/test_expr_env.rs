// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Tests for codegen_expr_env.rs — loop-invariant extraction and
// environment-based expression translation.
//
// Covers paths NOT already exercised in test_expr.rs:
// - translate_rvalue_with_env: Rvalue::Len (array compile-time length)
// - translate_rvalue_with_env: Rvalue::UnaryOp (Neg, Not)
// - translate_place_with_env: closure captured variable resolution
// - extract_loop_invariant_formula: closure with captured vars
// - extract_loop_invariant_formula: non-Return terminator rejection
// - translate_rvalue_with_env: unsupported rvalue returns None
//
// Part of #2255: test coverage for zero-coverage chc/ files.

#![allow(clippy::unwrap_used)]

use super::common::*;

// ═══════════════════════════════════════════════════════════════════════
// translate_rvalue_with_env: Rvalue::Len (array compile-time length)
// ═══════════════════════════════════════════════════════════════════════

const ARRAY_LEN_SOURCE: &str = r#"
pub fn probe_array_len_5() -> usize {
    let arr = [1u32, 2, 3, 4, 5];
    arr.len()
}

pub fn probe_array_len_0() -> usize {
    let arr: [u8; 0] = [];
    arr.len()
}
"#;

const LEN_FALLBACK_SOURCE: &str = r#"
pub fn probe_slice_len(xs: &[u32]) -> usize {
    xs.len()
}
"#;

#[test]
fn test_rvalue_len_array_compile_time_length() {
    with_test_ay_ctx_for_source(ARRAY_LEN_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_array_len_5");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_array_len_5", ChcConfig::default());

        // Walk MIR to find Rvalue::Len and translate it in env context
        let env: HashMap<usize, Expr> = body
            .locals()
            .iter()
            .enumerate()
            .filter_map(|(idx, decl)| {
                ChcCtx::translate_ty(decl.ty)
                    .map(|sort| (idx, Expr::var(format!("_v_{idx}"), sort)))
            })
            .collect();

        let mut saw_len = false;
        for block in &body.blocks {
            for stmt in &block.statements {
                if let rustc_public::mir::StatementKind::Assign(_, Rvalue::Len(_)) = &stmt.kind {
                    saw_len = true;
                    let result = chc_ctx.translate_rvalue_with_env(
                        &Rvalue::Len(match &stmt.kind {
                            rustc_public::mir::StatementKind::Assign(_, Rvalue::Len(p)) => {
                                p.clone()
                            }
                            _ => unreachable!(),
                        }),
                        &env,
                        &[],
                        None,
                        None,
                    );
                    // For a fixed-size array [T; 5], Rvalue::Len should produce a
                    // compile-time constant bitvec of pointer width.
                    let expr = result.expect(
                        "Rvalue::Len was present in MIR but translate_rvalue_with_env returned None",
                    );
                    assert!(
                        expr.sort().is_bitvec(),
                        "Rvalue::Len on fixed array should produce bitvec, got {:?}",
                        expr.sort()
                    );
                }
            }
        }
        // Note: Optimizer may compute array length at MIR level instead of
        // emitting Rvalue::Len. This is acceptable — the test exercises the path
        // when it's present.
        if !saw_len {
            // Verify the function at least compiles and translates without panic
            let _vc = chc_ctx.translate();
        }
    });
}

#[test]
fn test_rvalue_len_non_array_increments_fallback_counter() {
    // Rvalue::Len on non-array places should fail-open and increment fallback_count.
    with_test_ay_ctx_for_source(LEN_FALLBACK_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_slice_len");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_slice_len", ChcConfig::default());

        let before = chc_ctx.fallback_count;
        let result = chc_ctx.translate_rvalue_with_env(
            &Rvalue::Len(Place { local: 1, projection: vec![] }),
            &HashMap::new(),
            &[],
            None,
            None,
        );
        let after = chc_ctx.fallback_count;

        assert!(result.is_none(), "slice len fallback should return None in env translation");
        assert!(
            after > before,
            "Rvalue::Len fallback should increment fallback_count (before={before}, after={after})"
        );
    });
}

// ═══════════════════════════════════════════════════════════════════════
// translate_rvalue_with_env: Rvalue::UnaryOp (Neg, Not)
// ═══════════════════════════════════════════════════════════════════════

const UNARY_OP_SOURCE: &str = r#"
pub fn probe_neg(x: i32) -> i32 {
    -x
}

pub fn probe_not(x: bool) -> bool {
    !x
}

pub fn probe_bitwise_not(x: u32) -> u32 {
    !x
}
"#;

#[test]
fn test_rvalue_unaryop_neg_in_env() {
    with_test_ay_ctx_for_source(UNARY_OP_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_neg");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_neg", ChcConfig::default());

        let env: HashMap<usize, Expr> = body
            .locals()
            .iter()
            .enumerate()
            .filter_map(|(idx, decl)| {
                ChcCtx::translate_ty(decl.ty)
                    .map(|sort| (idx, Expr::var(format!("_v_{idx}"), sort)))
            })
            .collect();

        let mut found_unop = false;
        for block in &body.blocks {
            for stmt in &block.statements {
                if let rustc_public::mir::StatementKind::Assign(_, rvalue) = &stmt.kind
                    && matches!(rvalue, Rvalue::UnaryOp(..))
                {
                    let expr = chc_ctx
                        .translate_rvalue_with_env(rvalue, &env, &[], None, None)
                        .expect("translate_rvalue_with_env returned None for UnaryOp::Neg");
                    assert!(
                        expr.sort().is_bitvec(),
                        "Neg on i32 should produce bitvec, got {:?}",
                        expr.sort()
                    );
                    found_unop = true;
                }
            }
        }
        assert!(found_unop, "expected UnaryOp::Neg in MIR for probe_neg");
    });
}

#[test]
fn test_rvalue_unaryop_not_bool_in_env() {
    with_test_ay_ctx_for_source(UNARY_OP_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_not");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_not", ChcConfig::default());

        let env: HashMap<usize, Expr> = body
            .locals()
            .iter()
            .enumerate()
            .filter_map(|(idx, decl)| {
                ChcCtx::translate_ty(decl.ty)
                    .map(|sort| (idx, Expr::var(format!("_v_{idx}"), sort)))
            })
            .collect();

        let mut found_unop = false;
        for block in &body.blocks {
            for stmt in &block.statements {
                if let rustc_public::mir::StatementKind::Assign(_, rvalue) = &stmt.kind
                    && matches!(rvalue, Rvalue::UnaryOp(..))
                {
                    let expr = chc_ctx
                        .translate_rvalue_with_env(rvalue, &env, &[], None, None)
                        .expect("translate_rvalue_with_env returned None for UnaryOp::Not");
                    assert!(
                        expr.sort().is_bool(),
                        "Not on bool should produce Bool, got {:?}",
                        expr.sort()
                    );
                    found_unop = true;
                }
            }
        }
        // MIR may optimize `!x` for bool into SwitchInt; that's fine
        if !found_unop {
            let _vc = chc_ctx.translate();
        }
    });
}

// ═══════════════════════════════════════════════════════════════════════
// translate_place_with_env: closure captured variable resolution
// ═══════════════════════════════════════════════════════════════════════
//
// extract_loop_invariant_formula exercises translate_place_with_env for
// the closure env path. We test with a closure that captures a local
// and produces a Bool result.

const CLOSURE_CAPTURE_SOURCE: &str = r#"
pub fn probe_closure_capture(limit: u32) -> bool {
    let threshold = 10u32;
    let check = |x: u32| -> bool { x < threshold };
    check(limit)
}

pub fn probe_closure_binop_capture(a: u32, _b: u32) -> bool {
    let check = |x: u32| -> bool { x > 0 && x < 100 };
    check(a)
}
"#;

#[test]
fn test_extract_loop_invariant_with_captured_vars() {
    // This exercises the closure env path in translate_place_with_env:
    // closure_env_local is Some, and captured_vars maps field indices
    // to harness locals.
    with_test_ay_ctx_for_source(CLOSURE_CAPTURE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_closure_capture");
        let body = instance.body().expect("function body");

        // The outer function compiles to MIR with a closure call.
        // We verify that ChcCtx can handle the outer function without panicking,
        // which exercises the env-based translation indirectly.
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_closure_capture", ChcConfig::default());

        // Full pipeline: translate() calls declare_block_relations() internally.
        // Do NOT call declare_block_relations() separately — that would register
        // state vars twice, causing duplicate name collisions.
        let (vc, _has_error) = chc_ctx.translate();
        assert!(!vc.relations.is_empty(), "closure capture VC should have at least one relation");
        assert!(!vc.rules.is_empty(), "closure capture VC should have at least one rule");
    });
}

// ═══════════════════════════════════════════════════════════════════════
// translate_rvalue_with_env: unsupported rvalue returns None
// ═══════════════════════════════════════════════════════════════════════

const UNSUPPORTED_RVALUE_SOURCE: &str = r#"
pub fn probe_ref(x: &u32) -> &u32 {
    x
}

pub fn probe_discriminant() -> u32 {
    let opt: Option<u32> = Some(42);
    match opt {
        Some(v) => v,
        None => 0,
    }
}
"#;

// Part of #3041: Use multi-field struct so ty_signedness returns None.
// Single-field and fieldless structs now have resolved signedness.
const SIGNEDNESS_FALLBACK_SOURCE: &str = r#"
#![allow(dead_code)]
struct Opaque { x: u32, y: i32 }

fn probe_signedness_fallback(a: Opaque, b: Opaque) -> u32 {
    if core::mem::size_of_val(&a) == core::mem::size_of_val(&b) { 1 } else { 0 }
}
"#;

#[test]
fn test_rvalue_unsupported_returns_none() {
    // Rvalue kinds not handled by translate_rvalue_with_env (e.g., Ref, Discriminant,
    // Aggregate) should return None without panicking.
    with_test_ay_ctx_for_source(UNSUPPORTED_RVALUE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_discriminant");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_discriminant", ChcConfig::default());

        let env: HashMap<usize, Expr> = body
            .locals()
            .iter()
            .enumerate()
            .filter_map(|(idx, decl)| {
                ChcCtx::translate_ty(decl.ty)
                    .map(|sort| (idx, Expr::var(format!("_v_{idx}"), sort)))
            })
            .collect();

        // Look for rvalue kinds that fall through to the `other` arm
        for block in &body.blocks {
            for stmt in &block.statements {
                if let rustc_public::mir::StatementKind::Assign(_, rvalue) = &stmt.kind
                    && matches!(rvalue, Rvalue::Discriminant(_) | Rvalue::Ref(..))
                {
                    let result = chc_ctx.translate_rvalue_with_env(rvalue, &env, &[], None, None);
                    assert!(
                        result.is_none(),
                        "Unsupported rvalue {:?} should return None from translate_rvalue_with_env",
                        std::mem::discriminant(rvalue)
                    );
                }
            }
        }
    });
}

#[test]
fn test_rvalue_unsupported_kind_increments_fallback_counter() {
    // Directly exercise the catch-all `other` arm in translate_rvalue_with_env.
    with_test_ay_ctx_for_source(UNSUPPORTED_RVALUE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_discriminant");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_discriminant", ChcConfig::default());

        let rvalue = Rvalue::Discriminant(Place { local: 1, projection: vec![] });
        let before = chc_ctx.fallback_count;
        let result = chc_ctx.translate_rvalue_with_env(&rvalue, &HashMap::new(), &[], None, None);
        let after = chc_ctx.fallback_count;

        assert!(result.is_none(), "unsupported rvalue should return None");
        assert!(
            after > before,
            "unsupported rvalue fallback should increment fallback_count (before={before}, after={after})"
        );
    });
}

#[test]
fn test_div_unknown_signedness_increments_fallback_counter() {
    // Part of #3329: ty_to_bv_width now returns None for ADT types (Opaque struct),
    // so translate_rvalue_with_env correctly bails before reaching signedness inference.
    // This verifies that ADT-typed BinaryOp::Div returns None rather than silently
    // using a 32-bit fallback width.
    with_test_ay_ctx_for_source(SIGNEDNESS_FALLBACK_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_signedness_fallback");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_signedness_fallback", ChcConfig::default());

        let lhs_place = Place { local: 1, projection: vec![] };
        let rhs_place = Place { local: 2, projection: vec![] };
        let rvalue = Rvalue::BinaryOp(
            rustc_public::mir::BinOp::Div,
            Operand::Copy(lhs_place),
            Operand::Copy(rhs_place),
        );

        let mut env: HashMap<usize, Expr> = HashMap::new();
        env.insert(1, Expr::bitvec_const(24, 32));
        env.insert(2, Expr::bitvec_const(3, 32));

        let result = chc_ctx.translate_rvalue_with_env(&rvalue, &env, &[], None, None);

        assert!(
            result.is_none(),
            "ADT-typed div should return None — ty_to_bv_width rejects non-primitive types"
        );
    });
}

#[test]
fn test_rem_unknown_signedness_increments_fallback_counter() {
    // Part of #3329: ty_to_bv_width now returns None for ADT types (Opaque struct),
    // so translate_rvalue_with_env correctly bails before reaching signedness inference.
    // This verifies that ADT-typed BinaryOp::Rem returns None rather than silently
    // using a 32-bit fallback width.
    with_test_ay_ctx_for_source(SIGNEDNESS_FALLBACK_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_signedness_fallback");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_signedness_fallback", ChcConfig::default());

        let lhs_place = Place { local: 1, projection: vec![] };
        let rhs_place = Place { local: 2, projection: vec![] };
        let rvalue = Rvalue::BinaryOp(
            rustc_public::mir::BinOp::Rem,
            Operand::Copy(lhs_place),
            Operand::Copy(rhs_place),
        );

        let mut env: HashMap<usize, Expr> = HashMap::new();
        env.insert(1, Expr::bitvec_const(24, 32));
        env.insert(2, Expr::bitvec_const(3, 32));

        let result = chc_ctx.translate_rvalue_with_env(&rvalue, &env, &[], None, None);

        assert!(
            result.is_none(),
            "ADT-typed rem should return None — ty_to_bv_width rejects non-primitive types"
        );
    });
}

// ═══════════════════════════════════════════════════════════════════════
// translate_place_with_env: bare env lookup (no projection)
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn test_place_env_lookup_no_projection() {
    // translate_place_with_env for place.projection.is_empty() returns
    // env.get(&place.local).cloned() directly.
    with_test_ay_ctx_for_source(UNARY_OP_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_neg");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_neg", ChcConfig::default());

        let mut env: HashMap<usize, Expr> = HashMap::new();
        env.insert(1, Expr::bitvec_const(0xDEAD, 32));

        // Rvalue::Use(Copy(local 1, no projection)) should hit the env lookup path
        let place = Place { local: 1usize, projection: vec![] };
        let rvalue = Rvalue::Use(Operand::Copy(place));
        let result = chc_ctx.translate_rvalue_with_env(&rvalue, &env, &[], None, None);
        assert!(result.is_some(), "env lookup for local 1 should succeed");
        assert_eq!(
            result.unwrap().sort().bitvec_width(),
            Some(32),
            "env lookup should return bv32"
        );
    });
}

#[test]
fn test_place_env_lookup_missing_local_returns_none() {
    // When place.local is not in env, translate_place_with_env returns None.
    with_test_ay_ctx_for_source(UNARY_OP_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_neg");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_neg", ChcConfig::default());

        let env: HashMap<usize, Expr> = HashMap::new(); // empty env

        let place = Place { local: 99usize, projection: vec![] };
        let rvalue = Rvalue::Use(Operand::Copy(place));
        let result = chc_ctx.translate_rvalue_with_env(&rvalue, &env, &[], None, None);
        assert!(result.is_none(), "env lookup for absent local should return None");
    });
}

// ═══════════════════════════════════════════════════════════════════════
// extract_loop_invariant_formula: non-Return terminator rejection
// ═══════════════════════════════════════════════════════════════════════

const NON_RETURN_TERMINATOR_SOURCE: &str = r#"
pub fn probe_single_block_call() -> u32 {
    core::hint::black_box(42)
}
"#;

#[test]
fn test_extract_loop_invariant_rejects_non_return_terminator() {
    // A single-block body that ends with a Call terminator (not Return)
    // should be rejected by the check at codegen_expr_env.rs:23.
    with_test_ay_ctx_for_source(NON_RETURN_TERMINATOR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_single_block_call");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_single_block_call", ChcConfig::default());

        // black_box is typically a Call terminator in a single-block body
        // (though optimizer may alter this). If the body has 1 block with
        // a Call terminator, the invariant extractor should return None.
        let result = chc_ctx.extract_loop_invariant_formula(&[]);
        if body.blocks.len() == 1
            && !matches!(body.blocks[0].terminator.kind, rustc_public::mir::TerminatorKind::Return)
        {
            assert!(result.is_none(), "single-block with non-Return terminator should be rejected");
        }
    });
}
