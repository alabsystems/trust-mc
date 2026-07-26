// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! MIR-driven tests for codegen_assign.rs (938 lines).
//!
//! These tests compile real Rust source, walk the MIR, and call
//! codegen_statement for Assign statements — exercising the actual codegen
//! paths rather than testing expression patterns in isolation.
//!
//! Part of #2016 (test coverage for codegen_assign.rs, 0 MIR-driven tests).

use super::*;
use ay_bindings::Constraint;

/// Recursively check if an expression tree contains a node matching a predicate.
fn expr_contains(expr: &Expr, pred: &dyn Fn(&ExprValue) -> bool) -> bool {
    if pred(expr.value()) {
        return true;
    }
    match expr.value() {
        ExprValue::Not(inner) | ExprValue::BvNeg(inner) | ExprValue::BvNot(inner) => {
            expr_contains(inner, pred)
        }
        ExprValue::Eq(a, b)
        | ExprValue::BvAdd(a, b)
        | ExprValue::BvSub(a, b)
        | ExprValue::BvAnd(a, b)
        | ExprValue::BvOr(a, b)
        | ExprValue::BvShl(a, b)
        | ExprValue::BvLShr(a, b)
        | ExprValue::BvAShr(a, b)
        | ExprValue::BvMul(a, b) => expr_contains(a, pred) || expr_contains(b, pred),
        ExprValue::Ite { cond, then_expr, else_expr } => {
            expr_contains(cond, pred)
                || expr_contains(then_expr, pred)
                || expr_contains(else_expr, pred)
        }
        ExprValue::BvZeroExtend { expr: inner, .. }
        | ExprValue::BvSignExtend { expr: inner, .. }
        | ExprValue::BvExtract { expr: inner, .. } => expr_contains(inner, pred),
        _ => false,
    }
}

/// Check if any Assert constraint in a slice contains an expression matching a predicate.
fn any_assert_contains(commands: &[Constraint], pred: &dyn Fn(&ExprValue) -> bool) -> bool {
    commands.iter().any(|cmd| {
        if let Constraint::Assert { expr, .. } = cmd { expr_contains(expr, pred) } else { false }
    })
}

// Probe source with functions that generate diverse assignment patterns in MIR.
const ASSIGN_PROBE_SOURCE: &str = r#"
pub fn scalar_assign(x: u32) -> u32 {
    let a = x + 1;
    a
}

pub fn ref_assign(x: &u32) -> u32 {
    *x
}

pub fn mut_ref_assign(x: &mut u32) {
    *x = 42;
}

pub fn tuple_assign(x: u32, y: u32) -> (u32, u32) {
    (x, y)
}

pub fn array_index_read(arr: &[u32; 4], idx: usize) -> u32 {
    arr[idx]
}

pub fn bool_assign(a: bool, b: bool) -> bool {
    a && b
}

pub fn cast_assign(x: u8) -> u32 {
    x as u32
}

pub fn negate_assign(x: i32) -> i32 {
    -x
}

pub fn bitwise_assign(x: u32, y: u32) -> u32 {
    x & y
}

pub fn shift_assign(x: u32) -> u32 {
    x << 2
}

pub fn const_ref_assign() -> u32 {
    let r = &42u32;
    *r
}

pub fn exposed_provenance_assign(x: usize) -> *const u8 {
    x as *const u8
}

pub fn expose_address_assign(p: *const u8) -> usize {
    p as usize
}
"#;

/// Seed argument locals into SSA environment with symbolic variables.
fn seed_assign_args(codegen: &mut StatementCodegen<'_, '_, '_>, body: &rustc_public::mir::Body) {
    for (idx, local_decl) in body.arg_locals().iter().enumerate() {
        let local_idx = idx + 1;
        let local = Local::from(local_idx);
        let place = Place { local, projection: vec![] };
        let base = codegen.ssa_base_name(&place);
        if let Some(sort) = StatementCodegen::infer_sort_from_ty(local_decl.ty) {
            codegen.env_update(base, Expr::var(format!("arg_{local_idx}"), sort));
        } else {
            // Raw/ref pointers: seed as bv64 (pointer width)
            codegen.env_update(
                base,
                Expr::var(format!("arg_{local_idx}"), Sort::bitvec(POINTER_WIDTH)),
            );
        }
    }
}

/// Count how many Assign statements exist in the body's basic blocks.
fn count_assign_stmts(body: &rustc_public::mir::Body) -> usize {
    body.blocks
        .iter()
        .flat_map(|bb| bb.statements.iter())
        .filter(|stmt| matches!(stmt.kind, StatementKind::Assign(..)))
        .count()
}

/// Walk all basic blocks and process all statements through codegen_statement.
/// Returns the number of statements successfully processed (no panic).
fn walk_all_statements(
    codegen: &mut StatementCodegen<'_, '_, '_>,
    body: &rustc_public::mir::Body,
) -> usize {
    let mut processed = 0;
    for bb in &body.blocks {
        for stmt in &bb.statements {
            codegen.codegen_statement(stmt);
            processed += 1;
        }
    }
    processed
}

// =============================================================================
// Scalar assignment: let a = x + 1
// =============================================================================

/// Test that scalar_assign produces BvAdd constraints for `x + 1`.
#[test]
fn test_codegen_assign_scalar_walks_mir() {
    with_test_ay_ctx_for_source(ASSIGN_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "scalar_assign");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_assign_args(&mut codegen, &body);

        let assigns = count_assign_stmts(&body);
        assert!(assigns > 0, "scalar_assign should have Assign statements");

        let before = codegen.ctx.program.commands().len();
        let processed = walk_all_statements(&mut codegen, &body);
        assert!(processed > 0, "should process at least one statement");

        // Semantic: codegen emitted constraints containing BvAdd (x + 1)
        let added = &codegen.ctx.program.commands()[before..];
        assert!(!added.is_empty(), "scalar addition should emit constraints");
        assert!(
            any_assert_contains(added, &|v| matches!(v, ExprValue::BvAdd(..))),
            "scalar_assign (x + 1) should produce BvAdd in constraints"
        );
    });
}

// =============================================================================
// Reference deref: *x (read through reference)
// =============================================================================

/// Test that ref_assign (read through &u32) emits SSA constraints for deref read.
#[test]
fn test_codegen_assign_ref_deref_walks_mir() {
    with_test_ay_ctx_for_source(ASSIGN_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "ref_assign");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_assign_args(&mut codegen, &body);

        let before = codegen.ctx.program.commands().len();
        let processed = walk_all_statements(&mut codegen, &body);
        assert!(processed > 0, "ref_assign should have statements to process");

        // Semantic: deref read emits SSA constraints
        let added = &codegen.ctx.program.commands()[before..];
        assert!(!added.is_empty(), "ref deref read should emit SSA constraints");
    });
}

// =============================================================================
// Mutable reference write: *x = 42
// =============================================================================

/// Test that mut_ref_assign (*x = 42) emits constraints for constant-value deref write.
#[test]
fn test_codegen_assign_mut_ref_write_walks_mir() {
    with_test_ay_ctx_for_source(ASSIGN_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "mut_ref_assign");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_assign_args(&mut codegen, &body);

        let assigns = count_assign_stmts(&body);
        assert!(assigns > 0, "mut_ref_assign should have Assign statements");

        let before = codegen.ctx.program.commands().len();
        let processed = walk_all_statements(&mut codegen, &body);
        assert!(processed > 0, "should process at least one statement");

        // Semantic: deref write (*x = 42) should emit constraints with a constant
        let added = &codegen.ctx.program.commands()[before..];
        assert!(!added.is_empty(), "mut ref deref write should emit SSA constraints");
        assert!(
            any_assert_contains(added, &|v| matches!(v, ExprValue::BitVecConst { .. })),
            "mut_ref write of constant 42 should produce BitVecConst"
        );
    });
}

// =============================================================================
// Tuple aggregate: (x, y)
// =============================================================================

/// Test that tuple_assign emits constraints for Aggregate(Tuple) construction.
#[test]
fn test_codegen_assign_tuple_aggregate_walks_mir() {
    with_test_ay_ctx_for_source(ASSIGN_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "tuple_assign");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_assign_args(&mut codegen, &body);

        // Verify there's an Aggregate assignment in MIR
        let has_aggregate = body.blocks.iter().any(|bb| {
            bb.statements
                .iter()
                .any(|stmt| matches!(&stmt.kind, StatementKind::Assign(_, Rvalue::Aggregate(..))))
        });
        assert!(has_aggregate, "tuple_assign should have an Aggregate rvalue");

        let before = codegen.ctx.program.commands().len();
        let processed = walk_all_statements(&mut codegen, &body);
        assert!(processed > 0, "should process statements");

        // Semantic: tuple aggregate should emit SSA constraints
        let added = &codegen.ctx.program.commands()[before..];
        assert!(!added.is_empty(), "tuple aggregate should emit SSA constraints");
    });
}

// =============================================================================
// Bool assignment: a && b
// =============================================================================

/// Test that bool_assign emits bool-sorted constraints for short-circuit `&&`.
#[test]
fn test_codegen_assign_bool_walks_mir() {
    with_test_ay_ctx_for_source(ASSIGN_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bool_assign");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_assign_args(&mut codegen, &body);

        let before = codegen.ctx.program.commands().len();
        let processed = walk_all_statements(&mut codegen, &body);
        assert!(processed > 0, "should process bool_assign statements");

        // Semantic: bool assignments emit constraints with bool-sorted expressions
        let added = &codegen.ctx.program.commands()[before..];
        assert!(!added.is_empty(), "bool assignment should emit SSA constraints");
        // `a && b` in MIR becomes short-circuit control flow with bool constants
        let has_bool_const = any_assert_contains(added, &|v| matches!(v, ExprValue::BoolConst(..)));
        assert!(has_bool_const, "bool_assign (a && b) should produce BoolConst in constraints");
    });
}

// =============================================================================
// Cast: x as u32 (widening cast)
// =============================================================================

/// Test that cast_assign emits BvZeroExtend constraint for u8 → u32 widening.
#[test]
fn test_codegen_assign_cast_walks_mir() {
    with_test_ay_ctx_for_source(ASSIGN_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "cast_assign");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_assign_args(&mut codegen, &body);

        // Verify there's a Cast assignment in MIR
        let has_cast = body.blocks.iter().any(|bb| {
            bb.statements
                .iter()
                .any(|stmt| matches!(&stmt.kind, StatementKind::Assign(_, Rvalue::Cast(..))))
        });
        assert!(has_cast, "cast_assign should have a Cast rvalue");

        let before = codegen.ctx.program.commands().len();
        let processed = walk_all_statements(&mut codegen, &body);
        assert!(processed > 0, "should process cast_assign statements");

        // Semantic: u8→u32 widening cast emits BvZeroExtend
        let added = &codegen.ctx.program.commands()[before..];
        assert!(!added.is_empty(), "cast assignment should emit SSA constraints");
        assert!(
            any_assert_contains(added, &|v| matches!(v, ExprValue::BvZeroExtend { .. })),
            "u8→u32 cast should produce BvZeroExtend in constraints"
        );
    });
}

// =============================================================================
// Unary negation: -x
// =============================================================================

/// Test that negate_assign emits BvNeg constraint for `-x`.
#[test]
fn test_codegen_assign_negate_walks_mir() {
    with_test_ay_ctx_for_source(ASSIGN_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "negate_assign");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_assign_args(&mut codegen, &body);

        let before = codegen.ctx.program.commands().len();
        let processed = walk_all_statements(&mut codegen, &body);
        assert!(processed > 0, "should process negate_assign statements");

        // Semantic: -x produces BvNeg
        let added = &codegen.ctx.program.commands()[before..];
        assert!(!added.is_empty(), "negate assignment should emit SSA constraints");
        assert!(
            any_assert_contains(added, &|v| matches!(v, ExprValue::BvNeg(..))),
            "negate_assign (-x) should produce BvNeg in constraints"
        );
    });
}

// =============================================================================
// Bitwise: x & y
// =============================================================================

/// Test that bitwise_assign emits BvAnd constraint for `x & y`.
#[test]
fn test_codegen_assign_bitwise_walks_mir() {
    with_test_ay_ctx_for_source(ASSIGN_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bitwise_assign");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_assign_args(&mut codegen, &body);

        // Verify there's a BinaryOp assignment
        let has_binop = body.blocks.iter().any(|bb| {
            bb.statements
                .iter()
                .any(|stmt| matches!(&stmt.kind, StatementKind::Assign(_, Rvalue::BinaryOp(..))))
        });
        assert!(has_binop, "bitwise_assign should have a BinaryOp rvalue");

        let before = codegen.ctx.program.commands().len();
        let processed = walk_all_statements(&mut codegen, &body);
        assert!(processed > 0, "should process bitwise_assign statements");

        // Semantic: x & y produces BvAnd
        let added = &codegen.ctx.program.commands()[before..];
        assert!(!added.is_empty(), "bitwise assignment should emit SSA constraints");
        assert!(
            any_assert_contains(added, &|v| matches!(v, ExprValue::BvAnd(..))),
            "bitwise_assign (x & y) should produce BvAnd in constraints"
        );
    });
}

// =============================================================================
// Shift: x << 2
// =============================================================================

/// Test that shift_assign emits BvShl constraint for `x << 2`.
#[test]
fn test_codegen_assign_shift_walks_mir() {
    with_test_ay_ctx_for_source(ASSIGN_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "shift_assign");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_assign_args(&mut codegen, &body);

        let before = codegen.ctx.program.commands().len();
        let processed = walk_all_statements(&mut codegen, &body);
        assert!(processed > 0, "should process shift_assign statements");

        // Semantic: x << 2 produces BvShl
        let added = &codegen.ctx.program.commands()[before..];
        assert!(!added.is_empty(), "shift assignment should emit SSA constraints");
        assert!(
            any_assert_contains(added, &|v| matches!(v, ExprValue::BvShl(..))),
            "shift_assign (x << 2) should produce BvShl in constraints"
        );
    });
}

// =============================================================================
// Constant reference: &42u32
// =============================================================================

/// Test that const_ref_assign emits constraints with BitVecConst for the constant 42.
#[test]
fn test_codegen_assign_const_ref_walks_mir() {
    with_test_ay_ctx_for_source(ASSIGN_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "const_ref_assign");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_assign_args(&mut codegen, &body);

        let before = codegen.ctx.program.commands().len();
        let processed = walk_all_statements(&mut codegen, &body);
        assert!(processed > 0, "should process const_ref_assign statements");

        // Semantic: &42u32 path should produce BitVecConst in constraints
        let added = &codegen.ctx.program.commands()[before..];
        assert!(!added.is_empty(), "const ref assignment should emit SSA constraints");
        assert!(
            any_assert_contains(added, &|v| matches!(v, ExprValue::BitVecConst { .. })),
            "const_ref_assign (&42u32) should produce BitVecConst in constraints"
        );
    });
}

// =============================================================================
// Verify statement counts: each function should have a reasonable number
// =============================================================================

/// Test that the probe source compiles and all functions have MIR bodies.
#[test]
fn test_assign_probe_all_functions_have_mir() {
    with_test_ay_ctx_for_source(ASSIGN_PROBE_SOURCE, |ctx| {
        let fns = [
            "scalar_assign",
            "ref_assign",
            "mut_ref_assign",
            "tuple_assign",
            "bool_assign",
            "cast_assign",
            "negate_assign",
            "bitwise_assign",
            "shift_assign",
            "const_ref_assign",
            "exposed_provenance_assign",
            "expose_address_assign",
        ];
        for name in &fns {
            let instance = find_instance_by_suffix(&ctx, name);
            let body = instance.body();
            assert!(body.is_some(), "{name} should have a MIR body");
        }
    });
}

/// Check if any constraint in a slice declares or uses a variable whose name
/// starts with the given prefix.
fn any_constraint_has_var_prefix(commands: &[Constraint], prefix: &str) -> bool {
    commands.iter().any(|cmd| match cmd {
        Constraint::DeclareConst { name, .. } => name.starts_with(prefix),
        Constraint::Assert { expr, .. } => expr_contains(
            expr,
            &|v| matches!(v, ExprValue::Var { name } if name.starts_with(prefix)),
        ),
        _ => false,
    })
}

// =============================================================================
// Exposed provenance: usize as *const u8  (#3350, #3819)
// =============================================================================

/// Test that integer-to-pointer cast (PointerWithExposedProvenance) invalidates
/// obj_valid via heap_no_provenance_valid.  This guards the #3350 false-proof
/// fix at the assignment layer, not just the cast-expression layer.
#[test]
fn test_codegen_assign_pointer_with_exposed_provenance_invalidates_obj_valid() {
    with_test_ay_ctx_for_source(ASSIGN_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "exposed_provenance_assign");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);

        // Verify the MIR contains a PointerWithExposedProvenance cast
        let has_exposed = body.blocks.iter().any(|bb| {
            bb.statements.iter().any(|stmt| {
                matches!(
                    &stmt.kind,
                    StatementKind::Assign(
                        _,
                        Rvalue::Cast(CastKind::PointerWithExposedProvenance, ..)
                    )
                )
            })
        });
        assert!(
            has_exposed,
            "exposed_provenance_assign should have a PointerWithExposedProvenance cast in MIR"
        );

        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_assign_args(&mut codegen, &body);

        let before = codegen.ctx.program.commands().len();
        walk_all_statements(&mut codegen, &body);
        let added = &codegen.ctx.program.commands()[before..];

        assert!(
            any_constraint_has_var_prefix(added, "heap_no_provenance_valid"),
            "PointerWithExposedProvenance assignment must emit \
             heap_no_provenance_valid constraint (obj_valid invalidation, #3350)"
        );
    });
}

// =============================================================================
// Expose address: *const u8 as usize  (negative control, #3819)
// =============================================================================

/// Test that pointer-to-integer cast (PointerExposeAddress) does NOT invalidate
/// obj_valid.  This is the negative control that prevents the provenance test
/// above from degenerating into "some heap constraint was emitted".
#[test]
fn test_codegen_assign_pointer_expose_address_does_not_invalidate_obj_valid() {
    with_test_ay_ctx_for_source(ASSIGN_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "expose_address_assign");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);

        // Verify the MIR contains a PointerExposeAddress cast
        let has_expose = body.blocks.iter().any(|bb| {
            bb.statements.iter().any(|stmt| {
                matches!(
                    &stmt.kind,
                    StatementKind::Assign(_, Rvalue::Cast(CastKind::PointerExposeAddress, ..))
                )
            })
        });
        assert!(has_expose, "expose_address_assign should have a PointerExposeAddress cast in MIR");

        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_assign_args(&mut codegen, &body);

        let before = codegen.ctx.program.commands().len();
        walk_all_statements(&mut codegen, &body);
        let added = &codegen.ctx.program.commands()[before..];

        assert!(
            !any_constraint_has_var_prefix(added, "heap_no_provenance_valid"),
            "PointerExposeAddress (ptr→int) must NOT emit \
             heap_no_provenance_valid — only int→ptr casts invalidate provenance (#3819)"
        );
    });
}
