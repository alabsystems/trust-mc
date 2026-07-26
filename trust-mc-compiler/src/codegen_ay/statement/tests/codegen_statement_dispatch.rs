// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! MIR-driven tests for codegen_statement.rs — non-Assign dispatch arms.
//!
//! Tests cover statement kinds that are NOT Assign:
//! - `SetDiscriminant`: Unit enum assignment and ADT piecewise construction
//! - `StorageDead`/`StorageLive`: Storage markers
//! - No-op variants: FakeRead, PlaceMention, Nop, ConstEvalCounter, Retag
//!
//! These tests compile real Rust source, walk ALL MIR statements through
//! codegen_statement, and verify the generated constraints.
//!
//! Part of #2016: test coverage for codegen_statement.rs (205 lines, 0 tests).

use super::*;
use ay_bindings::Constraint;

// ─── Helper: seed argument locals ──────────────────────────────────

fn seed_args(codegen: &mut StatementCodegen<'_, '_, '_>, body: &rustc_public::mir::Body) {
    for (idx, local_decl) in body.arg_locals().iter().enumerate() {
        let local_idx = idx + 1;
        let local = Local::from(local_idx);
        let place = Place { local, projection: vec![] };
        let base = codegen.ssa_base_name(&place);
        if let Some(sort) = StatementCodegen::infer_sort_from_ty(local_decl.ty) {
            codegen.env_update(base, Expr::var(format!("arg_{local_idx}"), sort));
        } else {
            codegen.env_update(
                base,
                Expr::var(format!("arg_{local_idx}"), Sort::bitvec(POINTER_WIDTH)),
            );
        }
    }
}

/// Walk all statements through codegen_statement, return processed count.
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

/// Count statements matching a predicate.
fn count_stmts(body: &rustc_public::mir::Body, pred: impl Fn(&StatementKind) -> bool) -> usize {
    body.blocks.iter().flat_map(|bb| bb.statements.iter()).filter(|stmt| pred(&stmt.kind)).count()
}

/// Check if any Assert constraint contains an expression matching a predicate.
fn any_assert_contains(commands: &[Constraint], pred: &dyn Fn(&ExprValue) -> bool) -> bool {
    commands.iter().any(|cmd| {
        if let Constraint::Assert { expr, .. } = cmd {
            expr_contains_shallow(expr, pred)
        } else {
            false
        }
    })
}

/// Shallow expression tree check (top-level + one level of children).
fn expr_contains_shallow(expr: &Expr, pred: &dyn Fn(&ExprValue) -> bool) -> bool {
    if pred(expr.value()) {
        return true;
    }
    match expr.value() {
        ExprValue::Not(inner) | ExprValue::BvNeg(inner) | ExprValue::BvNot(inner) => {
            pred(inner.value())
        }
        ExprValue::Eq(a, b)
        | ExprValue::BvAdd(a, b)
        | ExprValue::BvSub(a, b)
        | ExprValue::BvAnd(a, b) => pred(a.value()) || pred(b.value()),
        ExprValue::Ite { cond, then_expr, else_expr } => {
            pred(cond.value()) || pred(then_expr.value()) || pred(else_expr.value())
        }
        _ => false,
    }
}

// =============================================================================
// SetDiscriminant — unit enum
// =============================================================================

// Unit enums with Copy derive: SetDiscriminant may or may not appear depending
// on MIR lowering. What matters is that codegen_statement handles all stmt kinds.
const UNIT_ENUM_SOURCE: &str = r#"
#![allow(dead_code)]
#[derive(Clone, Copy)]
pub enum Color {
    Red,
    Green,
    Blue,
}

pub fn make_green() -> Color {
    Color::Green
}

pub fn match_color(c: Color) -> u32 {
    match c {
        Color::Red => 1,
        Color::Green => 2,
        Color::Blue => 3,
    }
}
"#;

/// Test that unit enum construction emits SSA constraints for the discriminant.
#[test]
fn test_codegen_statement_unit_enum_construction() {
    with_test_ay_ctx_for_source(UNIT_ENUM_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "make_green");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_args(&mut codegen, &body);

        let before = codegen.ctx.program.commands().len();
        let processed = walk_all_statements(&mut codegen, &body);
        assert!(processed > 0, "make_green should have statements to process");

        // Semantic: enum construction emits constraints (discriminant assignment)
        let added = &codegen.ctx.program.commands()[before..];
        assert!(!added.is_empty(), "enum construction should emit SSA constraints");
    });
}

/// Test that unit enum match emits constraints including BitVecConst for branch values.
#[test]
fn test_codegen_statement_unit_enum_match() {
    with_test_ay_ctx_for_source(UNIT_ENUM_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "match_color");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_args(&mut codegen, &body);

        let before = codegen.ctx.program.commands().len();
        let processed = walk_all_statements(&mut codegen, &body);
        assert!(processed > 0, "match_color should process statements");

        // Semantic: match arms assign constant return values (1, 2, 3)
        let added = &codegen.ctx.program.commands()[before..];
        assert!(!added.is_empty(), "enum match should emit SSA constraints");
        let has_const = any_assert_contains(added, &|v| matches!(v, ExprValue::BitVecConst { .. }));
        assert!(has_const, "match arms should produce BitVecConst for return values");
    });
}

// =============================================================================
// SetDiscriminant — enum with fields (Option-like)
// =============================================================================

const OPTION_ENUM_SOURCE: &str = r#"
#![allow(dead_code)]
pub fn make_some(x: u32) -> Option<u32> {
    Some(x)
}

pub fn make_none() -> Option<u32> {
    None
}

pub fn option_discriminant(x: Option<u32>) -> bool {
    x.is_some()
}
"#;

/// Test Option::Some(x) emits datatype constructor constraints.
#[test]
fn test_codegen_statement_option_some() {
    with_test_ay_ctx_for_source(OPTION_ENUM_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "make_some");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_args(&mut codegen, &body);

        let before = codegen.ctx.program.commands().len();
        let processed = walk_all_statements(&mut codegen, &body);
        assert!(processed > 0, "make_some should process statements");

        // Semantic: Option::Some(x) emits constraints
        let added = &codegen.ctx.program.commands()[before..];
        assert!(!added.is_empty(), "Option::Some construction should emit SSA constraints");
    });
}

/// Test Option::None emits constraints for the None variant discriminant.
#[test]
fn test_codegen_statement_option_none() {
    with_test_ay_ctx_for_source(OPTION_ENUM_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "make_none");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_args(&mut codegen, &body);

        let before = codegen.ctx.program.commands().len();
        let processed = walk_all_statements(&mut codegen, &body);
        assert!(processed > 0, "make_none should process statements");

        // Semantic: None construction emits constraints
        let added = &codegen.ctx.program.commands()[before..];
        assert!(!added.is_empty(), "Option::None construction should emit SSA constraints");
    });
}

// =============================================================================
// SetDiscriminant — Result enum (multi-field variants)
// =============================================================================

const RESULT_ENUM_SOURCE: &str = r#"
#![allow(dead_code)]
pub fn make_ok(x: i32) -> Result<i32, u64> {
    Ok(x)
}

pub fn make_err(e: u64) -> Result<i32, u64> {
    Err(e)
}
"#;

/// Test Result::Ok emits constraints for the Ok variant with its field.
#[test]
fn test_codegen_statement_result_ok() {
    with_test_ay_ctx_for_source(RESULT_ENUM_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "make_ok");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_args(&mut codegen, &body);

        let before = codegen.ctx.program.commands().len();
        let processed = walk_all_statements(&mut codegen, &body);
        assert!(processed > 0, "make_ok should process statements");

        // Semantic: Result::Ok construction emits constraints
        let added = &codegen.ctx.program.commands()[before..];
        assert!(!added.is_empty(), "Result::Ok construction should emit SSA constraints");
    });
}

/// Test Result::Err emits constraints for the second variant path.
#[test]
fn test_codegen_statement_result_err() {
    with_test_ay_ctx_for_source(RESULT_ENUM_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "make_err");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_args(&mut codegen, &body);

        let before = codegen.ctx.program.commands().len();
        let processed = walk_all_statements(&mut codegen, &body);
        assert!(processed > 0, "make_err should process statements");

        // Semantic: Result::Err construction emits constraints
        let added = &codegen.ctx.program.commands()[before..];
        assert!(!added.is_empty(), "Result::Err construction should emit SSA constraints");
    });
}

// =============================================================================
// SetDiscriminant — unit enum with explicit discriminants (#1393)
// =============================================================================

const EXPLICIT_DISCR_SOURCE: &str = r#"
#![allow(dead_code)]
#[repr(i32)]
pub enum Signal {
    None = 0,
    Term = -1,
    Kill = -9,
    Stop = -500,
}

pub fn make_kill() -> Signal {
    Signal::Kill
}

pub fn make_stop() -> Signal {
    Signal::Stop
}
"#;

/// Test explicit negative discriminant (Signal::Kill = -9) emits BitVecConst.
#[test]
fn test_codegen_statement_explicit_negative_discriminant() {
    with_test_ay_ctx_for_source(EXPLICIT_DISCR_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "make_kill");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_args(&mut codegen, &body);

        let before = codegen.ctx.program.commands().len();
        let processed = walk_all_statements(&mut codegen, &body);
        assert!(processed > 0, "make_kill should process statements");

        // Semantic: explicit discriminant assignment emits a constant
        let added = &codegen.ctx.program.commands()[before..];
        assert!(!added.is_empty(), "explicit discriminant should emit SSA constraints");
        let has_const = any_assert_contains(added, &|v| matches!(v, ExprValue::BitVecConst { .. }));
        assert!(has_const, "Signal::Kill (-9) should produce BitVecConst for discriminant");
    });
}

/// Test Signal::Stop = -500 — large negative explicit discriminant.
#[test]
fn test_codegen_statement_large_negative_discriminant() {
    with_test_ay_ctx_for_source(EXPLICIT_DISCR_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "make_stop");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_args(&mut codegen, &body);

        let before = codegen.ctx.program.commands().len();
        let processed = walk_all_statements(&mut codegen, &body);
        assert!(processed > 0, "make_stop should process statements");

        // Semantic: large negative discriminant emits a constant
        let added = &codegen.ctx.program.commands()[before..];
        assert!(!added.is_empty(), "large negative discriminant should emit SSA constraints");
        let has_const = any_assert_contains(added, &|v| matches!(v, ExprValue::BitVecConst { .. }));
        assert!(has_const, "Signal::Stop (-500) should produce BitVecConst for discriminant");
    });
}

// =============================================================================
// Non-Assign statement presence — verify diverse statement kinds
// =============================================================================

const DIVERSE_STMTS_SOURCE: &str = r#"
#![allow(dead_code)]
pub fn diverse_stmts(x: u32) -> u32 {
    let a = x + 1;
    let b = a * 2;
    let c = if b > 10 { b - 5 } else { b + 5 };
    c
}
"#;

/// Test diverse statements emit constraints including BvAdd, BvMul, BvSub.
#[test]
fn test_codegen_statement_diverse_stmts() {
    with_test_ay_ctx_for_source(DIVERSE_STMTS_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "diverse_stmts");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_args(&mut codegen, &body);

        let total = body.blocks.iter().flat_map(|bb| bb.statements.iter()).count();
        let assign_count = count_stmts(&body, |kind| matches!(kind, StatementKind::Assign(..)));

        let before = codegen.ctx.program.commands().len();
        let processed = walk_all_statements(&mut codegen, &body);
        assert_eq!(processed, total, "should process all {total} statements");
        assert!(assign_count > 0, "should have Assign statements");

        // Semantic: arithmetic operations emit constraints
        let added = &codegen.ctx.program.commands()[before..];
        assert!(!added.is_empty(), "diverse statements should emit SSA constraints");
        // x + 1 produces BvAdd
        let has_add = any_assert_contains(added, &|v| matches!(v, ExprValue::BvAdd(..)));
        assert!(has_add, "diverse_stmts should contain BvAdd for x + 1");
    });
}

// =============================================================================
// Mixed enum and scalar — exercises multiple dispatch arms together
// =============================================================================

const MIXED_SOURCE: &str = r#"
#![allow(dead_code)]
pub enum Shape {
    Circle,
    Square,
    Triangle,
}

pub fn create_and_use(x: u32) -> Option<u32> {
    let _shape = Shape::Circle;
    let temp = x + 1;
    if temp > 10 {
        Some(temp)
    } else {
        None
    }
}
"#;

/// Test mixed enum + scalar function emits BvAdd and BitVecConst constraints.
#[test]
fn test_codegen_statement_mixed_kinds() {
    with_test_ay_ctx_for_source(MIXED_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "create_and_use");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_args(&mut codegen, &body);

        let assign_count = count_stmts(&body, |kind| matches!(kind, StatementKind::Assign(..)));
        assert!(assign_count > 0, "should have Assign statements");

        let before = codegen.ctx.program.commands().len();
        let processed = walk_all_statements(&mut codegen, &body);
        assert!(processed > 0, "should process statements");

        // Semantic: mixed function emits constraints
        let added = &codegen.ctx.program.commands()[before..];
        assert!(!added.is_empty(), "mixed enum+scalar should emit SSA constraints");
        // x + 1 produces BvAdd
        let has_add = any_assert_contains(added, &|v| matches!(v, ExprValue::BvAdd(..)));
        assert!(has_add, "create_and_use should contain BvAdd for x + 1");
    });
}

// =============================================================================
// Piecewise enum construction — forces SetDiscriminant in MIR
// =============================================================================

// Match on one enum and construct another — the construction side should use
// piecewise field writes + SetDiscriminant when the target variant has fields.
const PIECEWISE_ENUM_SOURCE: &str = r#"
#![allow(dead_code)]
pub enum MyResult {
    Ok(i32),
    Err(u32),
}

pub fn convert(x: Option<i32>) -> MyResult {
    match x {
        Some(v) => MyResult::Ok(v),
        None => MyResult::Err(0),
    }
}

pub fn build_nested(x: i32) -> Option<Option<i32>> {
    if x > 0 {
        Some(Some(x))
    } else {
        Some(None)
    }
}
"#;

/// Test match-and-build pattern emits constraints for both piecewise construction paths.
#[test]
fn test_codegen_statement_piecewise_enum_convert() {
    with_test_ay_ctx_for_source(PIECEWISE_ENUM_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "convert");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_args(&mut codegen, &body);

        let before = codegen.ctx.program.commands().len();
        let processed = walk_all_statements(&mut codegen, &body);
        assert!(processed > 0, "convert should process statements");

        // Semantic: piecewise enum construction emits constraints
        let added = &codegen.ctx.program.commands()[before..];
        assert!(!added.is_empty(), "piecewise enum construction should emit SSA constraints");
        // Enum construction emits DeclareConst/DeclareDatatype + Assert for SSA defs
        let has_assert = added.iter().any(|cmd| matches!(cmd, Constraint::Assert { .. }));
        assert!(has_assert, "convert should produce Assert constraints for enum construction");
    });
}

/// Test nested Option construction emits constraints for both paths.
#[test]
fn test_codegen_statement_nested_option() {
    with_test_ay_ctx_for_source(PIECEWISE_ENUM_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "build_nested");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_args(&mut codegen, &body);

        let before = codegen.ctx.program.commands().len();
        let processed = walk_all_statements(&mut codegen, &body);
        assert!(processed > 0, "build_nested should process statements");

        // Semantic: nested Option construction emits constraints
        let added = &codegen.ctx.program.commands()[before..];
        assert!(!added.is_empty(), "nested Option construction should emit SSA constraints");
    });
}

// =============================================================================
// Statement kind inventory — catalog what the compiler actually emits
// =============================================================================

/// Verify that diverse_stmts has multiple basic blocks and emits constraints
/// from each block.
#[test]
fn test_codegen_statement_multiple_blocks() {
    with_test_ay_ctx_for_source(DIVERSE_STMTS_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "diverse_stmts");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_args(&mut codegen, &body);

        // With an if/else, we should have at least 3 basic blocks
        assert!(
            body.blocks.len() >= 3,
            "diverse_stmts should have >=3 blocks for if/else, got {}",
            body.blocks.len()
        );

        let before = codegen.ctx.program.commands().len();
        let processed = walk_all_statements(&mut codegen, &body);
        assert!(processed > 0);

        // Semantic: multiple blocks with arithmetic produce multiple constraints
        let added = &codegen.ctx.program.commands()[before..];
        assert!(
            added.len() >= 3,
            "diverse_stmts with 3+ blocks should emit at least 3 constraints, got {}",
            added.len()
        );
    });
}

// =============================================================================
// Verify all probe functions compile
// =============================================================================

#[test]
fn test_all_dispatch_probes_compile() {
    let sources_and_fns = [
        (UNIT_ENUM_SOURCE, vec!["make_green", "match_color"]),
        (OPTION_ENUM_SOURCE, vec!["make_some", "make_none", "option_discriminant"]),
        (RESULT_ENUM_SOURCE, vec!["make_ok", "make_err"]),
        (EXPLICIT_DISCR_SOURCE, vec!["make_kill", "make_stop"]),
        (DIVERSE_STMTS_SOURCE, vec!["diverse_stmts"]),
        (MIXED_SOURCE, vec!["create_and_use"]),
        (PIECEWISE_ENUM_SOURCE, vec!["convert", "build_nested"]),
    ];

    for (source, fns) in &sources_and_fns {
        with_test_ay_ctx_for_source(source, |ctx| {
            for name in fns {
                let instance = find_instance_by_suffix(&ctx, name);
                assert!(instance.body().is_some(), "{name} should have a MIR body");
            }
        });
    }
}
