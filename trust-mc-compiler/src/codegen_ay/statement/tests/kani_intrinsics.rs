// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! MIR-driven unit tests for kani.rs — Kani verification intrinsic codegen.
//!
//! Tests exercise the actual `StatementCodegen` methods:
//! - `codegen_kani_any_raw` — symbolic variable creation (bitvec, bool, array, tuple, enum)
//! - `codegen_kani_assume` — path constraint emission via assert_guarded
//! - `codegen_kani_assert` — violation recording via record_violation_guarded
//! - `codegen_kani_cover` — cover property registration
//! - `codegen_float_to_int_in_range` — symbolic bool over-approximation
//! - `codegen_kani_value_view` — bv2int/bv2int_signed conversion
//!
//! Part of #2016 and #2192: MIR-driven codegen testing with semantic assertions.

use rustc_public::ty::GenericArgKind;

use super::*;

// ═══════════════════════════════════════════════════════════════════════
// Shared helpers
// ═══════════════════════════════════════════════════════════════════════

/// Simple Rust source that provides various typed functions for setting up
/// StatementCodegen contexts with specific local sorts.
const KANI_PROBE_SOURCE: &str = r#"
pub fn u32_probe(x: u32) -> u32 { x }
pub fn bool_probe(x: bool) -> bool { x }
pub fn two_bool_probe(x: bool, y: bool) -> bool { x && y }
pub fn u8_probe(x: u8) -> u8 { x }
pub fn i64_probe(x: i64) -> i64 { x }
pub fn two_u32_probe(x: u32, _y: u32) -> u32 { x }
"#;

fn seed_arg_locals(codegen: &mut StatementCodegen<'_, '_, '_>, body: &rustc_public::mir::Body) {
    for (idx, local_decl) in body.arg_locals().iter().enumerate() {
        let local_idx = idx + 1;
        let place = Place { local: Local::from(local_idx), projection: vec![] };
        let base = codegen.ssa_base_name(&place);
        if let Some(sort) = StatementCodegen::infer_sort_from_ty(local_decl.ty) {
            codegen.env_update(base, Expr::var(format!("kani_arg_{local_idx}"), sort));
        }
    }
}

fn return_dest_place() -> Place {
    Place { local: Local::from(0usize), projection: vec![] }
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

// ═══════════════════════════════════════════════════════════════════════
// codegen_kani_any_raw — default case (bitvec symbolic)
// ═══════════════════════════════════════════════════════════════════════

/// codegen_kani_any_raw for a u32 destination creates a bitvec(32) symbolic
/// variable and stores it in the SSA environment.
#[test]
fn test_any_raw_u32_creates_bitvec32_symbolic() {
    with_test_ay_ctx_for_source(KANI_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "u32_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = return_dest_place();
        codegen.codegen_kani_any_raw(&dest);

        // Verify: destination assigned with bitvec(32) expression
        let dest_expr =
            assigned_expr_for_place(&mut codegen, &dest).expect("any_raw should assign dest");
        assert_eq!(
            dest_expr.sort().bitvec_width(),
            Some(32),
            "any_raw for u32 destination should produce bv32"
        );

        // Verify: the expression is a symbolic variable (not a constant)
        assert!(
            !matches!(dest_expr.value(), ExprValue::BitVecConst { .. }),
            "any_raw result should be a symbolic variable, not a constant"
        );
    });
}

/// codegen_kani_any_raw for a bool destination creates a boolean symbolic.
#[test]
fn test_any_raw_bool_creates_bool_symbolic() {
    with_test_ay_ctx_for_source(KANI_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bool_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = return_dest_place();
        codegen.codegen_kani_any_raw(&dest);

        let dest_expr =
            assigned_expr_for_place(&mut codegen, &dest).expect("any_raw should assign dest");
        assert!(
            dest_expr.sort().is_bool(),
            "any_raw for bool destination should produce Bool sort"
        );
    });
}

#[test]
fn test_any_raw_char_adds_unicode_scalar_constraint() {
    let source = r#"
pub fn char_probe(x: char) -> char { x }
"#;
    with_test_ay_ctx_for_source(source, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "char_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let constraints_before = constraint_count(&codegen);
        let dest = return_dest_place();
        codegen.codegen_kani_any_raw(&dest);

        let dest_expr =
            assigned_expr_for_place(&mut codegen, &dest).expect("char any_raw should assign dest");
        assert_eq!(
            dest_expr.sort().bitvec_width(),
            Some(32),
            "char any_raw should produce a bv32 Unicode scalar"
        );
        assert_eq!(
            constraint_count(&codegen),
            constraints_before + 1,
            "char any_raw should constrain the nondet value to valid Unicode scalar ranges"
        );
    });
}

/// codegen_kani_any_raw for u8 creates bitvec(8).
#[test]
fn test_any_raw_u8_creates_bitvec8_symbolic() {
    with_test_ay_ctx_for_source(KANI_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "u8_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = return_dest_place();
        codegen.codegen_kani_any_raw(&dest);

        let dest_expr =
            assigned_expr_for_place(&mut codegen, &dest).expect("any_raw should assign dest");
        assert_eq!(
            dest_expr.sort().bitvec_width(),
            Some(8),
            "any_raw for u8 destination should produce bv8"
        );
    });
}

/// codegen_kani_any_raw for i64 creates bitvec(64).
#[test]
fn test_any_raw_i64_creates_bitvec64_symbolic() {
    with_test_ay_ctx_for_source(KANI_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "i64_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = return_dest_place();
        codegen.codegen_kani_any_raw(&dest);

        let dest_expr =
            assigned_expr_for_place(&mut codegen, &dest).expect("any_raw should assign dest");
        assert_eq!(
            dest_expr.sort().bitvec_width(),
            Some(64),
            "any_raw for i64 destination should produce bv64"
        );
    });
}

// ═══════════════════════════════════════════════════════════════════════
// codegen_kani_any_raw — enum discriminant constraint path
// ═══════════════════════════════════════════════════════════════════════

/// codegen_kani_any_raw for a unit enum adds a bvult discriminant constraint.
#[test]
fn test_any_raw_unit_enum_adds_discriminant_constraint() {
    let source = r#"
pub enum Color { Red, Green, Blue }
pub fn enum_probe(x: Color) -> Color { x }
"#;
    with_test_ay_ctx_for_source(source, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "enum_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let constraints_before = constraint_count(&codegen);
        let dest = return_dest_place();
        codegen.codegen_kani_any_raw(&dest);

        // Verify: destination assigned
        let dest_expr =
            assigned_expr_for_place(&mut codegen, &dest).expect("enum any_raw should assign dest");
        // Unit enums with <=65536 variants use 32 bits
        assert_eq!(
            dest_expr.sort().bitvec_width(),
            Some(32),
            "3-variant unit enum should use bv32 for discriminant"
        );

        // Verify: discriminant validity constraint added (value < 3)
        assert!(
            constraint_count(&codegen) > constraints_before,
            "any_raw for unit enum should add discriminant validity constraint"
        );
    });
}

/// codegen_kani_any_raw for a single-variant enum still adds a constraint.
#[test]
fn test_any_raw_single_variant_enum_adds_constraint() {
    let source = r#"
pub enum Singleton { Only }
pub fn singleton_probe(x: Singleton) -> Singleton { x }
"#;
    with_test_ay_ctx_for_source(source, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "singleton_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let constraints_before = constraint_count(&codegen);
        let dest = return_dest_place();
        codegen.codegen_kani_any_raw(&dest);

        let dest_expr =
            assigned_expr_for_place(&mut codegen, &dest).expect("singleton any_raw should assign");
        assert_eq!(dest_expr.sort().bitvec_width(), Some(32));

        // Single-variant enum: value < 1, i.e., value == 0
        assert!(
            constraint_count(&codegen) > constraints_before,
            "single-variant enum should still add discriminant constraint"
        );
    });
}

// ═══════════════════════════════════════════════════════════════════════
// codegen_kani_any_raw — tuple flattening
// ═══════════════════════════════════════════════════════════════════════

/// codegen_kani_any_raw for a tuple flattens into per-field symbolics in
/// flattened_tuples, NOT in current_env.
#[test]
fn test_any_raw_tuple_flattens_fields() {
    let source = r#"
pub fn tuple_probe(x: (u32, bool)) -> (u32, bool) { x }
"#;
    with_test_ay_ctx_for_source(source, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "tuple_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = return_dest_place();
        let base_name = codegen.ssa_base_name(&dest);
        codegen.codegen_kani_any_raw(&dest);

        // Verify: tuple goes into flattened_tuples, not current_env
        assert!(
            codegen.flattened_tuples.contains_key(base_name.as_str()),
            "tuple any_raw should populate flattened_tuples"
        );

        let fields = &codegen.flattened_tuples[base_name.as_str()];
        assert_eq!(fields.len(), 2, "(u32, bool) should produce 2 field variables");

        // Field 0 should be bitvec(32) for u32
        assert_eq!(fields[0].sort().bitvec_width(), Some(32), "tuple field 0 (u32) should be bv32");
        // Field 1 should be bool
        assert!(fields[1].sort().is_bool(), "tuple field 1 (bool) should be Bool sort");
    });
}

/// codegen_kani_any_raw for (u8, u16, u64) produces three correctly-sorted fields.
#[test]
fn test_any_raw_triple_tuple_field_sorts() {
    let source = r#"
pub fn triple_probe(x: (u8, u16, u64)) -> (u8, u16, u64) { x }
"#;
    with_test_ay_ctx_for_source(source, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "triple_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = return_dest_place();
        let base_name = codegen.ssa_base_name(&dest);
        codegen.codegen_kani_any_raw(&dest);

        let fields = &codegen.flattened_tuples[base_name.as_str()];
        assert_eq!(fields.len(), 3);
        assert_eq!(fields[0].sort().bitvec_width(), Some(8), "field 0 (u8) → bv8");
        assert_eq!(fields[1].sort().bitvec_width(), Some(16), "field 1 (u16) → bv16");
        assert_eq!(fields[2].sort().bitvec_width(), Some(64), "field 2 (u64) → bv64");
    });
}

// ═══════════════════════════════════════════════════════════════════════
// codegen_kani_any_raw — array path
// ═══════════════════════════════════════════════════════════════════════

/// codegen_kani_any_raw for an array creates an SMT Array sort with element stores.
#[test]
fn test_any_raw_array_creates_smt_array() {
    let source = r#"
pub fn array_probe(x: [u32; 3]) -> [u32; 3] { x }
"#;
    with_test_ay_ctx_for_source(source, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "array_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = return_dest_place();
        codegen.codegen_kani_any_raw(&dest);

        let dest_expr =
            assigned_expr_for_place(&mut codegen, &dest).expect("array any_raw should assign dest");
        assert!(dest_expr.sort().is_array(), "array any_raw should produce Array sort");

        // Array with 3 elements: the result should be built from store operations
        // (base array with 3 element stores)
        let debug_repr = format!("{:?}", dest_expr.value());
        assert!(
            debug_repr.contains("Store"),
            "3-element array should use Store operations, got {:?}",
            dest_expr.value()
        );
    });
}

#[test]
fn test_any_raw_char_array_constrains_elements() {
    let source = r#"
pub fn char_array_probe(x: [char; 2]) -> [char; 2] { x }
"#;
    with_test_ay_ctx_for_source(source, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "char_array_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let constraints_before = constraint_count(&codegen);
        let dest = return_dest_place();
        codegen.codegen_kani_any_raw(&dest);

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("char array any_raw should assign dest");
        assert!(dest_expr.sort().is_array(), "char array any_raw should produce Array sort");
        assert_eq!(
            constraint_count(&codegen),
            constraints_before + 2,
            "each char array element should get a Unicode scalar constraint"
        );
    });
}

/// codegen_kani_any_raw for [u8; 0] (zero-length array) produces an array with no stores.
#[test]
fn test_any_raw_zero_length_array() {
    let source = r#"
pub fn empty_array_probe(x: [u8; 0]) -> [u8; 0] { x }
"#;
    with_test_ay_ctx_for_source(source, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "empty_array_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = return_dest_place();
        codegen.codegen_kani_any_raw(&dest);

        // Zero-length array [u8; 0] is a ZST — codegen_kani_any_raw should
        // either produce an array with no stores, or skip assignment entirely.
        let dest_expr = assigned_expr_for_place(&mut codegen, &dest);
        if let Some(expr) = &dest_expr {
            assert!(expr.sort().is_array(), "zero-length array should produce Array sort");
            // Should NOT contain Store operations (no elements to store)
            let debug_repr = format!("{:?}", expr.value());
            assert!(
                !debug_repr.contains("Store"),
                "zero-length array should not use Store operations"
            );
        }
        // ZST may not be assigned at all — that's the expected path
    });
}

// ═══════════════════════════════════════════════════════════════════════
// codegen_kani_assume — path constraint emission
// ═══════════════════════════════════════════════════════════════════════

/// codegen_kani_assume adds a constraint to the SMT context.
#[test]
fn test_assume_adds_constraint() {
    with_test_ay_ctx_for_source(KANI_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bool_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);

        let constraints_before = constraint_count(&codegen);

        // Call codegen_kani_assume with the first arg (a bool operand)
        codegen.codegen_kani_assume(&[local_operand(1)]);

        assert!(
            constraint_count(&codegen) > constraints_before,
            "codegen_kani_assume should add at least one constraint"
        );
    });
}

/// codegen_kani_assume with empty args is a no-op.
#[test]
fn test_assume_empty_args_noop() {
    with_test_ay_ctx_for_source(KANI_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bool_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let constraints_before = constraint_count(&codegen);
        codegen.codegen_kani_assume(&[]);

        assert_eq!(
            constraint_count(&codegen),
            constraints_before,
            "codegen_kani_assume with no args should not add constraints"
        );
    });
}

// ═══════════════════════════════════════════════════════════════════════
// codegen_kani_assert — violation recording
// ═══════════════════════════════════════════════════════════════════════

/// codegen_kani_assert records a property violation in the context.
#[test]
fn test_assert_records_violation() {
    with_test_ay_ctx_for_source(KANI_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bool_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);

        let violations_before = codegen.ctx.bmc_vc.violations.len();

        codegen.codegen_kani_assert(&[local_operand(1)]);

        assert_eq!(
            codegen.ctx.bmc_vc.violations.len(),
            violations_before + 1,
            "codegen_kani_assert should record exactly one property violation"
        );
    });
}

/// codegen_kani_assert maps to PropertyKind::Assertion via the "kani_assert" label.
#[test]
fn test_assert_uses_kani_assert_label() {
    with_test_ay_ctx_for_source(KANI_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bool_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);

        codegen.codegen_kani_assert(&[local_operand(1)]);

        // Violation should use the "kani_assert" label which maps to PropertyKind::Assertion
        let last_violation = codegen.ctx.bmc_vc.violations.last().expect("expected a violation");
        assert_eq!(
            last_violation.kind,
            trust_mc_core::violation::PropertyKind::Assertion,
            "kani_assert should map to PropertyKind::Assertion"
        );
    });
}

/// codegen_kani_assert with empty args records a conservative unconditional violation.
/// This prevents false PROOF from silently dropped assertions.
#[test]
fn test_assert_empty_args_records_conservative_violation() {
    with_test_ay_ctx_for_source(KANI_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bool_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let violations_before = codegen.ctx.bmc_vc.violations.len();
        codegen.codegen_kani_assert(&[]);

        assert_eq!(
            codegen.ctx.bmc_vc.violations.len(),
            violations_before + 1,
            "codegen_kani_assert with no args should record conservative violation"
        );
    });
}

// ═══════════════════════════════════════════════════════════════════════
// codegen_kani_cover — cover property registration
// ═══════════════════════════════════════════════════════════════════════

/// codegen_kani_cover registers a cover property in the context.
#[test]
fn test_cover_registers_property() {
    with_test_ay_ctx_for_source(KANI_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bool_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);

        let covers_before = codegen.ctx.bmc_vc.model_queries.len();

        codegen.codegen_kani_cover(&[local_operand(1)]);

        assert_eq!(
            codegen.ctx.bmc_vc.model_queries.len(),
            covers_before + 1,
            "codegen_kani_cover should register one cover property"
        );
    });
}

/// codegen_kani_cover with empty args is a no-op.
#[test]
fn test_cover_empty_args_noop() {
    with_test_ay_ctx_for_source(KANI_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bool_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let covers_before = codegen.ctx.bmc_vc.model_queries.len();
        codegen.codegen_kani_cover(&[]);

        assert_eq!(
            codegen.ctx.bmc_vc.model_queries.len(),
            covers_before,
            "codegen_kani_cover with no args should not register a cover property"
        );
    });
}

/// codegen_kani_cover property name starts with ay_cover_ prefix.
#[test]
fn test_cover_property_naming() {
    with_test_ay_ctx_for_source(KANI_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bool_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);

        let covers_before = codegen.ctx.bmc_vc.model_queries.len();
        let constraints_before = constraint_count(&codegen);
        codegen.codegen_kani_cover(&[local_operand(1)]);

        assert_eq!(
            codegen.ctx.bmc_vc.model_queries.len(),
            covers_before + 1,
            "codegen_kani_cover should register exactly one model query"
        );
        let last_query = codegen.ctx.bmc_vc.model_queries.last().expect("cover query");
        match last_query.value() {
            ExprValue::Var { name } => {
                assert!(
                    name.starts_with("ay_cover_"),
                    "cover query variable should start with ay_cover_, got {name}"
                );
            }
            other => panic!("cover query should be a variable, got {:?}", other),
        }
        assert!(
            codegen.ctx.bmc_vc.decls.iter().any(|decl| {
                matches!(
                    decl,
                    trust_mc_core::decl::Decl::Const { name, sort }
                        if name.starts_with("ay_cover_") && sort.is_bool()
                )
            }),
            "expected a Bool const declaration named ay_cover_*"
        );
        // Cover property should add constraints (the ay_cover_N = condition assertion)
        assert!(
            constraint_count(&codegen) > constraints_before,
            "codegen_kani_cover should add constraint for cover property definition"
        );
    });
}

// ═══════════════════════════════════════════════════════════════════════
// codegen_float_to_int_in_range — symbolic bool over-approximation
// ═══════════════════════════════════════════════════════════════════════

/// codegen_float_to_int_in_range assigns a Bool-sorted expression to destination.
#[test]
fn test_float_to_int_in_range_produces_bool() {
    let source = r#"
pub fn f32_probe(x: f32) -> f32 { x }
"#;
    with_test_ay_ctx_for_source(source, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "f32_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = return_dest_place();

        // Construct GenericArgs with two type args (Float, Int) — use empty GenericArgs
        // since the function handles the fallback case gracefully
        let empty_args = rustc_public::ty::GenericArgs(vec![]);
        codegen.codegen_float_to_int_in_range(&empty_args, &[], &dest);

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("float_to_int_in_range should assign destination");
        assert!(
            dest_expr.sort().is_bool(),
            "float_to_int_in_range should produce a Bool-sorted expression"
        );

        // Over-approximation: should NOT be a constant (it's a fresh symbolic)
        assert!(
            !matches!(dest_expr.value(), ExprValue::BoolConst(_)),
            "float_to_int_in_range should produce a symbolic bool, not a constant"
        );
    });
}

/// The over-approximation symbolic bool is a Var, not a constant.
#[test]
fn test_float_to_int_in_range_symbolic_not_constant() {
    let source = r#"
pub fn f64_probe(x: f64) -> f64 { x }
"#;
    with_test_ay_ctx_for_source(source, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "f64_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = return_dest_place();
        let empty_args = rustc_public::ty::GenericArgs(vec![]);
        codegen.codegen_float_to_int_in_range(&empty_args, &[], &dest);

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("float_to_int_in_range should assign destination");

        // Should NOT be a constant — it's a fresh symbolic for soundness
        assert!(
            !matches!(dest_expr.value(), ExprValue::BoolConst(_)),
            "float_to_int_in_range result should be symbolic (Var), not a BoolConst"
        );
    });
}

/// Part of #3840: Concrete f32 -> u16 fast path returns BoolConst(true).
/// 5.6f32 truncates to 5.0, which fits in u16 [0, 65535].
#[test]
fn test_float_to_int_in_range_concrete_true_f32_u16() {
    let source = r#"
pub fn f32_u16_probe(x: f32, y: u16) -> bool { true }
"#;
    with_test_ay_ctx_for_source(source, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "f32_u16_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Seed local_1 (f32 arg) with IEEE 754 bits for 5.6f32
        let f32_bits = 5.6f32.to_bits();
        let place1 = Place { local: Local::from(1usize), projection: vec![] };
        let base1 = codegen.ssa_base_name(&place1);
        codegen.env_update(base1, Expr::bitvec_const(f32_bits as i128, 32));

        // Extract Ty objects from arg locals
        let arg_locals = body.arg_locals();
        let float_ty = arg_locals[0].ty; // f32
        let int_ty = arg_locals[1].ty; // u16

        let gen_args = rustc_public::ty::GenericArgs(vec![
            GenericArgKind::Type(float_ty),
            GenericArgKind::Type(int_ty),
        ]);

        let dest = return_dest_place();
        codegen.codegen_float_to_int_in_range(&gen_args, &[local_operand(1)], &dest);

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("float_to_int_in_range should assign destination");
        assert!(dest_expr.sort().is_bool());
        assert!(
            matches!(dest_expr.value(), ExprValue::BoolConst(true)),
            "5.6f32 -> u16 should produce BoolConst(true), got {:?}",
            dest_expr.value()
        );
    });
}

/// Part of #3840: Concrete f32 -> i8 fast path returns BoolConst(false).
/// 145.7f32 truncates to 145.0, which exceeds i8 max (127).
#[test]
fn test_float_to_int_in_range_concrete_false_f32_i8() {
    let source = r#"
pub fn f32_i8_probe(x: f32, y: i8) -> bool { true }
"#;
    with_test_ay_ctx_for_source(source, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "f32_i8_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Seed local_1 (f32 arg) with IEEE 754 bits for 145.7f32
        let f32_bits = 145.7f32.to_bits();
        let place1 = Place { local: Local::from(1usize), projection: vec![] };
        let base1 = codegen.ssa_base_name(&place1);
        codegen.env_update(base1, Expr::bitvec_const(f32_bits as i128, 32));

        let arg_locals = body.arg_locals();
        let float_ty = arg_locals[0].ty; // f32
        let int_ty = arg_locals[1].ty; // i8

        let gen_args = rustc_public::ty::GenericArgs(vec![
            GenericArgKind::Type(float_ty),
            GenericArgKind::Type(int_ty),
        ]);

        let dest = return_dest_place();
        codegen.codegen_float_to_int_in_range(&gen_args, &[local_operand(1)], &dest);

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("float_to_int_in_range should assign destination");
        assert!(dest_expr.sort().is_bool());
        assert!(
            matches!(dest_expr.value(), ExprValue::BoolConst(false)),
            "145.7f32 -> i8 should produce BoolConst(false), got {:?}",
            dest_expr.value()
        );
    });
}

/// Part of #3840: Too-wide target (f64 -> u64) stays symbolic.
/// u64 has 64 bits > f64 mantissa (53 bits), so concrete path defers.
#[test]
fn test_float_to_int_in_range_wide_target_stays_symbolic() {
    let source = r#"
pub fn f64_u64_probe(x: f64, y: u64) -> bool { true }
"#;
    with_test_ay_ctx_for_source(source, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "f64_u64_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Seed local_1 (f64 arg) with IEEE 754 bits for 1.0f64
        let f64_bits = 1.0f64.to_bits();
        let place1 = Place { local: Local::from(1usize), projection: vec![] };
        let base1 = codegen.ssa_base_name(&place1);
        codegen.env_update(base1, Expr::bitvec_const(f64_bits as i128, 64));

        let arg_locals = body.arg_locals();
        let float_ty = arg_locals[0].ty; // f64
        let int_ty = arg_locals[1].ty; // u64

        let gen_args = rustc_public::ty::GenericArgs(vec![
            GenericArgKind::Type(float_ty),
            GenericArgKind::Type(int_ty),
        ]);

        let dest = return_dest_place();
        codegen.codegen_float_to_int_in_range(&gen_args, &[local_operand(1)], &dest);

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("float_to_int_in_range should assign destination");
        assert!(dest_expr.sort().is_bool());
        // u64 width (64) > f64 mantissa (53), so should stay symbolic
        assert!(
            !matches!(dest_expr.value(), ExprValue::BoolConst(_)),
            "f64 -> u64 should stay symbolic (width exceeds mantissa), got {:?}",
            dest_expr.value()
        );
    });
}

// ═══════════════════════════════════════════════════════════════════════
// codegen_kani_value_view — bv2int conversion
// ═══════════════════════════════════════════════════════════════════════

/// codegen_kani_value_view for unsigned bitvec produces Int sort via bv2int.
#[test]
fn test_value_view_unsigned_bv_to_int() {
    with_test_ay_ctx_for_source(KANI_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "u32_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);

        let dest = return_dest_place();
        codegen.codegen_kani_value_view(&[local_operand(1)], &dest);

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("value_view should assign destination");
        assert!(
            dest_expr.sort().is_int(),
            "value_view for u32 should produce Int sort (via bv2int)"
        );
        // Should be bv2int (unsigned), not bv2int_signed (which expands to ITE)
        assert!(
            matches!(dest_expr.value(), ExprValue::Bv2Int(_)),
            "value_view for unsigned type should use Bv2Int, got {:?}",
            dest_expr.value()
        );
    });
}

/// codegen_kani_value_view for signed bitvec produces Int sort via bv2int_signed.
#[test]
fn test_value_view_signed_bv_to_int() {
    with_test_ay_ctx_for_source(KANI_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "i64_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);

        let dest = return_dest_place();
        codegen.codegen_kani_value_view(&[local_operand(1)], &dest);

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("value_view should assign destination");
        assert!(dest_expr.sort().is_int(), "value_view for i64 should produce Int sort");
        // bv2int_signed expands to ITE(msb==1, bv2int-2^width, bv2int)
        assert!(
            matches!(dest_expr.value(), ExprValue::Ite { .. }),
            "value_view for signed type should expand bv2int_signed to ITE, got {:?}",
            dest_expr.value()
        );
    });
}

/// codegen_kani_value_view for bool produces bool passthrough (no conversion).
#[test]
fn test_value_view_bool_passthrough() {
    with_test_ay_ctx_for_source(KANI_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bool_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);

        let dest = return_dest_place();
        codegen.codegen_kani_value_view(&[local_operand(1)], &dest);

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("value_view should assign destination");
        assert!(dest_expr.sort().is_bool(), "value_view for bool should pass through as Bool sort");
    });
}

/// codegen_kani_value_view with empty args emits a fallback assignment.
/// This prevents downstream codegen from seeing an uninitialized destination.
#[test]
fn test_value_view_empty_args_emits_fallback() {
    with_test_ay_ctx_for_source(KANI_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "u32_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = return_dest_place();
        codegen.codegen_kani_value_view(&[], &dest);

        // Production code now assigns a fallback value to prevent uninitialized
        // destinations. This is a correctness improvement over the old no-op.
        let dest_expr = assigned_expr_for_place(&mut codegen, &dest);
        assert!(dest_expr.is_some(), "value_view with no args should assign fallback destination");
    });
}

// ═══════════════════════════════════════════════════════════════════════
// codegen_kani_value_view — char Unicode range constraint
// ═══════════════════════════════════════════════════════════════════════

/// codegen_kani_value_view for char adds Unicode range constraints (0..=0x10FFFF).
#[test]
fn test_value_view_char_adds_unicode_constraints() {
    let source = r#"
pub fn char_probe(x: char) -> char { x }
"#;
    with_test_ay_ctx_for_source(source, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "char_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);

        let constraints_before = constraint_count(&codegen);
        let dest = return_dest_place();
        codegen.codegen_kani_value_view(&[local_operand(1)], &dest);

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("value_view for char should assign destination");
        // char → Int sort (unsigned bv2int)
        assert!(dest_expr.sort().is_int(), "value_view for char should produce Int sort");

        // Should add at least 2 constraints: lower bound (>= 0) and upper bound (<= 0x10FFFF)
        assert!(
            constraint_count(&codegen) >= constraints_before + 2,
            "value_view for char should add Unicode range constraints (>= 0 and <= 0x10FFFF), \
             had {} before, now {}",
            constraints_before,
            constraint_count(&codegen)
        );
    });
}

/// codegen_kani_value_view for char must exclude surrogates (0xD800–0xDFFF).
///
/// The Rust `char` type is a Unicode scalar value: [0, 0xD7FF] ∪ [0xE000, 0x10FFFF].
/// Surrogates (0xD800–0xDFFF) are NOT valid scalar values and must be excluded.
/// A constraint that only checks `val >= 0 && val <= 0x10FFFF` without excluding
/// surrogates is unsound for char validation.
///
/// Part of #2932: dual-encoding parity — CHC path correctly excludes surrogates
/// (char_nondet_bounds at codegen_call_kani_hooks.rs:516-522) but BMC value_view
/// path must also exclude them.
#[test]
fn test_value_view_char_excludes_surrogates() {
    let source = r#"
pub fn char_probe(x: char) -> char { x }
"#;
    with_test_ay_ctx_for_source(source, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "char_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);

        let constraints_before = constraint_count(&codegen);
        let dest = return_dest_place();
        codegen.codegen_kani_value_view(&[local_operand(1)], &dest);

        // Collect the newly added constraints.
        let new_constraints = &codegen.ctx.bmc_vc.constraints[constraints_before..];
        let constraint_strs: Vec<String> =
            new_constraints.iter().map(ToString::to_string).collect();

        // There should be a constraint that references 0xD7FF or 0xE000 to exclude
        // surrogates. A constraint using only 0x10FFFF as the upper bound is
        // insufficient — it allows surrogates (0xD800–0xDFFF).
        let excludes_surrogates = constraint_strs.iter().any(|s| {
            // Look for surrogate boundary constants: 0xD7FF = 55295, 0xE000 = 57344
            s.contains("55295")
                || s.contains("57344")
                || s.contains("d7ff")
                || s.contains("D7FF")
                || s.contains("e000")
                || s.contains("E000")
        });
        assert!(
            excludes_surrogates,
            "char value_view MUST exclude Unicode surrogates (0xD800-0xDFFF). \
             CHC path correctly constrains to [0,0xD7FF]∪[0xE000,0x10FFFF] but \
             BMC path only constrains to [0,0x10FFFF]. Constraints emitted: {:?}",
            constraint_strs
        );
    });
}

// ═══════════════════════════════════════════════════════════════════════
// SMT pattern verification — assert negation and cover conjunction
// ═══════════════════════════════════════════════════════════════════════

/// kani::assert(cond) records NOT(cond) as the violation — verify negation.
#[test]
fn test_assert_violation_is_negated_condition() {
    with_test_ay_ctx_for_source(KANI_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bool_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);

        codegen.codegen_kani_assert(&[local_operand(1)]);

        // The violation predicate should be Bool-sorted
        let last_violation = codegen.ctx.bmc_vc.violations.last().expect("violation");
        assert!(
            last_violation.condition.sort().is_bool(),
            "violation predicate should be Bool-sorted"
        );
        assert!(
            matches!(last_violation.condition.value(), ExprValue::Not(_)),
            "kani_assert should record a negated violation predicate, got {:?}",
            last_violation.condition.value()
        );
    });
}

/// Multiple codegen_kani_assert calls accumulate violations.
#[test]
fn test_multiple_asserts_accumulate() {
    with_test_ay_ctx_for_source(KANI_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "two_bool_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);

        let violations_before = codegen.ctx.bmc_vc.violations.len();

        codegen.codegen_kani_assert(&[local_operand(1)]);
        codegen.codegen_kani_assert(&[local_operand(2)]);

        assert_eq!(
            codegen.ctx.bmc_vc.violations.len(),
            violations_before + 2,
            "two bool kani_assert calls should record two violations"
        );
    });
}

/// codegen_kani_assert with non-bool args coerces to bool and records violations (#2619).
/// After commit 68d0afc (Fix kani assume/assert/cover silently dropping non-bool conditions),
/// non-bool operands are coerced via `bv != 0` / `int != 0` instead of being silently dropped.
#[test]
fn test_assert_non_bool_args_coerced() {
    with_test_ay_ctx_for_source(KANI_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "two_u32_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);

        let violations_before = codegen.ctx.bmc_vc.violations.len();

        // Non-bool u32 args are coerced to bool (bv != 0) and record violations
        codegen.codegen_kani_assert(&[local_operand(1)]); // u32 → coerced to bool
        codegen.codegen_kani_assert(&[local_operand(2)]); // u32 → coerced to bool

        // Each non-bool arg is coerced and produces a violation
        assert_eq!(
            codegen.ctx.bmc_vc.violations.len(),
            violations_before + 2,
            "codegen_kani_assert with non-bool u32 args should coerce and record violations (#2619)"
        );
    });
}

/// Multiple codegen_kani_cover calls accumulate cover properties.
#[test]
fn test_multiple_covers_accumulate() {
    with_test_ay_ctx_for_source(KANI_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bool_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);

        let queries_before = codegen.ctx.bmc_vc.model_queries.len();

        codegen.codegen_kani_cover(&[local_operand(1)]);
        codegen.codegen_kani_cover(&[local_operand(1)]);

        // Each cover call adds one model query (the ay_cover_N predicate)
        assert_eq!(
            codegen.ctx.bmc_vc.model_queries.len(),
            queries_before + 2,
            "two codegen_kani_cover calls should register two model queries"
        );
    });
}

/// codegen_kani_assume with non-bool (BitVec) args coerces to bool and adds constraint (#2619).
/// Regression test: before commit 68d0afc, non-bool conditions were silently dropped.
#[test]
fn test_assume_non_bool_args_coerced() {
    with_test_ay_ctx_for_source(KANI_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "u32_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);

        let constraints_before = constraint_count(&codegen);

        // Non-bool u32 arg should be coerced to bool (bv != 0) and add a constraint
        codegen.codegen_kani_assume(&[local_operand(1)]);

        assert!(
            constraint_count(&codegen) > constraints_before,
            "codegen_kani_assume with non-bool u32 arg should coerce and add constraint (#2619)"
        );
    });
}

/// codegen_kani_cover with non-bool (BitVec) args coerces to bool and registers cover query (#2619).
/// Regression test: before commit 68d0afc, non-bool conditions were silently dropped.
#[test]
fn test_cover_non_bool_args_coerced() {
    with_test_ay_ctx_for_source(KANI_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "u32_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);

        let queries_before = codegen.ctx.bmc_vc.model_queries.len();

        // Non-bool u32 arg should be coerced to bool (bv != 0) and register a cover query
        codegen.codegen_kani_cover(&[local_operand(1)]);

        assert_eq!(
            codegen.ctx.bmc_vc.model_queries.len(),
            queries_before + 1,
            "codegen_kani_cover with non-bool u32 arg should coerce and register cover query (#2619)"
        );
    });
}
