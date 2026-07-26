// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Environment and phi merge unit tests.

use super::*;

const ENV_ASSERT_SOURCE: &str = r#"
pub fn env_assert_probe() {}
"#;

// =============================================================================
// Tests for env.rs functionality (phi merging and sort conversion)
// =============================================================================

/// Test convert_expr_to_sort with BitVec to Int conversion.
#[test]
fn test_convert_bitvec_to_int() {
    let bv_expr = Expr::bitvec_const(255, 8);
    let converted = StatementCodegen::convert_expr_to_sort(bv_expr, &Sort::int(), Some(false));

    assert!(converted.sort().is_int());
    assert!(matches!(converted.value(), ExprValue::Bv2Int(..)));
}

/// Regression for #2432: signed BitVec -> Int must preserve signed interpretation.
#[test]
fn test_convert_signed_bitvec_to_int_uses_bv2int_signed() {
    let bv_expr = Expr::bitvec_const(255, 8);
    let converted = StatementCodegen::convert_expr_to_sort(bv_expr, &Sort::int(), Some(true));

    assert!(converted.sort().is_int());
    assert!(matches!(converted.value(), ExprValue::Ite { .. }));
}

/// Test convert_expr_to_sort with Int to BitVec conversion.
#[test]
fn test_convert_int_to_bitvec() {
    let int_expr = Expr::var("x", Sort::int());
    let converted = StatementCodegen::convert_expr_to_sort(int_expr, &Sort::bitvec(32), None);

    assert!(converted.sort().is_bitvec());
    assert_eq!(converted.sort().bitvec_width(), Some(32));
    assert!(matches!(converted.value(), ExprValue::Int2Bv { .. }));
}

/// Test convert_expr_to_sort with same sort (no conversion needed).
#[test]
fn test_convert_same_sort_noop() {
    let int_expr = Expr::var("x", Sort::int());
    let converted = StatementCodegen::convert_expr_to_sort(int_expr, &Sort::int(), None);

    // Should return the same expression unchanged
    assert!(converted.sort().is_int());
    assert!(matches!(converted.value(), ExprValue::Var { .. }));
}

/// Test convert_expr_to_sort with Ratio datatype to Int.
#[test]
fn test_convert_ratio_datatype_to_int() {
    let ratio_sort = struct_sort("num_rational::Ratio", [("numer", Sort::int())]);
    let ratio_expr = Expr::var("ratio", ratio_sort);

    let converted = StatementCodegen::convert_expr_to_sort(ratio_expr, &Sort::int(), None);

    assert!(converted.sort().is_int());
    match converted.value() {
        ExprValue::DatatypeSelector { datatype_name, selector_name, .. } => {
            assert_eq!(datatype_name, "num_rational::Ratio");
            assert_eq!(selector_name, "numer");
        }
        other => panic!("expected DatatypeSelector, got {:?}", other),
    }
}

/// Regression for #2432: BigInt-like datatypes with BitVec payloads should stay constrained.
#[test]
fn test_convert_bigint_datatype_bitvec_field_to_int_uses_selector_conversion() {
    let bigint_sort = struct_sort("num_bigint::BigIntNoInt", [("digits", Sort::bitvec(16))]);
    let bigint_expr = Expr::var("bigint_no_int", bigint_sort);

    let converted = StatementCodegen::convert_expr_to_sort(bigint_expr, &Sort::int(), Some(false));

    assert!(converted.sort().is_int());
    match converted.value() {
        ExprValue::Bv2Int(inner) => match inner.value() {
            ExprValue::DatatypeSelector { datatype_name, selector_name, .. } => {
                assert_eq!(datatype_name, "num_bigint::BigIntNoInt");
                assert_eq!(selector_name, "digits");
            }
            other => panic!("expected DatatypeSelector inside Bv2Int, got {:?}", other),
        },
        ExprValue::Var { name } => {
            panic!("expected constrained selector conversion, got fallback var '{name}'")
        }
        other => panic!("expected Bv2Int conversion, got {:?}", other),
    }
}

/// Regression for #2432: signed Datatype(BitVec) -> Int should use signed conversion semantics.
#[test]
fn test_convert_signed_bigint_datatype_bitvec_field_to_int_uses_bv2int_signed() {
    let bigint_sort = struct_sort("num_bigint::BigIntNoIntSigned", [("digits", Sort::bitvec(16))]);
    let bigint_expr = Expr::var("bigint_no_int_signed", bigint_sort);

    let converted = StatementCodegen::convert_expr_to_sort(bigint_expr, &Sort::int(), Some(true));

    assert!(converted.sort().is_int());
    assert!(
        matches!(converted.value(), ExprValue::Ite { .. }),
        "expected signed bv2int expansion (Ite), got {:?}",
        converted.value()
    );
}

/// Regression for #2432: multi-constructor BigInt-like enums should use constructor guards.
#[test]
fn test_convert_bigint_enum_to_int_uses_constructor_guards_without_fresh_fallback() {
    let bigint_sort = enum_sort(
        "num_bigint::BigIntEnum",
        vec![
            ("Small", vec![("small_bits", Sort::bitvec(16))]),
            ("Large", vec![("large_int", Sort::int())]),
        ],
    );
    let bigint_expr = Expr::var("bigint_enum", bigint_sort);

    let converted = StatementCodegen::convert_expr_to_sort(bigint_expr, &Sort::int(), Some(false));

    assert!(converted.sort().is_int());
    match converted.value() {
        ExprValue::Ite { cond, then_expr, else_expr } => {
            assert!(matches!(
                cond.value(),
                ExprValue::DatatypeTester { constructor_name, .. } if constructor_name == "Small"
            ));
            assert!(matches!(then_expr.value(), ExprValue::Bv2Int(..)));
            assert!(matches!(else_expr.value(), ExprValue::DatatypeSelector { .. }));
            let rendered = converted.to_string();
            assert!(
                rendered.contains("small_bits"),
                "expected small_bits selector in guarded conversion: {rendered}"
            );
            assert!(
                rendered.contains("large_int"),
                "expected large_int selector in guarded conversion: {rendered}"
            );
            assert!(
                !rendered.contains("bigint_phi_conv_"),
                "unexpected fresh fallback in fully-covered constructors: {rendered}"
            );
        }
        other => panic!("expected constructor-guarded Ite, got {:?}", other),
    }
}

/// Regression for #2432: missing payload constructors should retain fresh-fallback branch.
#[test]
fn test_convert_bigint_enum_to_int_uses_fresh_fallback_for_missing_constructor_payload() {
    let bigint_sort = enum_sort(
        "num_bigint::BigIntPartialEnum",
        vec![("Unit", Vec::<(&str, Sort)>::new()), ("Packed", vec![("payload", Sort::bitvec(8))])],
    );
    let bigint_expr = Expr::var("bigint_partial_enum", bigint_sort);

    let converted = StatementCodegen::convert_expr_to_sort(bigint_expr, &Sort::int(), Some(false));

    assert!(converted.sort().is_int());
    match converted.value() {
        ExprValue::Ite { cond, then_expr, else_expr } => {
            assert!(matches!(
                cond.value(),
                ExprValue::DatatypeTester { constructor_name, .. } if constructor_name == "Packed"
            ));
            assert!(matches!(then_expr.value(), ExprValue::Bv2Int(..)));
            match else_expr.value() {
                ExprValue::Var { name } => {
                    assert!(
                        name.starts_with("bigint_phi_conv_"),
                        "expected bigint fallback symbol, got {name}"
                    );
                }
                other => panic!("expected fresh fallback var, got {:?}", other),
            }
            let rendered = converted.to_string();
            assert!(
                rendered.contains("payload"),
                "expected payload selector in guarded conversion: {rendered}"
            );
        }
        other => panic!("expected constructor-guarded Ite with fallback, got {:?}", other),
    }
}

/// Regression for #2295: phi harmonization should unwrap single-field tuple datatypes.
#[test]
fn test_convert_single_field_tuple_datatype_to_bitvec() {
    let tuple_sort = struct_sort("Tuple_bv64", [("fld_0", Sort::bitvec(64))]);
    let tuple_expr = Expr::var("tuple", tuple_sort);

    let converted = StatementCodegen::convert_expr_to_sort(tuple_expr, &Sort::bitvec(64), None);

    assert_eq!(converted.sort(), &Sort::bitvec(64));
    match converted.value() {
        ExprValue::DatatypeSelector { datatype_name, selector_name, .. } => {
            assert_eq!(datatype_name, "Tuple_bv64");
            assert_eq!(selector_name, "fld_0");
        }
        other => panic!("expected DatatypeSelector, got {:?}", other),
    }
}

/// Regression for #2432: signed widening must sign-extend.
#[test]
fn test_convert_signed_bitvec_widen_uses_sign_extend() {
    let bv_expr = Expr::bitvec_const(255, 8);
    let converted = StatementCodegen::convert_expr_to_sort(bv_expr, &Sort::bitvec(32), Some(true));

    assert_eq!(converted.sort().bitvec_width(), Some(32));
    assert!(matches!(
        converted.value(),
        ExprValue::BvSignExtend { extra_bits, .. } if *extra_bits == 24
    ));
}

/// Part of #2749: unknown signedness widening defaults to unsigned.
#[test]
fn test_convert_unknown_signedness_bitvec_widen_defaults_to_unsigned() {
    let bv_expr = Expr::bitvec_const(255, 8);
    let converted = StatementCodegen::convert_expr_to_sort(bv_expr, &Sort::bitvec(32), None);

    assert_eq!(converted.sort().bitvec_width(), Some(32));
    assert!(matches!(
        converted.value(),
        ExprValue::BvZeroExtend { extra_bits, .. } if *extra_bits == 24
    ));
}

/// Regression for #2432: unsigned widening must zero-extend.
#[test]
fn test_convert_unsigned_bitvec_widen_uses_zero_extend() {
    let bv_expr = Expr::bitvec_const(255, 8);
    let converted = StatementCodegen::convert_expr_to_sort(bv_expr, &Sort::bitvec(32), Some(false));

    assert_eq!(converted.sort().bitvec_width(), Some(32));
    assert!(matches!(
        converted.value(),
        ExprValue::BvZeroExtend { extra_bits, .. } if *extra_bits == 24
    ));
}

/// Regression for #2081: conditional SSA defs should use ite, not implication.
#[test]
fn test_assert_ssa_def_with_prev_uses_ite() {
    with_test_ay_ctx_for_source(ENV_ASSERT_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "env_assert_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let base_name = "env_assert_probe::local_1";
        codegen.current_path_condition = Some(Expr::var("pc", Sort::bool()));
        let prev_expr = codegen.ctx.declare_var("x_prev", Sort::bitvec(32));
        codegen.env_update(base_name, prev_expr);

        let lhs_expr = codegen.ctx.declare_var("x_next", Sort::bitvec(32));
        let rhs_expr = Expr::bitvec_const(7u128, 32);
        codegen.assert_ssa_def(lhs_expr, rhs_expr, &base_name);

        let emitted = codegen
            .ctx
            .bmc_vc
            .constraints
            .last()
            .expect("assert_ssa_def should emit a constraint")
            .to_string();
        assert!(emitted.contains("ite"), "expected ite-based SSA definition: {emitted}");
        assert!(
            !emitted.contains("=>"),
            "unexpected implication-guarded SSA definition: {emitted}"
        );
    });
}

/// Regression for #2081: first conditional SSA def uses a stable symbolic seed.
#[test]
fn test_assert_ssa_def_without_prev_uses_symbolic_seed_ite() {
    with_test_ay_ctx_for_source(ENV_ASSERT_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "env_assert_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let base_name = "env_assert_probe::local_2";
        codegen.current_path_condition = Some(Expr::var("pc", Sort::bool()));
        let lhs_expr = codegen.ctx.declare_var("y_next", Sort::bitvec(32));
        let rhs_expr = Expr::bitvec_const(99u128, 32);
        codegen.assert_ssa_def(lhs_expr, rhs_expr, &base_name);

        let emitted = codegen
            .ctx
            .bmc_vc
            .constraints
            .last()
            .expect("assert_ssa_def should emit a constraint")
            .to_string();
        assert!(emitted.contains("ite"), "expected ite-based SSA definition: {emitted}");
        assert!(
            emitted.contains("__ssa_init_"),
            "expected symbolic pre-state seed in SSA definition: {emitted}"
        );
        assert!(
            !emitted.contains("=>"),
            "unexpected implication-guarded SSA definition: {emitted}"
        );
    });
}

/// Regression for #2081: phi merges under guarded reachability must stay total.
#[test]
fn test_phi_merge_guarded_reachability_uses_seeded_ite() {
    with_test_ay_ctx_for_source(ENV_ASSERT_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "env_assert_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let base_name = "env_assert_probe::local_phi_guarded";
        let target_bb = 1usize;

        codegen.current_path_condition = Some(Expr::var("pred_a", Sort::bool()));
        codegen.env_update(base_name, Expr::bitvec_const(1u128, 32));
        codegen.record_outgoing_edge(target_bb, Some(Expr::var("br_a", Sort::bool())));

        codegen.current_path_condition = Some(Expr::var("pred_b", Sort::bool()));
        codegen.env_update(base_name, Expr::bitvec_const(2u128, 32));
        codegen.record_outgoing_edge(target_bb, Some(Expr::var("br_b", Sort::bool())));

        codegen.initialize_block_entry_env(target_bb);

        let emitted = codegen
            .ctx
            .bmc_vc
            .constraints
            .last()
            .expect("phi merge should emit a guarded constraint")
            .to_string();
        assert!(emitted.contains("ite"), "expected ite-based phi definition: {emitted}");
        assert!(
            emitted.contains("__ssa_init_"),
            "expected symbolic pre-state seed in phi definition: {emitted}"
        );
        assert!(
            !emitted.contains("=>"),
            "unexpected implication-guarded phi definition: {emitted}"
        );
    });
}

/// Regression for #2081: missing incoming phi values must still be total with a seed.
#[test]
fn test_phi_merge_missing_incoming_uses_seeded_ite() {
    with_test_ay_ctx_for_source(ENV_ASSERT_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "env_assert_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let base_name = "env_assert_probe::local_phi_missing";
        let target_bb = 1usize;

        codegen.current_path_condition = Some(Expr::var("pred_has", Sort::bool()));
        codegen.env_update(base_name, Expr::bitvec_const(9u128, 32));
        codegen.record_outgoing_edge(target_bb, Some(Expr::var("br_has", Sort::bool())));

        codegen.current_path_condition = Some(Expr::var("pred_missing", Sort::bool()));
        codegen.current_env.remove(base_name);
        codegen.record_outgoing_edge(target_bb, Some(Expr::var("br_missing", Sort::bool())));

        codegen.initialize_block_entry_env(target_bb);

        let emitted = codegen
            .ctx
            .bmc_vc
            .constraints
            .last()
            .expect("phi merge with missing incoming should emit a guarded constraint")
            .to_string();
        assert!(emitted.contains("ite"), "expected ite-based phi definition: {emitted}");
        assert!(
            emitted.contains("__ssa_init_"),
            "expected symbolic pre-state seed in phi definition: {emitted}"
        );
        assert!(
            !emitted.contains("=>"),
            "unexpected implication-guarded phi definition: {emitted}"
        );
    });
}

// =============================================================================
// Tests for guard helpers (#2491)
// =============================================================================

/// assert_guarded without path condition emits unconditional constraint.
#[test]
fn test_assert_guarded_unconditional() {
    with_test_ay_ctx_for_source(ENV_ASSERT_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "env_assert_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        codegen.current_path_condition = None;
        let constraint = Expr::var("validity", Sort::bool());
        let before = codegen.ctx.bmc_vc.constraints.len();
        codegen.assert_guarded(constraint);

        assert!(
            codegen.ctx.bmc_vc.constraints.len() > before,
            "assert_guarded should emit a constraint"
        );
        let emitted = codegen.ctx.bmc_vc.constraints.last().unwrap().to_string();
        assert!(
            emitted.contains("validity"),
            "unconditional assert should contain the constraint directly: {emitted}"
        );
        assert!(
            !emitted.contains("=>"),
            "unconditional assert should not use implication: {emitted}"
        );
    });
}

/// assert_guarded with path condition emits pc => constraint.
#[test]
fn test_assert_guarded_with_path_condition() {
    with_test_ay_ctx_for_source(ENV_ASSERT_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "env_assert_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        codegen.current_path_condition = Some(Expr::var("pc", Sort::bool()));
        let constraint = Expr::var("ptr_valid", Sort::bool());
        let before = codegen.ctx.bmc_vc.constraints.len();
        codegen.assert_guarded(constraint);

        assert!(
            codegen.ctx.bmc_vc.constraints.len() > before,
            "assert_guarded should emit a constraint"
        );
        let emitted = codegen.ctx.bmc_vc.constraints.last().unwrap().to_string();
        assert!(emitted.contains("=>"), "guarded assert should use implication: {emitted}");
        assert!(
            emitted.contains("pc") && emitted.contains("ptr_valid"),
            "guarded assert should contain both pc and constraint: {emitted}"
        );
    });
}

/// record_violation_guarded without path condition emits bare violation.
#[test]
fn test_record_violation_guarded_unconditional() {
    with_test_ay_ctx_for_source(ENV_ASSERT_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "env_assert_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        codegen.current_path_condition = None;
        let violation = Expr::var("overflow", Sort::bool());
        let before = codegen.ctx.bmc_vc.violations.len();
        codegen.record_violation_guarded(violation, "overflow_check");

        assert!(
            codegen.ctx.bmc_vc.violations.len() > before,
            "record_violation_guarded should add a violation"
        );
        let last = codegen.ctx.bmc_vc.violations.last().unwrap();
        let rendered = last.condition.to_string();
        assert!(
            rendered.contains("overflow"),
            "unconditional violation should contain the condition: {rendered}"
        );
        assert!(
            !rendered.contains("and"),
            "unconditional violation should not use conjunction: {rendered}"
        );
    });
}

/// record_violation_guarded with path condition emits (pc AND violation).
#[test]
fn test_record_violation_guarded_with_path_condition() {
    with_test_ay_ctx_for_source(ENV_ASSERT_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "env_assert_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        codegen.current_path_condition = Some(Expr::var("reachable", Sort::bool()));
        let violation = Expr::var("div_zero", Sort::bool());
        let before = codegen.ctx.bmc_vc.violations.len();
        codegen.record_violation_guarded(violation, "div_by_zero_check");

        assert!(
            codegen.ctx.bmc_vc.violations.len() > before,
            "record_violation_guarded should add a violation"
        );
        let last = codegen.ctx.bmc_vc.violations.last().unwrap();
        let rendered = last.condition.to_string();
        assert!(rendered.contains("and"), "guarded violation should be conjunction: {rendered}");
        assert!(
            rendered.contains("reachable") && rendered.contains("div_zero"),
            "guarded violation should contain both pc and violation: {rendered}"
        );
    });
}

/// bind_ssa_result declares a variable and updates the environment.
#[test]
fn test_bind_ssa_result_declares_and_updates_env() {
    with_test_ay_ctx_for_source(ENV_ASSERT_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "env_assert_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Use the return place (_0) as destination
        let dest_place = Place { local: 0usize, projection: vec![] };
        let result = Expr::bitvec_const(42u128, 32);
        let constraints_before = codegen.ctx.bmc_vc.constraints.len();

        codegen.bind_ssa_result(&dest_place, result);

        assert!(
            codegen.ctx.bmc_vc.constraints.len() > constraints_before,
            "bind_ssa_result should emit at least one constraint (SSA def)"
        );
        let has_env_entry = codegen.current_env.values().any(|v| v.sort().is_bitvec());
        assert!(
            has_env_entry,
            "bind_ssa_result should update current_env with the declared variable"
        );
    });
}

// =============================================================================
// Tests for #2533: assert_ssa_def sort mismatch uses symbolic fallback
// =============================================================================

/// Regression for #2533: sort mismatch in assert_ssa_def must still emit a constraint.
///
/// Before the fix, sort coercion failure caused an early `return;`, leaving the
/// lhs variable completely unconstrained. Now it falls through with a symbolic
/// fallback of the correct sort.
#[test]
fn test_assert_ssa_def_sort_mismatch_emits_constraint() {
    with_test_ay_ctx_for_source(ENV_ASSERT_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "env_assert_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let base_name = "env_assert_probe::sort_mismatch_1";
        // No path condition — unconditional path.
        codegen.current_path_condition = None;

        // lhs is Int, rhs is Bool — convert_expr_to_sort now handles Bool→Int
        // via `ite(rhs, 1, 0)` (#3266), so the conversion succeeds.
        let lhs_expr = codegen.ctx.declare_var("mismatch_lhs", Sort::int());
        let rhs_expr = Expr::var("mismatch_rhs", Sort::bool());

        let before = codegen.ctx.bmc_vc.constraints.len();
        codegen.assert_ssa_def(lhs_expr, rhs_expr, &base_name);

        assert!(
            codegen.ctx.bmc_vc.constraints.len() > before,
            "assert_ssa_def with sort mismatch should still emit a constraint (#2533)"
        );

        // Part of #3266: Bool→Int conversion now succeeds. The constraint
        // binds lhs directly to the converted rhs (ite over the Bool value),
        // not to a symbolic fallback.
        let emitted = codegen.ctx.bmc_vc.constraints.last().unwrap().to_string();
        assert!(
            emitted.contains("mismatch_lhs"),
            "constraint should reference lhs variable: {emitted}"
        );
        assert!(
            emitted.contains("mismatch_rhs"),
            "constraint should contain converted Bool rhs: {emitted}"
        );
    });
}

/// Regression for #2533: sort mismatch with path condition uses ITE with symbolic fallback.
#[test]
fn test_assert_ssa_def_sort_mismatch_with_pc_uses_ite_fallback() {
    with_test_ay_ctx_for_source(ENV_ASSERT_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "env_assert_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let base_name = "env_assert_probe::sort_mismatch_2";
        codegen.current_path_condition = Some(Expr::var("pc", Sort::bool()));

        // lhs is Int, rhs is Bool — triggers sort mismatch fallback.
        let lhs_expr = codegen.ctx.declare_var("mismatch_pc_lhs", Sort::int());
        let rhs_expr = Expr::var("mismatch_pc_rhs", Sort::bool());

        let before = codegen.ctx.bmc_vc.constraints.len();
        codegen.assert_ssa_def(lhs_expr, rhs_expr, &base_name);

        assert!(
            codegen.ctx.bmc_vc.constraints.len() > before,
            "assert_ssa_def with sort mismatch + PC should still emit a constraint (#2533)"
        );

        let emitted = codegen.ctx.bmc_vc.constraints.last().unwrap().to_string();
        assert!(
            emitted.contains("ite"),
            "sort mismatch with path condition should use ITE: {emitted}"
        );
        assert!(
            emitted.contains("__ssa_init_"),
            "sort mismatch should use symbolic init fallback in ITE: {emitted}"
        );
        assert!(emitted.contains("pc"), "ITE should reference path condition: {emitted}");
    });
}

/// update_block_path_condition sets condition for first edge, ORs for second.
#[test]
fn test_update_block_path_condition_merge() {
    with_test_ay_ctx_for_source(ENV_ASSERT_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "env_assert_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let target_bb = 5usize;

        // First edge: sets condition directly
        codegen.current_path_condition = Some(Expr::var("branch_a", Sort::bool()));
        codegen.update_block_path_condition(target_bb, Some(Expr::var("cond_a", Sort::bool())));

        // Second edge: should OR with existing
        codegen.current_path_condition = Some(Expr::var("branch_b", Sort::bool()));
        codegen.update_block_path_condition(target_bb, Some(Expr::var("cond_b", Sort::bool())));

        // Set the path condition and verify
        codegen.set_block_path_condition(target_bb);
        assert!(
            codegen.current_path_condition.is_some(),
            "path condition should be set after set_block_path_condition"
        );
        let pc = codegen.current_path_condition.unwrap().to_string();
        assert!(
            pc.contains("or"),
            "multiple paths to same block should produce OR'd condition: {pc}"
        );
    });
}

// =============================================================================
// Tests for else_expr sort mismatch fallback in assert_ssa_def (lines 117-127)
// =============================================================================

/// Previous env value has incompatible sort (Bool) with rhs (Int): convert_expr_to_sort
/// now handles Bool→Int via `ite(expr, 1, 0)`, so the previous value is correctly
/// converted and used as the else_expr in the ITE-guarded definition.
///
/// Part of #3266: Bool→Int conversion was added to convert_expr_to_sort.
#[test]
fn test_assert_ssa_def_prev_env_sort_mismatch_uses_symbolic_fallback() {
    with_test_ay_ctx_for_source(ENV_ASSERT_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "env_assert_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let base_name = "env_assert_probe::prev_sort_mismatch";
        codegen.current_path_condition = Some(Expr::var("pc", Sort::bool()));

        // Seed the env with a Bool-sorted value.
        let prev_bool = Expr::var("prev_flag", Sort::bool());
        codegen.env_update(base_name, prev_bool);

        // Now define an Int-sorted SSA variable. The else_expr resolution at
        // mod.rs:115-134 will find the Bool prev value and successfully convert
        // it to Int via `ite(prev_flag, 1, 0)` (#3266).
        let lhs_expr = codegen.ctx.declare_var("int_next", Sort::int());
        let rhs_expr = Expr::var("int_rhs", Sort::int());

        let before = codegen.ctx.bmc_vc.constraints.len();
        codegen.assert_ssa_def(lhs_expr, rhs_expr, &base_name);

        assert!(
            codegen.ctx.bmc_vc.constraints.len() > before,
            "assert_ssa_def should emit a constraint even when prev env sort mismatches"
        );

        let emitted = codegen.ctx.bmc_vc.constraints.last().unwrap().to_string();
        assert!(emitted.contains("ite"), "should produce ITE-guarded definition: {emitted}");
        assert!(emitted.contains("pc"), "ITE should reference path condition: {emitted}");
        // Part of #3266: Bool→Int conversion now succeeds, so the previous Bool
        // value is converted and used in the else branch (not a symbolic fallback).
        assert!(
            emitted.contains("prev_flag"),
            "else branch should use converted prev Bool value, not symbolic fallback: {emitted}"
        );
    });
}

/// No path condition + matching sorts: unconditional equality assertion.
///
/// Covers the happy path at env/mod.rs:109-111 where `current_path_condition`
/// is None and sorts already match, producing a direct `lhs = rhs` constraint.
#[test]
fn test_assert_ssa_def_no_pc_matching_sorts_unconditional_equality() {
    with_test_ay_ctx_for_source(ENV_ASSERT_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "env_assert_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let base_name = "env_assert_probe::unconditional_1";
        codegen.current_path_condition = None;

        let lhs_expr = codegen.ctx.declare_var("uc_lhs", Sort::bitvec(32));
        let rhs_expr = Expr::bitvec_const(42u128, 32);

        let before = codegen.ctx.bmc_vc.constraints.len();
        codegen.assert_ssa_def(lhs_expr, rhs_expr, &base_name);

        assert!(
            codegen.ctx.bmc_vc.constraints.len() > before,
            "unconditional assert_ssa_def should emit a constraint"
        );

        let emitted = codegen.ctx.bmc_vc.constraints.last().unwrap().to_string();
        // No path condition → direct equality, no ITE
        assert!(
            !emitted.contains("ite"),
            "unconditional SSA def should be direct equality, not ITE: {emitted}"
        );
        assert!(emitted.contains("uc_lhs"), "constraint should reference lhs variable: {emitted}");
    });
}

// =============================================================================
// Tests for sort_harmonize.rs — harmonize_incoming_sorts (#2933)
// =============================================================================

/// harmonize_incoming_sorts with all-Int values returns Int target unchanged.
#[test]
fn test_harmonize_incoming_sorts_all_int_returns_int_unchanged() {
    let cond_a = Some(Expr::var("cond_a", Sort::bool()));
    let val_a = Expr::var("a", Sort::int());
    let cond_b = Some(Expr::var("cond_b", Sort::bool()));
    let val_b = Expr::var("b", Sort::int());

    let incoming = vec![(cond_a, val_a), (cond_b, val_b)];
    let (target_sort, harmonized) = StatementCodegen::harmonize_incoming_sorts(incoming, None);

    assert!(target_sort.is_int(), "all-Int input should produce Int target");
    assert_eq!(harmonized.len(), 2);
    // Values should be unchanged since sorts already match
    assert!(harmonized[0].1.sort().is_int());
    assert!(harmonized[1].1.sort().is_int());
}

/// harmonize_incoming_sorts with mixed Int + BV targets Int and converts BV values.
#[test]
fn test_harmonize_incoming_sorts_mixed_int_bitvec_targets_int() {
    let cond_a = Some(Expr::var("cond_a", Sort::bool()));
    let val_int = Expr::var("a_int", Sort::int());
    let cond_b = Some(Expr::var("cond_b", Sort::bool()));
    let val_bv = Expr::bitvec_const(42u64, 32);

    let incoming = vec![(cond_a, val_int), (cond_b, val_bv)];
    let (target_sort, harmonized) = StatementCodegen::harmonize_incoming_sorts(incoming, None);

    assert!(target_sort.is_int(), "mixed Int+BV should target Int to preserve precision");
    assert_eq!(harmonized.len(), 2);
    // First value (Int) should be unchanged
    assert!(harmonized[0].1.sort().is_int());
    // Second value (BV) should be converted to Int
    assert!(
        harmonized[1].1.sort().is_int(),
        "BV value should be converted to Int, got {:?}",
        harmonized[1].1.sort()
    );
}

/// harmonize_incoming_sorts with all-BV same width returns BV target unchanged.
#[test]
fn test_harmonize_incoming_sorts_all_bitvec_same_width_no_conversion() {
    let cond_a = Some(Expr::var("cond_a", Sort::bool()));
    let val_a = Expr::bitvec_const(1u64, 32);
    let cond_b = Some(Expr::var("cond_b", Sort::bool()));
    let val_b = Expr::bitvec_const(2u64, 32);

    let incoming = vec![(cond_a, val_a), (cond_b, val_b)];
    let (target_sort, harmonized) = StatementCodegen::harmonize_incoming_sorts(incoming, None);

    assert!(target_sort.is_bitvec(), "all-BV(32) input should produce BV target");
    assert_eq!(target_sort.bitvec_width(), Some(32));
    assert_eq!(harmonized.len(), 2);
    assert_eq!(harmonized[0].1.sort().bitvec_width(), Some(32));
    assert_eq!(harmonized[1].1.sort().bitvec_width(), Some(32));
}

/// harmonize_incoming_sorts with BigInt datatype + BV targets Int.
#[test]
fn test_harmonize_incoming_sorts_bigint_datatype_plus_bitvec_targets_int() {
    let bigint_sort = struct_sort("num_bigint::BigInt", [("value", Sort::int())]);
    let cond_a = Some(Expr::var("cond_a", Sort::bool()));
    let val_bigint = Expr::var("big", bigint_sort);
    let cond_b = Some(Expr::var("cond_b", Sort::bool()));
    let val_bv = Expr::bitvec_const(99u64, 64);

    let incoming = vec![(cond_a, val_bigint), (cond_b, val_bv)];
    let (target_sort, harmonized) = StatementCodegen::harmonize_incoming_sorts(incoming, None);

    assert!(
        target_sort.is_int(),
        "BigInt datatype + BV should target Int to preserve arbitrary precision"
    );
    assert_eq!(harmonized.len(), 2);
    // Both should be converted to Int
    assert!(harmonized[0].1.sort().is_int());
    assert!(harmonized[1].1.sort().is_int());
}

/// harmonize_incoming_sorts with single value returns its sort unchanged.
#[test]
fn test_harmonize_incoming_sorts_single_value_passthrough() {
    let cond = Some(Expr::var("cond", Sort::bool()));
    let val = Expr::bitvec_const(7u64, 16);

    let incoming = vec![(cond, val)];
    let (target_sort, harmonized) = StatementCodegen::harmonize_incoming_sorts(incoming, None);

    assert!(target_sort.is_bitvec());
    assert_eq!(target_sort.bitvec_width(), Some(16));
    assert_eq!(harmonized.len(), 1);
    assert_eq!(harmonized[0].1.sort().bitvec_width(), Some(16));
}

// =============================================================================
// Tests for convert_expr_to_sort Bool↔BV paths (sort_harmonize.rs #2933)
// =============================================================================

/// Bool → BitVec: true maps to BV(1), false to BV(0).
#[test]
fn test_convert_bool_to_bitvec() {
    let bool_expr = Expr::var("flag", Sort::bool());
    let converted = StatementCodegen::convert_expr_to_sort(bool_expr, &Sort::bitvec(8), None);

    assert_eq!(converted.sort().bitvec_width(), Some(8));
    assert!(
        matches!(converted.value(), ExprValue::Ite { .. }),
        "Bool→BV should produce ITE(flag, 1, 0), got {:?}",
        converted.value()
    );
}

/// BV → Bool: non-zero maps to true.
/// `ne` is implemented as `eq(other).not()`, so result is `Not(Eq(status, 0))`.
#[test]
fn test_convert_bitvec_to_bool() {
    let bv_expr = Expr::var("status", Sort::bitvec(8));
    let converted = StatementCodegen::convert_expr_to_sort(bv_expr, &Sort::bool(), None);

    assert!(converted.sort().is_bool());
    // ne(other) = eq(other).not() → Not(Eq(status, bv_const(0, 8)))
    assert!(
        matches!(converted.value(), ExprValue::Not(inner) if matches!(inner.value(), ExprValue::Eq(..))),
        "BV→Bool should produce Not(Eq(status, 0)), got {:?}",
        converted.value()
    );
}
