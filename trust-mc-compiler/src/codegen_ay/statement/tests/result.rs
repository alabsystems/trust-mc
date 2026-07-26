// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! MIR-driven tests for result.rs — Result<T, E> codegen methods.
//!
//! 35 trivial AY-only expression tests deleted per rule #2312 and #2482
//! (tested AY datatype_constructor/is_constructor/field_select/ITE/discriminant
//! patterns, not production codegen).
//! Remaining tests use with_test_ay_ctx_for_source to exercise codegen_result_*
//! methods, plus solver-backed proofs for Result discriminant semantics.
//!
//! Part of #2016.

use super::*;

const RESULT_PRODUCTION_CODEGEN_PROBE: &str = r#"
pub fn result_predicate_probe(_x: &Result<i32, i32>) -> bool {
    true
}

pub fn result_unwrap_or_probe(_x: Result<i32, i32>, _default: i32) -> i32 {
    0
}
"#;

const RESULT_TEST_SMT_VAR_PREFIX: &str = "ay_violation_result_test";

fn return_place() -> Place {
    local_place(0)
}

fn assert_result_unsat_for_violation(
    ctx: &crate::codegen_ay::context::AYCtx<'_, 'static>,
    violation_expr: Expr,
    proof_name: &str,
) {
    super::assert_unsat_for_violation(ctx, violation_expr, RESULT_TEST_SMT_VAR_PREFIX, proof_name);
}

// =============================================================================
// Direct production-method tests — codegen_result_is_ok / is_err / unwrap_or
// =============================================================================

#[test]
fn test_codegen_result_is_ok_flattened_assigns_eq_predicate() {
    with_test_ay_ctx_for_source(RESULT_PRODUCTION_CODEGEN_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "result_predicate_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let result_base =
            codegen.get_result_base_from_ref(&local_operand(1)).expect("tracked Result reference");
        let discrim = codegen.ctx.declare_var("result_is_ok_discrim", Sort::bitvec(8));
        codegen.env_update(format!("{result_base}.0"), discrim);

        let dest = return_place();
        let target = Some(17);
        let before = codegen.ctx.program.commands().len();
        let returned = codegen.codegen_result_is_ok(&[local_operand(1)], &dest, target);

        assert_eq!(returned, target);
        assert!(codegen.ctx.program.commands().len() > before);

        let dest_base = codegen.ssa_base_name(&dest);
        let dest_expr =
            codegen.current_env.get(dest_base.as_str()).expect("destination should be assigned");
        assert!(dest_expr.sort().is_bool());

        let added = &codegen.ctx.program.commands()[before..];
        let rhs = extract_ssa_rhs(added, dest_expr).expect("missing SSA rhs for is_ok");
        assert!(
            matches!(rhs.value(), ExprValue::Eq(..)),
            "is_ok should encode discriminant == 0, got {:?}",
            rhs.value()
        );
    });
}

#[test]
fn test_codegen_result_is_err_flattened_assigns_negated_eq_predicate() {
    with_test_ay_ctx_for_source(RESULT_PRODUCTION_CODEGEN_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "result_predicate_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let result_base =
            codegen.get_result_base_from_ref(&local_operand(1)).expect("tracked Result reference");
        let discrim = codegen.ctx.declare_var("result_is_err_discrim", Sort::bitvec(8));
        codegen.env_update(format!("{result_base}.0"), discrim);

        let dest = return_place();
        let target = Some(19);
        let before = codegen.ctx.program.commands().len();
        let returned = codegen.codegen_result_is_err(&[local_operand(1)], &dest, target);

        assert_eq!(returned, target);
        assert!(codegen.ctx.program.commands().len() > before);

        let dest_base = codegen.ssa_base_name(&dest);
        let dest_expr =
            codegen.current_env.get(dest_base.as_str()).expect("destination should be assigned");
        assert!(dest_expr.sort().is_bool());

        let added = &codegen.ctx.program.commands()[before..];
        let rhs = extract_ssa_rhs(added, dest_expr).expect("missing SSA rhs for is_err");
        match rhs.value() {
            ExprValue::Not(inner) => {
                assert!(
                    matches!(inner.value(), ExprValue::Eq(..)),
                    "is_err should encode not(discriminant == 0), got {:?}",
                    inner.value()
                );
            }
            other => panic!("is_err should be Not(Eq(..)), got {other:?}"),
        }
    });
}

#[test]
fn test_codegen_result_unwrap_or_flattened_assigns_ite() {
    with_test_ay_ctx_for_source(RESULT_PRODUCTION_CODEGEN_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "result_unwrap_or_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let result_base = codegen.ssa_base_name(&local_place(1));
        codegen.env_update(format!("{result_base}.0"), Expr::bitvec_const(0u128, 8));
        codegen.env_update(format!("{result_base}.1"), Expr::bitvec_const(42u128, 32));

        let default_base = codegen.ssa_base_name(&local_place(2));
        codegen.env_update(default_base, Expr::bitvec_const(7u128, 32));

        let dest = return_place();
        let target = Some(23);
        let before = codegen.ctx.program.commands().len();
        let returned =
            codegen.codegen_result_unwrap_or(&[local_operand(1), local_operand(2)], &dest, target);

        assert_eq!(returned, target);
        assert!(codegen.ctx.program.commands().len() > before);

        let dest_base = codegen.ssa_base_name(&dest);
        let dest_expr =
            codegen.current_env.get(dest_base.as_str()).expect("destination should be assigned");
        assert_eq!(dest_expr.sort().bitvec_width(), Some(32));

        let added = &codegen.ctx.program.commands()[before..];
        let rhs = extract_ssa_rhs(added, dest_expr).expect("missing SSA rhs for unwrap_or");
        match rhs.value() {
            ExprValue::Ite { cond, then_expr, else_expr } => {
                assert!(
                    matches!(cond.value(), ExprValue::Eq(..)),
                    "unwrap_or ITE condition should check discriminant == 0, got {:?}",
                    cond.value()
                );
                assert_eq!(then_expr.sort().bitvec_width(), Some(32));
                assert_eq!(else_expr.sort().bitvec_width(), Some(32));
            }
            other => panic!("unwrap_or should encode ITE, got {other:?}"),
        }
    });
}

#[test]
fn test_codegen_result_is_ok_solver_proves_zero_discriminant_true() {
    with_test_ay_ctx_for_source(RESULT_PRODUCTION_CODEGEN_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "result_predicate_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let result_base =
            codegen.get_result_base_from_ref(&local_operand(1)).expect("tracked Result reference");
        let discrim = codegen.ctx.declare_var("result_solver_discrim", Sort::bitvec(8));
        codegen.env_update(format!("{result_base}.0"), discrim.clone());

        let dest = return_place();
        let returned = codegen.codegen_result_is_ok(&[local_operand(1)], &dest, Some(29));
        assert_eq!(returned, Some(29));

        let dest_base = codegen.ssa_base_name(&dest);
        let dest_expr = codegen
            .current_env
            .get(dest_base.as_str())
            .expect("destination should be assigned")
            .clone();
        assert!(dest_expr.sort().is_bool());

        // Prove: discrim==0 implies is_ok=true.
        // We check UNSAT for (discrim==0) AND (is_ok != true).
        let violation = discrim.eq(Expr::bitvec_const(0u128, 8)).and(dest_expr.not());
        assert_result_unsat_for_violation(codegen.ctx, violation, "is_ok_zero_discriminant");
    });
}

// =============================================================================
// Direct production-method tests for remaining codegen_result_* methods
// Part of #2248: Close semantic coverage gaps
// =============================================================================

#[test]
fn test_codegen_result_unwrap_flattened_assigns_payload() {
    with_test_ay_ctx_for_source(RESULT_PRODUCTION_CODEGEN_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "result_unwrap_or_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Set up flattened Result: .0 = discriminant (Ok), .1 = payload
        let result_base = codegen.ssa_base_name(&local_place(1));
        codegen.env_update(format!("{result_base}.0"), Expr::bitvec_const(0u128, 8));
        codegen.env_update(format!("{result_base}.1"), Expr::bitvec_const(42u128, 32));

        let dest = return_place();
        let target = Some(31);
        let before = codegen.ctx.program.commands().len();
        let returned = codegen.codegen_result_unwrap(&[local_operand(1)], &dest, target);

        assert_eq!(returned, target);
        assert!(codegen.ctx.program.commands().len() > before);

        let dest_base = codegen.ssa_base_name(&dest);
        let dest_expr =
            codegen.current_env.get(dest_base.as_str()).expect("destination should be assigned");
        assert_eq!(dest_expr.sort().bitvec_width(), Some(32));

        // unwrap extracts the payload directly (no ITE — assumes caller checked is_ok)
        let added = &codegen.ctx.program.commands()[before..];
        let rhs = extract_ssa_rhs(added, dest_expr).expect("missing SSA rhs for unwrap");
        assert_eq!(rhs.sort().bitvec_width(), Some(32), "unwrap should extract bv32 payload");
        // Verify the extracted value is the exact constant we stored in .1
        let payload = Expr::bitvec_const(42u128, 32);
        assert_eq!(rhs, payload, "unwrap should extract the .1 field value (42)");
    });
}

#[test]
fn test_codegen_result_unwrap_or_else_flattened_assigns_ite_with_symbolic_else() {
    with_test_ay_ctx_for_source(RESULT_PRODUCTION_CODEGEN_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "result_unwrap_or_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Set up flattened Result with symbolic discriminant
        let result_base = codegen.ssa_base_name(&local_place(1));
        let discrim = codegen.ctx.declare_var("unwrap_or_else_discrim", Sort::bitvec(8));
        codegen.env_update(format!("{result_base}.0"), discrim);
        codegen.env_update(format!("{result_base}.1"), Expr::bitvec_const(42u128, 32));

        let dest = return_place();
        let target = Some(33);
        let before = codegen.ctx.program.commands().len();
        let returned = codegen.codegen_result_unwrap_or_else(
            &[local_operand(1), local_operand(2)],
            &dest,
            target,
        );

        assert_eq!(returned, target);
        assert!(codegen.ctx.program.commands().len() > before);

        let dest_base = codegen.ssa_base_name(&dest);
        let dest_expr =
            codegen.current_env.get(dest_base.as_str()).expect("destination should be assigned");
        assert_eq!(dest_expr.sort().bitvec_width(), Some(32));

        // unwrap_or_else produces ITE(is_ok, ok_value, symbolic_closure_result)
        let added = &codegen.ctx.program.commands()[before..];
        let rhs = extract_ssa_rhs(added, dest_expr).expect("missing SSA rhs for unwrap_or_else");
        match rhs.value() {
            ExprValue::Ite { cond, then_expr, else_expr } => {
                assert!(
                    matches!(cond.value(), ExprValue::Eq(..)),
                    "unwrap_or_else ITE condition should check discriminant == 0, got {:?}",
                    cond.value()
                );
                assert_eq!(then_expr.sort().bitvec_width(), Some(32));
                assert_eq!(else_expr.sort().bitvec_width(), Some(32));
            }
            other => panic!("unwrap_or_else should encode ITE, got {other:?}"),
        }
    });
}

#[test]
fn test_codegen_result_map_assigns_symbolic_result() {
    with_test_ay_ctx_for_source(RESULT_PRODUCTION_CODEGEN_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "result_unwrap_or_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = return_place();
        let target = Some(35);
        let returned = codegen.codegen_result_map(&[local_operand(1)], &dest, target);

        assert_eq!(returned, target);

        let dest_base = codegen.ssa_base_name(&dest);
        let dest_expr = codegen
            .current_env
            .get(dest_base.as_str())
            .expect("map should assign symbolic destination");
        // Destination sort matches probe return type (i32 -> bv32)
        assert_eq!(dest_expr.sort().bitvec_width(), Some(32));
    });
}

#[test]
fn test_codegen_result_and_then_assigns_symbolic_result() {
    with_test_ay_ctx_for_source(RESULT_PRODUCTION_CODEGEN_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "result_unwrap_or_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = return_place();
        let target = Some(37);
        let returned = codegen.codegen_result_and_then(&[local_operand(1)], &dest, target);

        assert_eq!(returned, target);

        let dest_base = codegen.ssa_base_name(&dest);
        let dest_expr = codegen
            .current_env
            .get(dest_base.as_str())
            .expect("and_then should assign symbolic destination");
        assert_eq!(dest_expr.sort().bitvec_width(), Some(32));
    });
}

#[test]
fn test_codegen_result_map_err_assigns_symbolic_result() {
    with_test_ay_ctx_for_source(RESULT_PRODUCTION_CODEGEN_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "result_unwrap_or_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = return_place();
        let target = Some(39);
        let returned = codegen.codegen_result_map_err(&[local_operand(1)], &dest, target);

        assert_eq!(returned, target);

        let dest_base = codegen.ssa_base_name(&dest);
        let dest_expr = codegen
            .current_env
            .get(dest_base.as_str())
            .expect("map_err should assign symbolic destination");
        assert_eq!(dest_expr.sort().bitvec_width(), Some(32));
    });
}

#[test]
fn test_codegen_result_ok_assigns_symbolic_result() {
    with_test_ay_ctx_for_source(RESULT_PRODUCTION_CODEGEN_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "result_unwrap_or_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = return_place();
        let target = Some(41);
        let returned = codegen.codegen_result_ok(&[local_operand(1)], &dest, target);

        assert_eq!(returned, target);

        let dest_base = codegen.ssa_base_name(&dest);
        let dest_expr = codegen
            .current_env
            .get(dest_base.as_str())
            .expect("ok should assign symbolic destination");
        assert_eq!(dest_expr.sort().bitvec_width(), Some(32));
    });
}

#[test]
fn test_codegen_result_err_assigns_symbolic_result() {
    with_test_ay_ctx_for_source(RESULT_PRODUCTION_CODEGEN_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "result_unwrap_or_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = return_place();
        let target = Some(43);
        let returned = codegen.codegen_result_err(&[local_operand(1)], &dest, target);

        assert_eq!(returned, target);

        let dest_base = codegen.ssa_base_name(&dest);
        let dest_expr = codegen
            .current_env
            .get(dest_base.as_str())
            .expect("err should assign symbolic destination");
        assert_eq!(dest_expr.sort().bitvec_width(), Some(32));
    });
}

// =============================================================================
// Empty-args guard tests for Result methods
// Part of #2248: Verify all methods return None on empty args
// =============================================================================

#[test]
fn test_codegen_result_methods_return_none_on_empty_args() {
    with_test_ay_ctx_for_source(RESULT_PRODUCTION_CODEGEN_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "result_unwrap_or_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // All methods with args.is_empty() guard
        assert_eq!(codegen.codegen_result_is_ok(&[], &return_place(), Some(1)), None);
        assert_eq!(codegen.codegen_result_is_err(&[], &return_place(), Some(1)), None);
        assert_eq!(codegen.codegen_result_unwrap(&[], &return_place(), Some(1)), None);
        assert_eq!(codegen.codegen_result_unwrap_or_else(&[], &return_place(), Some(1)), None);
        assert_eq!(codegen.codegen_result_map(&[], &return_place(), Some(1)), None);
        assert_eq!(codegen.codegen_result_and_then(&[], &return_place(), Some(1)), None);
        assert_eq!(codegen.codegen_result_map_err(&[], &return_place(), Some(1)), None);
        assert_eq!(codegen.codegen_result_ok(&[], &return_place(), Some(1)), None);
        assert_eq!(codegen.codegen_result_err(&[], &return_place(), Some(1)), None);
        // unwrap_or has args.len() < 2 guard — empty args returns None
        assert_eq!(codegen.codegen_result_unwrap_or(&[], &return_place(), Some(1)), None);
    });
}

// =============================================================================
// Polarity regression tests — discriminant inversion detection
// Part of #2248: Ensure Ok=0/Err!=0 convention cannot silently flip
// =============================================================================

#[test]
fn test_codegen_result_is_ok_solver_proves_nonzero_discriminant_false() {
    with_test_ay_ctx_for_source(RESULT_PRODUCTION_CODEGEN_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "result_predicate_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let result_base =
            codegen.get_result_base_from_ref(&local_operand(1)).expect("tracked Result reference");
        let discrim = codegen.ctx.declare_var("result_polarity_discrim", Sort::bitvec(8));
        codegen.env_update(format!("{result_base}.0"), discrim.clone());

        let dest = return_place();
        codegen.codegen_result_is_ok(&[local_operand(1)], &dest, Some(45));

        let dest_base = codegen.ssa_base_name(&dest);
        let dest_expr = codegen
            .current_env
            .get(dest_base.as_str())
            .expect("destination should be assigned")
            .clone();

        // Prove: discrim != 0 implies is_ok = false.
        // UNSAT for (discrim != 0) AND (is_ok = true).
        let violation = discrim.eq(Expr::bitvec_const(0u128, 8)).not().and(dest_expr);
        assert_result_unsat_for_violation(
            codegen.ctx,
            violation,
            "is_ok_nonzero_discriminant_false",
        );
    });
}

#[test]
fn test_codegen_result_is_err_equals_not_is_ok_same_discriminant() {
    with_test_ay_ctx_for_source(RESULT_PRODUCTION_CODEGEN_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "result_predicate_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let result_base =
            codegen.get_result_base_from_ref(&local_operand(1)).expect("tracked Result reference");
        let discrim = codegen.ctx.declare_var("result_dual_discrim", Sort::bitvec(8));
        codegen.env_update(format!("{result_base}.0"), discrim);

        // Compute is_ok into local 0 (return place)
        let ok_dest = return_place();
        codegen.codegen_result_is_ok(&[local_operand(1)], &ok_dest, Some(47));
        let ok_base = codegen.ssa_base_name(&ok_dest);
        let is_ok_expr =
            codegen.current_env.get(ok_base.as_str()).expect("is_ok destination").clone();

        // Compute is_err into a separate destination (use local 2 via default_arg slot)
        // Since is_err needs the same ref, and the discriminant is still in env, we
        // use local_place(2) as the destination for is_err.
        let err_dest = local_place(2);
        codegen.codegen_result_is_err(&[local_operand(1)], &err_dest, Some(49));
        let err_base = codegen.ssa_base_name(&err_dest);
        let is_err_expr =
            codegen.current_env.get(err_base.as_str()).expect("is_err destination").clone();

        // Prove: is_err == !is_ok (they are complementary).
        // UNSAT for is_err XOR (NOT is_ok), i.e., is_err != !is_ok.
        // Encode as: (is_err AND is_ok) OR (!is_err AND !is_ok) — both true
        // simultaneously or both false simultaneously means they're NOT complementary.
        let violation =
            is_err_expr.clone().and(is_ok_expr.clone()).or(is_err_expr.not().and(is_ok_expr.not()));
        assert_result_unsat_for_violation(codegen.ctx, violation, "is_err_equals_not_is_ok");
    });
}

// =============================================================================
// MIR-driven dispatch tests for Option/Result higher-order stubs (Part of #2016)
// =============================================================================

/// Probe source: Option::and_then exercising codegen_option_and_then.
const OPTION_AND_THEN_PROBE: &str = r#"
pub fn option_and_then_probe(x: Option<i32>) -> Option<i64> {
    x.and_then(|v| Some(v as i64))
}
"#;

/// Test Option::and_then dispatches through stub pipeline.
#[test]
fn test_mir_option_and_then_dispatch() {
    with_test_ay_ctx_for_source(OPTION_AND_THEN_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "option_and_then_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let mut call_count = 0;
        for bb in &body.blocks {
            for stmt in &bb.statements {
                codegen.codegen_statement(stmt);
            }
            if matches!(bb.terminator.kind, rustc_public::mir::TerminatorKind::Call { .. }) {
                call_count += 1;
            }
            let _successors = codegen.codegen_terminator_with_successors(&bb.terminator);
        }
        // and_then generates at least 1 Call terminator
        assert!(call_count >= 1, "Option::and_then should have Call, got {call_count}");
    });
}

/// Probe source: Result::map exercising codegen_result_map.
const RESULT_MAP_PROBE: &str = r#"
pub fn result_map_probe(x: Result<i32, i32>) -> Result<i64, i32> {
    x.map(|v| v as i64)
}
"#;

/// Test Result::map dispatches through stub pipeline.
#[test]
fn test_mir_result_map_dispatch() {
    with_test_ay_ctx_for_source(RESULT_MAP_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "result_map_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let mut call_count = 0;
        for bb in &body.blocks {
            for stmt in &bb.statements {
                codegen.codegen_statement(stmt);
            }
            if matches!(bb.terminator.kind, rustc_public::mir::TerminatorKind::Call { .. }) {
                call_count += 1;
            }
            let _successors = codegen.codegen_terminator_with_successors(&bb.terminator);
        }
        // Result::map generates at least 1 Call terminator
        assert!(call_count >= 1, "Result::map should have Call, got {call_count}");
    });
}

/// Probe source: Option::ok_or_else exercising codegen_option_ok_or_else.
const OPTION_OK_OR_ELSE_PROBE: &str = r#"
pub fn option_ok_or_else_probe(x: Option<i32>) -> Result<i32, i32> {
    x.ok_or_else(|| -1)
}
"#;

/// Test Option::ok_or_else dispatches through stub pipeline.
#[test]
fn test_mir_option_ok_or_else_dispatch() {
    with_test_ay_ctx_for_source(OPTION_OK_OR_ELSE_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "option_ok_or_else_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let mut call_count = 0;
        for bb in &body.blocks {
            for stmt in &bb.statements {
                codegen.codegen_statement(stmt);
            }
            if matches!(bb.terminator.kind, rustc_public::mir::TerminatorKind::Call { .. }) {
                call_count += 1;
            }
            let _successors = codegen.codegen_terminator_with_successors(&bb.terminator);
        }
        assert!(call_count >= 1, "Option::ok_or_else should have Call, got {call_count}");
    });
}

/// Probe source: Result::unwrap_or_else exercising codegen_result_unwrap_or_else.
const RESULT_UNWRAP_OR_ELSE_PROBE: &str = r#"
pub fn result_unwrap_or_else_probe(x: Result<i32, i32>) -> i32 {
    x.unwrap_or_else(|e| e * 2)
}
"#;

/// Test Result::unwrap_or_else dispatches through stub pipeline.
#[test]
fn test_mir_result_unwrap_or_else_dispatch() {
    with_test_ay_ctx_for_source(RESULT_UNWRAP_OR_ELSE_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "result_unwrap_or_else_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let mut call_count = 0;
        for bb in &body.blocks {
            for stmt in &bb.statements {
                codegen.codegen_statement(stmt);
            }
            if matches!(bb.terminator.kind, rustc_public::mir::TerminatorKind::Call { .. }) {
                call_count += 1;
            }
            let _successors = codegen.codegen_terminator_with_successors(&bb.terminator);
        }
        assert!(call_count >= 1, "Result::unwrap_or_else should have Call, got {call_count}");
    });
}
