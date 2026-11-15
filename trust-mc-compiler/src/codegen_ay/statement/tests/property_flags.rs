// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Boolean definitions must retain both directions and named model identities.

use super::*;
use crate::codegen_ay::context::AYCtx;
use ay_bindings::{AYProgram, Constraint};

/// Match the statement controls' default executor and interrupt-only budget.
/// Keep all outputs so the SAT controls also check the property model flags.
fn solve(program: &AYProgram, expected: &str) -> Vec<String> {
    let smt = program.to_string();
    let commands = ay_frontend::parse(&smt).expect("well-formed BMC query");
    let mut executor = ay_dpll::Executor::new();
    let interrupt = Arc::new(AtomicBool::new(false));
    executor.set_interrupt(Arc::clone(&interrupt));
    let (cancel_tx, cancel_rx) = std::sync::mpsc::channel();
    let timer_interrupt = Arc::clone(&interrupt);
    let timer = std::thread::spawn(move || {
        if cancel_rx.recv_timeout(Duration::from_secs(AY_TEST_TIMEOUT_SECS)).is_err() {
            timer_interrupt.store(true, Ordering::Relaxed);
        }
    });
    let outputs = executor.execute_all(&commands);
    let _ = cancel_tx.send(());
    timer.join().expect("timer thread");
    assert!(!interrupt.load(Ordering::Relaxed), "default AY timeout:\n{smt}");
    let outputs = outputs.unwrap_or_else(|err| panic!("AY failed: {err}\n{smt}"));
    let verdict =
        outputs.iter().map(|s| s.trim()).find(|s| matches!(*s, "sat" | "unsat" | "unknown"));
    assert_eq!(verdict, Some(expected), "BMC query:\n{smt}\n{outputs:?}");
    outputs
}

fn finish(ctx: &mut AYCtx<'_, '_>, ir_emitter: bool, model: bool) -> AYProgram {
    if ir_emitter {
        let mut vc = ctx.bmc_vc.clone();
        vc.query.produce_model = model;
        emit_bmc(vc)
    } else {
        ctx.finalize_counterexample_query();
        ctx.program.check_sat();
        if model {
            ctx.add_get_value_for_violations();
        }
        ctx.program.clone()
    }
}

#[test]
fn property_flag_definition_retains_both_directions_without_a_goal() {
    for (datatype, unrelated) in [(false, false), (false, true), (true, false)] {
        for condition_value in [false, true] {
            for flag_value in [false, true] {
                let mut program = AYProgram::qf_bv();
                if unrelated {
                    program.set_logic("ALL");
                    let sort = Sort::simple_enum_type("Unrelated", ["Left", "Right"]);
                    let value =
                        program.declare_const("unrelated_Option_Layout_Result", sort.clone());
                    program.assert(value.eq(Expr::datatype_constructor(
                        "Unrelated",
                        "Left",
                        vec![],
                        sort,
                    )));
                }
                let flag = program.declare_const("property_flag", Sort::bool());
                let condition = if datatype {
                    program.set_logic("ALL");
                    let sort = Sort::simple_enum_type("Witness", ["Left", "Right"]);
                    let input = program.declare_const("property_input", sort.clone());
                    let constructor = if condition_value { "Left" } else { "Right" };
                    program.assert(input.clone().eq(Expr::datatype_constructor(
                        "Witness",
                        constructor,
                        vec![],
                        sort,
                    )));
                    input.is_constructor("Witness", "Left")
                } else {
                    let input = program.declare_const("property_input", Sort::bv8());
                    program
                        .assert(input.clone().eq(Expr::bitvec_const(u8::from(condition_value), 8)));
                    input.eq(Expr::bitvec_const(1u8, 8))
                };
                crate::codegen_ay::emitter::define_property_flag(
                    &mut program,
                    flag.clone(),
                    condition,
                );
                program.assert(flag.eq(Expr::bool_const(flag_value)));
                program.check_sat();
                solve(&program, if condition_value == flag_value { "sat" } else { "unsat" });
            }
        }
    }
}

#[test]
fn datatype_property_flags_keep_alternatives_and_models_on_both_bmc_routes() {
    for ir_emitter in [false, true] {
        for selected in 0..4 {
            with_test_ay_ctx_for_source("pub fn datatype_property_flags() {}", |mut ctx| {
                let variants = ["First", "Second", "Third", "Neither"];
                let sort = Sort::simple_enum_type("Choices", variants);
                let input = ctx.declare_var("property_input", sort.clone());
                ctx.assert(input.clone().eq(Expr::datatype_constructor(
                    "Choices",
                    variants[selected],
                    vec![],
                    sort,
                )));
                for variant in &variants[..3] {
                    ctx.record_property_violation_full(
                        input.clone().is_constructor("Choices", *variant),
                        "kani_assert",
                        None,
                        Some(format!("alternative {variant}")),
                    );
                }
                let original = ctx.bmc_vc.clone();
                let names: Vec<_> = original
                    .violations
                    .iter()
                    .map(|v| v.smt_var.clone().expect("recorded identity"))
                    .collect();
                let program = finish(&mut ctx, ir_emitter, selected < 3);
                assert_eq!(ctx.bmc_vc.violations, original.violations);
                assert_eq!(ctx.bmc_vc.constraints, original.constraints);
                let outputs = solve(&program, if selected < 3 { "sat" } else { "unsat" });
                if selected < 3 {
                    let model = outputs.last().expect("named model values");
                    for (index, name) in names.iter().enumerate() {
                        assert!(
                            model.contains(&format!("({name} {})", index == selected)),
                            "route={ir_emitter}, selected={selected}: {model}"
                        );
                    }
                }
            });
        }
        with_test_ay_ctx_for_source("pub fn infeasible_datatype_property() {}", |mut ctx| {
            let sort = Sort::simple_enum_type("Witness", ["Left", "Right"]);
            let input = ctx.declare_var("property_input", sort);
            ctx.assert(Expr::bool_const(false));
            ctx.record_property_violation(input.is_constructor("Witness", "Left"), "kani_assert");
            solve(&finish(&mut ctx, ir_emitter, false), "unsat");
        });
    }
}

/// Inspect only the new definition's typed assertions; semantic equivalence is
/// checked independently by the SAT/UNSAT controls above, without a query goal.
fn assert_definition_encoding(program: &mut AYProgram, condition: Expr, datatype: bool) {
    let flag = program
        .declare_const(format!("definition_flag_{}", program.commands().len()), Sort::bool());
    let start = program.commands().len();
    crate::codegen_ay::emitter::define_property_flag(program, flag, condition);
    let definitions = &program.commands()[start..];
    assert_eq!(definitions.len(), if datatype { 2 } else { 1 });
    for definition in definitions {
        let Constraint::Assert { expr, .. } = definition else {
            panic!("definition emitted a non-assertion");
        };
        assert!(if datatype {
            matches!(expr.value(), ExprValue::Implies(..))
        } else {
            matches!(expr.value(), ExprValue::Eq(..))
        });
    }
}

#[test]
fn property_definition_policy_uses_typed_witnesses_not_names_or_other_declarations() {
    let witness = Sort::simple_enum_type("primitive_looking_bv8", ["Left", "Right"]);
    let mut program = AYProgram::new();
    let input = program.declare_const("unrelated", witness);
    for name in ["Layout", "Option", "Result", "Datatype", "write_volatile_then_eq_must_fail"] {
        let primitive = program.declare_const(name, Sort::bv8());
        assert_definition_encoding(&mut program, primitive.eq(Expr::bitvec_const(0u8, 8)), false);
    }
    let mut opaque_program = AYProgram::new();
    let opaque = Sort::uninterpreted("primitive_looking_bv8");
    let opaque_l = opaque_program.declare_const("opaque_left", opaque.clone());
    let opaque_r = opaque_program.declare_const("opaque_right", opaque);
    assert_definition_encoding(&mut opaque_program, opaque_l.eq(opaque_r), false);

    let tester = input.is_constructor("primitive_looking_bv8", "Left");
    let alias = program.declare_const("alias", Sort::bool());
    program.assert(alias.clone().eq(tester.clone()));
    assert_definition_encoding(&mut program, alias, false);
    assert_definition_encoding(&mut program, tester, true);
}

#[test]
fn property_definition_policy_finds_typed_intermediate_and_container_sorts() {
    let record = Sort::struct_type("Record", [("value", Sort::bv8())]);
    let value = Expr::var("record", record.clone());
    let selected = value.clone().field_select("Record", "value", Sort::bv8());
    let mut program = AYProgram::new();
    assert_definition_encoding(&mut program, selected.eq(Expr::bitvec_const(0u8, 8)), true);
    let constructed = Expr::datatype_constructor(
        "Record",
        "Record_mk",
        vec![Expr::bitvec_const(0u8, 8)],
        record.clone(),
    );
    assert_definition_encoding(&mut program, value.eq(constructed), true);
    // These are typed-AST routing controls, not unsupported container-solving
    // claims or dangling DatatypeRef declarations.
    for sort in [
        Sort::array(Sort::bv8(), record.clone()),
        Sort::array(record.clone(), Sort::bv8()),
        Sort::array(Sort::bv8(), Sort::seq(record.clone())),
        Sort::seq(Sort::array(Sort::bv8(), record.clone())),
    ] {
        let left = Expr::var("container_left", sort.clone());
        let right = Expr::var("container_right", sort);
        assert_definition_encoding(&mut program, left.eq(right), true);
    }
    for existential in [false, true] {
        let vars = vec![("unused_binder".to_string(), record.clone())];
        let body = Expr::var("body", Sort::bool());
        let quantified =
            if existential { Expr::exists(vars, body) } else { Expr::forall(vars, body) };
        assert_definition_encoding(&mut program, quantified, true);
    }
}

#[test]
fn property_definition_policy_walks_deep_and_shared_graphs_iteratively() {
    let sort = Sort::simple_enum_type("Witness", ["Left", "Right"]);
    let base = Expr::var("deep_input", sort).is_constructor("Witness", "Left");
    let mut layers = vec![base];
    for _ in 0..4096 {
        layers.push(layers.last().unwrap().clone().not());
    }
    let mut program = AYProgram::new();
    assert_definition_encoding(&mut program, layers.last().unwrap().clone(), true);
    // Keep every child alive while dropping its parents, so this detector test
    // does not instead exercise recursively dropping a deeply nested Arc tree.
    drop(program);
    while layers.pop().is_some() {}

    let primitive = Expr::var("shared_input", Sort::bool());
    let mut layers = vec![primitive];
    for _ in 0..48 {
        let previous = layers.last().unwrap().clone();
        layers.push(previous.clone().and(previous));
    }
    let mut program = AYProgram::new();
    assert_definition_encoding(&mut program, layers.last().unwrap().clone(), false);
    drop(program);
    while layers.pop().is_some() {}
}

#[test]
fn property_flags_keep_each_alternative_and_its_model_on_both_bmc_routes() {
    for ir_emitter in [false, true] {
        for selected in 0..4 {
            with_test_ay_ctx_for_source("pub fn property_flags() {}", |mut ctx| {
                let input = ctx.declare_var("property_input", Sort::bv8());
                ctx.assert(input.clone().eq(Expr::bitvec_const(selected, 8)));
                for alternative in 0..3 {
                    ctx.record_property_violation_full(
                        input.clone().eq(Expr::bitvec_const(alternative, 8)),
                        "kani_assert",
                        None,
                        Some(format!("alternative {alternative}")),
                    );
                }
                let original = ctx.bmc_vc.clone();
                let names: Vec<_> = original
                    .violations
                    .iter()
                    .map(|v| v.smt_var.clone().expect("recorded identity"))
                    .collect();
                assert_eq!(names.len(), 3);
                // UNSAT has no get-value command, matching the driver's use.
                let program = finish(&mut ctx, ir_emitter, selected < 3);
                assert_eq!(ctx.bmc_vc.violations, original.violations);
                assert_eq!(ctx.bmc_vc.constraints, original.constraints);
                let outputs = solve(&program, if selected < 3 { "sat" } else { "unsat" });
                if selected < 3 {
                    let model = outputs.last().expect("named model values");
                    for (index, name) in names.iter().enumerate() {
                        assert!(
                            model.contains(&format!("({name} {})", index == selected as usize)),
                            "route={ir_emitter}, selected={selected}: {model}"
                        );
                    }
                }
            });
        }
    }
}

#[test]
fn property_flags_preserve_infeasible_and_zero_property_queries() {
    for ir_emitter in [false, true] {
        with_test_ay_ctx_for_source("pub fn no_properties() {}", |mut ctx| {
            let program = finish(&mut ctx, ir_emitter, true);
            assert!(ctx.bmc_vc.violations.is_empty());
            assert!(program.to_string().contains("(assert false)"));
            assert!(!program.to_string().contains("(get-value"));
            solve(&program, "unsat");
        });
        with_test_ay_ctx_for_source("pub fn infeasible() {}", |mut ctx| {
            ctx.assert(Expr::bool_const(false));
            ctx.record_property_violation(Expr::bool_const(true), "kani_assert");
            let program = finish(&mut ctx, ir_emitter, false);
            solve(&program, "unsat");
        });
    }
}
