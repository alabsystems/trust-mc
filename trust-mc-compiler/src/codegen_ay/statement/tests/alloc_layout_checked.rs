// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Exercise the checked Layout producer with actual MIR destination types.

use super::*;

const CHECKED_LAYOUT_SOURCE: &str = r#"
use core::alloc::{Layout, LayoutError};

pub fn checked_layout(size: usize, align: usize) -> Result<Layout, LayoutError> {
    Layout::from_size_align(size, align)
}

pub fn layout_validity(size: usize, align: usize) -> bool {
    Layout::from_size_align(size, align).is_ok()
}
"#;

fn set_layout_args(codegen: &mut StatementCodegen<'_, '_, '_>, size: Expr, align: Expr) {
    let size_base = codegen.ssa_base_name(&local_place(1));
    let align_base = codegen.ssa_base_name(&local_place(2));
    codegen.env_update(size_base, size);
    codegen.env_update(align_base, align);
}

fn construct_layout(codegen: &mut StatementCodegen<'_, '_, '_>) -> Expr {
    let dest = local_place(0);
    assert_eq!(
        codegen.codegen_layout_from_size_align(
            &[local_operand(1), local_operand(2)],
            &dest,
            Some(1)
        ),
        Some(1)
    );
    let base = codegen.ssa_base_name(&dest);
    let value = codegen.env_lookup(&base).expect("checked Result binding").clone();
    assert_eq!(
        value.sort(),
        &codegen.infer_sort_from_place(&dest).expect("actual MIR Result sort")
    );
    value
}

fn result_is(value: &Expr, variant: &str) -> Expr {
    let dt = value.sort().datatype_sort().expect("Result datatype");
    let name = StatementCodegen::find_result_constructor(value.sort(), variant, &dt.name)
        .expect("declared Result constructor");
    value.clone().is_constructor(&dt.name, name)
}

fn result_payload(value: &Expr, variant: &str) -> Expr {
    let dt = value.sort().datatype_sort().expect("Result datatype");
    let name = StatementCodegen::find_result_constructor(value.sort(), variant, &dt.name)
        .expect("declared Result constructor");
    let ctor = dt.constructors.iter().find(|ctor| ctor.name == name).expect("constructor");
    assert_eq!(ctor.fields.len(), 1);
    let field = &ctor.fields[0];
    value.clone().field_select(&dt.name, &field.name, field.sort.clone())
}

/// Query both a safe assertion and its false twin. SAT is required explicitly
/// so an inconsistent producer cannot pass the positive tests vacuously.
fn assert_layout_query(
    ctx: &crate::codegen_ay::context::AYCtx<'_, 'static>,
    violation: Expr,
    expected: &str,
) {
    let mut vc = ctx.bmc_vc.clone();
    vc.violations.clear();
    vc.model_queries.clear();
    vc.add_violation(
        trust_mc_core::Violation::new(
            trust_mc_core::PropertyId::new(0),
            trust_mc_core::PropertyKind::Assertion,
            violation,
        )
        .with_smt_var("ay_violation_checked_layout"),
    );
    let smt = super::emit_bmc(vc).to_string();
    let verdict = super::run_ay_on_smt2_with_timeout(
        &smt,
        super::ay_test_timeout_secs_or(super::AY_TEST_TIMEOUT_SECS),
    )
    .unwrap_or_else(|err| panic!("{err}\n{smt}"));
    assert_eq!(verdict, expected, "checked Layout query:\n{smt}");
}

#[test]
fn checked_layout_matches_std_boundaries_and_retains_both_fields() {
    with_test_ay_ctx_for_source(CHECKED_LAYOUT_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "checked_layout");
        let body = instance.body().expect("MIR body");
        ctx.set_current_fn(instance);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, TupleUsageAnalysis::run(&body));
        let bound = 1usize << (usize::BITS - 1);
        for (size, align) in [
            (1, 3), // Fresh Err destination; the overwrite test starts fresh Ok.
            (3, 8),
            (0, 1),
            (0, bound),
            (1, bound),
            (bound - 1, 1),
            (bound, 1),
            (bound - 8, 8),
            (bound - 7, 8),
            (0, 0),
            (usize::MAX, 1),
        ] {
            set_layout_args(
                &mut codegen,
                Expr::bitvec_const(size as u128, POINTER_WIDTH),
                Expr::bitvec_const(align as u128, POINTER_WIDTH),
            );
            let value = construct_layout(&mut codegen);
            let expected = match std::alloc::Layout::from_size_align(size, align) {
                Ok(layout) => {
                    let payload = result_payload(&value, "Ok");
                    let (actual_size, actual_align) = codegen
                        .try_extract_layout_fields(&payload)
                        .expect("complete Layout payload");
                    result_is(&value, "Ok")
                        .and(
                            actual_size
                                .eq(Expr::bitvec_const(layout.size() as u128, POINTER_WIDTH)),
                        )
                        .and(
                            actual_align
                                .eq(Expr::bitvec_const(layout.align() as u128, POINTER_WIDTH)),
                        )
                }
                Err(_) => result_is(&value, "Err")
                    .and(result_payload(&value, "Err").eq(Expr::bool_const(false))),
            };
            assert_layout_query(codegen.ctx, expected.clone().not(), "unsat");
            assert_layout_query(codegen.ctx, expected, "sat");
        }
    });
}

#[test]
fn checked_layout_symbolic_input_keeps_valid_and_invalid_outcomes() {
    with_test_ay_ctx_for_source(CHECKED_LAYOUT_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "checked_layout");
        let body = instance.body().expect("MIR body");
        ctx.set_current_fn(instance);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, TupleUsageAnalysis::run(&body));
        let size = codegen.ctx.declare_var("layout_input_size", Sort::bitvec(POINTER_WIDTH));
        let align = codegen.ctx.declare_var("layout_input_align", Sort::bitvec(POINTER_WIDTH));
        set_layout_args(&mut codegen, size.clone(), align.clone());
        let value = construct_layout(&mut codegen);
        let is_ok = result_is(&value, "Ok");
        let is_err = result_is(&value, "Err");
        let valid_inputs = size
            .clone()
            .eq(Expr::bitvec_const(3, POINTER_WIDTH))
            .and(align.clone().eq(Expr::bitvec_const(8, POINTER_WIDTH)));
        let invalid_align = align.clone().eq(Expr::bitvec_const(3, POINTER_WIDTH));
        assert_layout_query(codegen.ctx, valid_inputs.clone().and(is_ok.clone()), "sat");
        assert_layout_query(codegen.ctx, valid_inputs.and(is_err.clone()), "unsat");
        assert_layout_query(codegen.ctx, invalid_align.clone().and(is_err), "sat");
        assert_layout_query(codegen.ctx, invalid_align.and(is_ok.clone()), "unsat");
        let (payload_size, payload_align) = codegen
            .try_extract_layout_fields(&result_payload(&value, "Ok"))
            .expect("complete symbolic Layout payload");
        assert_layout_query(
            codegen.ctx,
            is_ok.and(payload_size.eq(size).and(payload_align.eq(align)).not()),
            "unsat",
        );
    });
}

#[test]
fn layout_validity_predicate_does_not_assume_safe_inputs_are_valid() {
    with_test_ay_ctx_for_source(CHECKED_LAYOUT_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "layout_validity");
        let body = instance.body().expect("MIR body");
        ctx.set_current_fn(instance);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, TupleUsageAnalysis::run(&body));
        for (size, align) in [(3usize, 8usize), (1, 3), (usize::MAX, 1), (0, 0)] {
            set_layout_args(
                &mut codegen,
                Expr::bitvec_const(size as u128, POINTER_WIDTH),
                Expr::bitvec_const(align as u128, POINTER_WIDTH),
            );
            assert_eq!(
                codegen.codegen_layout_is_size_align_valid(
                    &[local_operand(1), local_operand(2)],
                    &local_place(0),
                    Some(1)
                ),
                Some(1)
            );
            let base = codegen.ssa_base_name(&local_place(0));
            let value = codegen.env_lookup(&base).expect("validity binding").clone();
            let expected =
                Expr::bool_const(std::alloc::Layout::from_size_align(size, align).is_ok());
            let correct = value.eq(expected);
            assert_layout_query(codegen.ctx, correct.clone().not(), "unsat");
            assert_layout_query(codegen.ctx, correct, "sat");
        }
    });
}

#[test]
fn checked_layout_wrong_destination_or_missing_args_remains_unassigned() {
    with_test_ay_ctx_for_source(CHECKED_LAYOUT_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "layout_validity");
        let body = instance.body().expect("MIR body");
        ctx.set_current_fn(instance);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, TupleUsageAnalysis::run(&body));
        set_layout_args(
            &mut codegen,
            Expr::bitvec_const(3, POINTER_WIDTH),
            Expr::bitvec_const(8, POINTER_WIDTH),
        );
        let dest = local_place(0);
        let base = codegen.ssa_base_name(&dest);
        assert!(codegen.env_lookup(&base).is_none());
        assert_eq!(
            codegen.codegen_layout_from_size_align(
                &[local_operand(1), local_operand(2)],
                &dest,
                Some(1)
            ),
            None
        );
        assert_eq!(
            codegen.codegen_layout_from_size_align(&[local_operand(1)], &dest, Some(1)),
            None
        );
        assert!(codegen.env_lookup(&base).is_none());
    });
}

#[test]
fn checked_layout_overwrite_freshens_stale_views_and_keeps_old_scalar_values() {
    with_test_ay_ctx_for_source(CHECKED_LAYOUT_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "checked_layout");
        let body = instance.body().expect("MIR body");
        ctx.set_current_fn(instance);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, TupleUsageAnalysis::run(&body));
        set_layout_args(
            &mut codegen,
            Expr::bitvec_const(4, POINTER_WIDTH),
            Expr::bitvec_const(8, POINTER_WIDTH),
        );
        let old = construct_layout(&mut codegen);
        let old_is_ok = result_is(&old, "Ok");
        assert!(!codegen.ctx.unsupported_constructs.contains_key("store_flattened_components"));

        // These are the real flattened view families a read/borrow may leave
        // behind. The new whole-value binding must not keep any old view.
        let base = codegen.ssa_base_name(&local_place(0));
        let old_payload = result_payload(&old, "Ok");
        let old_views = [
            (format!("{base}.0"), Expr::bitvec_const(0, POINTER_WIDTH)),
            (format!("{base}.1"), old_payload.clone()),
            (format!("{base}_variant_0_field_0"), old_payload),
        ];
        for (key, value) in &old_views {
            codegen.env_update(key.clone(), value.clone());
        }
        set_layout_args(
            &mut codegen,
            Expr::bitvec_const(3, POINTER_WIDTH),
            Expr::bitvec_const(16, POINTER_WIDTH),
        );
        let new = construct_layout(&mut codegen);
        assert!(codegen.ctx.unsupported_constructs.contains_key("store_flattened_components"));
        for (key, old_value) in old_views {
            let fresh = codegen.env_lookup(&key).expect("declared conservative view");
            assert_ne!(fresh, &old_value);
            assert!(matches!(fresh.value(), ExprValue::Var { .. }));
        }
        let (size, align) =
            codegen.try_extract_layout_fields(&result_payload(&new, "Ok")).expect("new Layout");
        let correct = old_is_ok
            .clone()
            .and(result_is(&new, "Ok"))
            .and(size.eq(Expr::bitvec_const(3, POINTER_WIDTH)))
            .and(align.eq(Expr::bitvec_const(16, POINTER_WIDTH)));
        assert_layout_query(codegen.ctx, correct.clone().not(), "unsat");
        assert_layout_query(codegen.ctx, correct, "sat");

        set_layout_args(
            &mut codegen,
            Expr::bitvec_const(3, POINTER_WIDTH),
            Expr::bitvec_const(3, POINTER_WIDTH),
        );
        let invalid = construct_layout(&mut codegen);
        let correct = old_is_ok.and(result_is(&invalid, "Err"));
        assert_layout_query(codegen.ctx, correct.clone().not(), "unsat");
        assert_layout_query(codegen.ctx, correct, "sat");
    });
}

#[test]
fn checked_layout_guarded_overwrite_keeps_prestate_and_kills_old_refinements() {
    with_test_ay_ctx_for_source(CHECKED_LAYOUT_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "checked_layout");
        let body = instance.body().expect("MIR body");
        ctx.set_current_fn(instance);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, TupleUsageAnalysis::run(&body));
        set_layout_args(
            &mut codegen,
            Expr::bitvec_const(4, POINTER_WIDTH),
            Expr::bitvec_const(8, POINTER_WIDTH),
        );
        let old = construct_layout(&mut codegen);
        let dest = local_place(0);
        let place_key = codegen.variant_fact_place_key(&dest).expect("Result storage identity");
        let TyKind::RigidTy(RigidTy::Adt(adt_def, _)) =
            dest.ty(body.locals()).into_option().expect("Result type").kind()
        else {
            panic!("Result ADT expected");
        };
        let dt = old.sort().datatype_sort().expect("Result datatype");
        let dt_name: std::sync::Arc<str> = dt.name.as_str().into();
        let ctor_names: Vec<std::sync::Arc<str>> =
            dt.constructors.iter().map(|c| c.name.as_str().into()).collect();
        codegen.discr_of_local.insert(
            1,
            super::super::DiscrScrutinee {
                place_key: place_key.clone(),
                dt_name: dt_name.clone(),
                ctor_names: ctor_names.clone(),
                adt_def,
            },
        );
        codegen.current_variant_facts.push(super::super::VariantFact {
            place_key,
            dt_name,
            ctor_idx: 0,
            ctor_name: ctor_names[0].clone(),
            guard: Expr::bool_const(true),
        });
        let branch = codegen.ctx.declare_var("layout_overwrite_branch", Sort::bool());
        codegen.current_path_condition = Some(branch.clone());
        set_layout_args(
            &mut codegen,
            Expr::bitvec_const(3, POINTER_WIDTH),
            Expr::bitvec_const(16, POINTER_WIDTH),
        );
        let new = construct_layout(&mut codegen);
        assert!(codegen.discr_of_local.is_empty());
        assert!(codegen.current_variant_facts.is_empty());
        let (size, align) = codegen
            .try_extract_layout_fields(&result_payload(&new, "Ok"))
            .expect("guarded payload");
        let wanted_size = Expr::ite(
            branch.clone(),
            Expr::bitvec_const(3, POINTER_WIDTH),
            Expr::bitvec_const(4, POINTER_WIDTH),
        );
        let wanted_align = Expr::ite(
            branch.clone(),
            Expr::bitvec_const(16, POINTER_WIDTH),
            Expr::bitvec_const(8, POINTER_WIDTH),
        );
        let correct = result_is(&old, "Ok")
            .and(result_is(&new, "Ok"))
            .and(size.eq(wanted_size))
            .and(align.eq(wanted_align));
        assert_layout_query(codegen.ctx, correct.clone().not(), "unsat");
        assert_layout_query(codegen.ctx, correct.clone().and(branch.clone()), "sat");
        assert_layout_query(codegen.ctx, correct.and(branch.not()), "sat");
    });
}
