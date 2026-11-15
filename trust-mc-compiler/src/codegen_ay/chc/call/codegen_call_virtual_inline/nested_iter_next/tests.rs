// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
use crate::codegen_ay::chc::ChcConfig;
use crate::codegen_ay::context::with_test_ay_ctx_for_source;
use crate::codegen_ay::test_fixtures::find_instance_by_suffix;
use crate::codegen_ay::types::CtorFieldExt;
use rustc_public::mir::TerminatorKind;

const SOURCE: &str = r#"
    pub fn chars_type(source: &str) -> core::str::Chars<'_> { source.chars() }
    pub fn real(source: &mut core::str::Chars<'_>) -> Option<char> { source.next() }
    pub struct Fake;
    impl Fake { pub fn next(&mut self) -> Option<char> { Some('x') } }
    pub fn fake(source: &mut Fake) -> Option<char> { source.next() }
"#;

fn bv(value: u64) -> Expr {
    Expr::bitvec_const(value, POINTER_WIDTH)
}

fn field_sort(sort: &Sort, name: &str) -> Sort {
    sort.datatype_sort().unwrap().constructors[0].field(name).unwrap().sort.clone()
}

fn field(value: &Expr, name: &str) -> Expr {
    value.clone().field_select(
        value.sort().datatype_name().unwrap(),
        name,
        field_sort(value.sort(), name),
    )
}

fn structure(sort: &Sort, fields: &[(&str, Expr)]) -> Expr {
    let dt = sort.datatype_sort().unwrap();
    let ctor = &dt.constructors[0];
    let values = ctor
        .fields
        .iter()
        .map(|field| fields.iter().find(|(name, _)| *name == field.name).unwrap().1.clone())
        .collect();
    Expr::datatype_constructor(&dt.name, &ctor.name, values, sort.clone())
}

fn chars(sort: &Sort, bytes: &[u8], pos: u64) -> Expr {
    let iter_sort = field_sort(sort, "fld_iter");
    let slice_sort = field_sort(&iter_sort, "fld_vec");
    let data = bytes.iter().enumerate().fold(
        Expr::const_array(Sort::bitvec(64), Expr::bitvec_const(0u8, 8)),
        |data, (index, byte)| data.store(bv(index as u64), Expr::bitvec_const(*byte, 8)),
    );
    let slice = structure(
        &slice_sort,
        &[("fld_ptr", bv(4096)), ("fld_len", bv(bytes.len() as u64)), ("fld_data", data)],
    );
    let iter = structure(&iter_sort, &[("fld_vec", slice), ("fld_pos", bv(pos))]);
    structure(sort, &[("fld_iter", iter)])
}

fn assert_formula(formula: Expr, expected: bool, output_sort: &Sort) {
    let declaration =
        ay_bindings::Constraint::declare_datatype(output_sort.datatype_sort().unwrap().clone());
    for (formula, expected) in [(formula.clone(), expected), (formula.not(), !expected)] {
        let commands = ay_frontend::parse(&format!(
            "(set-logic ALL)\n{declaration}\n(assert {formula})\n(check-sat)\n"
        ))
        .unwrap();
        let mut solver = ay_dpll::Executor::new();
        solver.set_timeout(Some(std::time::Duration::from_secs(5)));
        let output = solver.execute_all(&commands).unwrap();
        let wanted = if expected { "sat" } else { "unsat" };
        assert!(output.iter().any(|line| line.trim() == wanted), "{wanted}: {output:?}");
    }
}

#[test]
fn nested_chars_next_decodes_unicode_and_writes_back_the_same_cursor() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let body = find_instance_by_suffix(ctx.tcx, "real").body().unwrap();
        let mut chc = ChcCtx::new(ctx.tcx, &body, "real", ChcConfig::default());
        let chars_body = find_instance_by_suffix(ctx.tcx, "chars_type").body().unwrap();
        let chars_sort = ChcCtx::translate_ty(chars_body.locals()[0].ty).unwrap();
        let (func, args) = body
            .blocks
            .iter()
            .find_map(|block| match &block.terminator.kind {
                TerminatorKind::Call { func, args, .. } => Some((func, args)),
                _ => None,
            })
            .unwrap();
        let (authenticated_chars_sort, output_sort) =
            authenticated_chars_next_sorts(&chc, func, &body).unwrap();
        assert_eq!(authenticated_chars_sort, chars_sort);
        let fields = HashMap::new();
        let locals = HashMap::new();
        let resolver = PlaceResolver::FieldMap(&fields);
        let mut receiver = chars(&chars_sort, "xé🦀".as_bytes(), 1);
        for (expected, position) in [(Some('é'), 3), (Some('🦀'), 7), (None, 7)] {
            let result = try_inline_iter_next_call(
                &mut chc,
                func,
                "core::str::iter::Chars::next",
                args,
                &[receiver],
                &body,
                &locals,
                &resolver,
            )
            .expect("authenticated nested next");
            assert_eq!(result.deferred_checks.len(), 1);
            assert_eq!(result.deferred_checks[0].kind, PropertyKind::UndefinedBehavior);
            let mut formula = result.deferred_checks[0].check.clone();
            formula = formula.and(
                chc.option_is_some(result.value.clone()).eq(Expr::bool_const(expected.is_some())),
            );
            if let Some(expected) = expected {
                formula = formula.and(
                    chc.option_unwrap_value_on_some_path(result.value)
                        .unwrap()
                        .eq(Expr::bitvec_const(expected as u32, 32)),
                );
            }
            receiver = result.alias_updates[&1].clone();
            formula = formula.and(field(&field(&receiver, "fld_iter"), "fld_pos").eq(bv(position)));
            assert_formula(formula, true, &output_sort);
        }
        let invalid =
            inline_chars_next(&mut chc, chars(&chars_sort, &[0xc3], 0), &output_sort).unwrap();
        let check = invalid.deferred_checks[0].clone();
        assert_formula(check.check.clone(), false, &output_sort);
        assert_formula(check.weaken_by_guard(&Expr::bool_const(false)).check, true, &output_sort);
    });
}

#[test]
fn nested_chars_next_refuses_lookalikes_and_active_unit_stubs() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        for name in ["real", "fake"] {
            let body = find_instance_by_suffix(ctx.tcx, name).body().unwrap();
            let chc = ChcCtx::new(ctx.tcx, &body, name, ChcConfig::default());
            let func = body
                .blocks
                .iter()
                .find_map(|block| match &block.terminator.kind {
                    TerminatorKind::Call { func, .. } => Some(func),
                    _ => None,
                })
                .unwrap();
            assert_eq!(authenticated_chars_next_sorts(&chc, func, &body).is_some(), name == "real");
            if name == "real" {
                let TyKind::RigidTy(RigidTy::FnDef(def, _)) =
                    func.ty(body.locals()).unwrap().kind()
                else {
                    panic!("direct next")
                };
                let _stubs = crate::kani_middle::transform::UnitStubsTestScope::install(
                    HashMap::from([(def, def)]),
                );
                assert!(authenticated_chars_next_sorts(&chc, func, &body).is_none());
            }
        }
    });
}
