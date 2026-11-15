// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
use crate::codegen_ay::chc::ChcConfig;
use crate::codegen_ay::chc::codegen_types::CodegenTypes;
use crate::codegen_ay::chc::stubs_option_helpers::OptionHelpers;
use crate::codegen_ay::context::with_test_ay_ctx_for_source;
use crate::codegen_ay::test_fixtures::find_instance_by_suffix;
use ay_bindings::{ExprValue, Sort};
use rustc_public::mir::TerminatorKind;
use rustc_public::ty::{RigidTy, TyKind};
use std::collections::HashSet;

const SOURCE: &str = r#"
    pub fn outer() -> u8 { 7 }
    pub fn hint_slice(it: core::slice::Iter<'_, u8>) -> (usize, Option<usize>) { it.size_hint() }
    pub fn hint_chars(it: core::str::Chars<'_>) -> (usize, Option<usize>) { it.size_hint() }
    pub fn hint_take(it: core::iter::Take<core::str::Chars<'_>>) -> (usize, Option<usize>) { it.size_hint() }
    pub fn len_slice(it: core::slice::Iter<'_, u8>) -> usize { it.len() }
    pub fn len_take(it: core::iter::Take<core::slice::Iter<'_, u8>>) -> usize { it.len() }
    pub fn len_map(it: core::iter::Map<core::slice::Iter<'_, u8>, fn(&u8) -> u8>) -> usize { it.len() }
    pub fn len_reborrow(it: &mut core::slice::Iter<'_, u8>) -> usize { it.len() }
    pub struct Custom { pub marker: u8 }
    impl Iterator for Custom {
        type Item = u8;
        fn next(&mut self) -> Option<u8> { None }
        fn size_hint(&self) -> (usize, Option<usize>) { panic!("custom hint must run") }
    }
    impl ExactSizeIterator for Custom {
        fn len(&self) -> usize { panic!("custom len must run") }
    }
    pub fn custom_hint(it: Custom) -> (usize, Option<usize>) { it.size_hint() }
    pub fn custom_len(it: Custom) -> usize { it.len() }
    pub fn custom_take_hint(it: core::iter::Take<Custom>) -> (usize, Option<usize>) { it.size_hint() }
    pub fn custom_take_len(it: core::iter::Take<Custom>) -> usize { it.len() }
    pub fn custom_map_hint(it: core::iter::Map<Custom, fn(u8) -> u8>) -> (usize, Option<usize>) { it.size_hint() }
    pub fn custom_map_len(it: core::iter::Map<Custom, fn(u8) -> u8>) -> usize { it.len() }
    pub struct DefaultLen { pub marker: u8 }
    impl Iterator for DefaultLen {
        type Item = u8;
        fn next(&mut self) -> Option<u8> { None }
        fn size_hint(&self) -> (usize, Option<usize>) { panic!("default len must run its custom hint") }
    }
    impl ExactSizeIterator for DefaultLen {}
    pub fn custom_default_len(it: DefaultLen) -> usize { it.len() }
"#;

fn bv(value: u64) -> Expr {
    Expr::bitvec_const(value, 64)
}

fn carrier(sort: &Sort, pos: u64, len: u64, limit: u64) -> Expr {
    if let Some(width) = sort.bitvec_width() {
        return Expr::bitvec_const(0u8, width);
    }
    if sort.is_bool() {
        return Expr::bool_const(false);
    }
    if let Some(array) = sort.array_sort() {
        return Expr::const_array(
            array.index_sort.clone(),
            carrier(&array.element_sort, pos, len, limit),
        );
    }
    let dt = sort.datatype_sort().unwrap();
    let ctor = &dt.constructors[0];
    let values = ctor
        .fields
        .iter()
        .map(|field| match &*field.name {
            "fld_pos" => bv(pos),
            "fld_len" => bv(len),
            "fld_n" => bv(limit),
            _ => carrier(&field.sort, pos, len, limit),
        })
        .collect();
    Expr::datatype_constructor(&dt.name, &ctor.name, values, sort.clone())
}

fn declarations(sort: &Sort, seen: &mut HashSet<String>, output: &mut String) {
    if let Some(array) = sort.array_sort() {
        declarations(&array.element_sort, seen, output);
    }
    if let Some(dt) = sort.datatype_sort()
        && seen.insert(dt.name.to_string())
    {
        for ctor in &dt.constructors {
            for field in &ctor.fields {
                declarations(&field.sort, seen, output);
            }
        }
        output.push_str(&ay_bindings::Constraint::declare_datatype(dt.clone()).to_string());
        output.push('\n');
    }
}

fn assert_formula(formula: Expr, sort: &Sort) {
    let mut defs = String::new();
    declarations(sort, &mut HashSet::new(), &mut defs);
    for (formula, expected) in [(formula.clone(), "sat"), (formula.not(), "unsat")] {
        let commands = ay_frontend::parse(&format!(
            "(set-logic ALL)\n{defs}(assert {formula})\n(check-sat)\n"
        ))
        .unwrap();
        let mut solver = ay_dpll::Executor::new();
        solver.set_timeout(Some(std::time::Duration::from_secs(5)));
        let output = solver.execute_all(&commands).unwrap();
        assert!(output.iter().any(|line| line.trim() == expected), "{expected}: {output:?}");
    }
}

#[test]
fn nested_native_queries_use_the_nested_namespace_current_cursor_and_actual_result_sort() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let outer = find_instance_by_suffix(ctx.tcx, "outer").body().unwrap();
        let mut chc = ChcCtx::new(ctx.tcx, &outer, "outer", ChcConfig::default());
        for (name, lower, upper) in [
            ("hint_slice", 4, Some(4)),
            ("hint_chars", 1, Some(4)),
            ("hint_take", 1, Some(3)),
            ("len_slice", 4, None),
            ("len_take", 3, None),
            ("len_map", 4, None),
            ("len_reborrow", 4, None),
        ] {
            let body = find_instance_by_suffix(ctx.tcx, name).body().unwrap();
            let (func, args) = body
                .blocks
                .iter()
                .find_map(|block| match &block.terminator.kind {
                    TerminatorKind::Call { func, args, .. } => Some((func, args)),
                    _ => None,
                })
                .unwrap();
            let mut ty = body.locals()[1].ty;
            while let TyKind::RigidTy(RigidTy::Ref(_, inner, _)) = ty.kind() {
                ty = inner;
            }
            let sort = ChcCtx::translate_ty(ty).unwrap();
            let receiver = carrier(&sort, 2, 6, 3);
            let locals = HashMap::from([(1, receiver.clone())]);
            let fields = HashMap::new();
            let result = try_inline_native_iterator_query(
                &mut chc,
                func,
                args,
                &[receiver.clone()],
                &body,
                &locals,
                &PlaceResolver::FieldMap(&fields),
            )
            .unwrap_or_else(|| panic!("{name} must resolve its native receiver"));
            let output_sort = ChcCtx::translate_ty(body.locals()[0].ty).unwrap();
            assert_eq!(result.value.sort(), &output_sort, "{name}");
            assert!(result.alias_updates.is_empty() && result.deferred_checks.is_empty(), "{name}");
            let formula = if let Some(upper) = upper {
                let ExprValue::DatatypeConstructor { args, .. } = result.value.value() else {
                    panic!("native hint tuple")
                };
                args[0].clone().eq(bv(lower)).and(chc.option_is_some(args[1].clone())).and(
                    chc.option_unwrap_value_on_some_path(args[1].clone()).unwrap().eq(bv(upper)),
                )
            } else {
                result.value.clone().eq(bv(lower))
            };
            assert_formula(formula, &output_sort);
            let bad = carrier(&ChcCtx::translate_ty(outer.locals()[0].ty).unwrap(), 0, 0, 0);
            assert!(
                chc.native_iterator_query_instance(func, body.locals())
                    .and_then(|instance| chc.native_iterator_query_expr(&instance, &bad))
                    .is_none(),
                "{name} must reject the wrong receiver value sort"
            );
            if name == "hint_slice" {
                let wrapped = find_instance_by_suffix(ctx.tcx, "len_take").body().unwrap();
                let wrapped_sort = ChcCtx::translate_ty(wrapped.locals()[1].ty).unwrap();
                let wrong_receiver = carrier(&wrapped_sort, 2, 6, 0);
                assert!(
                    chc.native_iterator_query_instance(func, body.locals())
                        .and_then(
                            |instance| chc.native_iterator_query_expr(&instance, &wrong_receiver)
                        )
                        .is_none(),
                    "a SliceIter callee must not consume a Take wrapper's inner carrier"
                );
            }
            if name != "len_reborrow" {
                assert!(
                    try_inline_native_iterator_query(
                        &mut chc,
                        func,
                        args,
                        &[],
                        &body,
                        &locals,
                        &PlaceResolver::FieldMap(&fields),
                    )
                    .is_some(),
                    "{name} must resolve the actual borrowed owner before argument translation"
                );
            }
        }
    });
}

#[test]
fn nested_native_queries_refuse_custom_methods_active_stubs_and_unsupported_inner_effects() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let outer = find_instance_by_suffix(ctx.tcx, "outer").body().unwrap();
        let mut chc = ChcCtx::new(ctx.tcx, &outer, "outer", ChcConfig::default());
        for name in [
            "custom_hint",
            "custom_len",
            "custom_map_hint",
            "custom_map_len",
            "custom_default_len",
            "custom_take_hint",
            "custom_take_len",
            "hint_slice",
        ] {
            let body = find_instance_by_suffix(ctx.tcx, name).body().unwrap();
            let (func, args) = body
                .blocks
                .iter()
                .find_map(|block| match &block.terminator.kind {
                    TerminatorKind::Call { func, args, .. } => Some((func, args)),
                    _ => None,
                })
                .unwrap();
            let sort = ChcCtx::translate_ty(body.locals()[1].ty).unwrap();
            let fields = HashMap::new();
            let locals = HashMap::new();
            let receiver = carrier(&sort, 2, 6, 3);
            let resolver = PlaceResolver::FieldMap(&fields);
            if name.starts_with("custom_take") {
                assert!(
                    try_inline_native_iterator_query(
                        &mut chc,
                        func,
                        args,
                        &[receiver],
                        &body,
                        &locals,
                        &resolver
                    )
                    .is_none(),
                    "nonzero {name} must run the inner implementation"
                );
                let zero = carrier(&sort, 2, 6, 0);
                assert!(
                    try_inline_native_iterator_query(
                        &mut chc,
                        func,
                        args,
                        &[zero],
                        &body,
                        &locals,
                        &resolver
                    )
                    .is_some(),
                    "native Take(0) skips its inner query"
                );
            } else if name.starts_with("custom") {
                assert!(
                    try_inline_native_iterator_query(
                        &mut chc,
                        func,
                        args,
                        &[receiver],
                        &body,
                        &locals,
                        &resolver
                    )
                    .is_none(),
                    "{name} body carries its own effects"
                );
            } else {
                let TyKind::RigidTy(RigidTy::FnDef(def, _)) =
                    func.ty(body.locals()).unwrap().kind()
                else {
                    panic!("direct query")
                };
                let _stubs = crate::kani_middle::transform::UnitStubsTestScope::install(
                    HashMap::from([(def, def)]),
                );
                assert!(
                    try_inline_native_iterator_query(
                        &mut chc,
                        func,
                        args,
                        &[receiver],
                        &body,
                        &locals,
                        &resolver
                    )
                    .is_none(),
                    "unit stubs retain their changed program"
                );
            }
        }
    });
}

#[test]
fn nested_dispatch_answers_native_queries_before_walking_raw_pointer_fields() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        for name in ["hint_slice", "len_slice"] {
            let body = find_instance_by_suffix(ctx.tcx, name).body().unwrap();
            let mut chc = ChcCtx::new(ctx.tcx, &body, name, ChcConfig::default());
            let (func, args, destination) = body
                .blocks
                .iter()
                .find_map(|block| match &block.terminator.kind {
                    TerminatorKind::Call { func, args, destination, .. } => {
                        Some((func, args, destination))
                    }
                    _ => None,
                })
                .unwrap();
            let sort = ChcCtx::translate_ty(body.locals()[1].ty).unwrap();
            let receiver = carrier(&sort, 2, 6, 0);
            let instance = chc.native_iterator_query_instance(func, body.locals()).unwrap();
            let expected = chc.native_iterator_query_expr(&instance, &receiver).unwrap();
            let locals = HashMap::from([(1, receiver)]);
            let fields = HashMap::new();
            let result = super::super::nested_call::try_inline_nested_call(
                &mut chc,
                func,
                args,
                &body,
                &locals,
                &PlaceResolver::FieldMap(&fields),
                &HashMap::new(),
                &HashMap::new(),
                destination,
                0,
            )
            .unwrap_or_else(|| panic!("{name} dispatch must preserve the logical carrier"));
            assert_eq!(result.value, expected, "{name}");
            assert!(result.alias_updates.is_empty() && result.deferred_checks.is_empty(), "{name}");
        }
    });
}
