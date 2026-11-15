// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
use crate::codegen_ay::chc::ChcConfig;
use crate::codegen_ay::chc::codegen_types::CodegenTypes;
use crate::codegen_ay::context::with_test_ay_ctx_for_source;
use crate::codegen_ay::test_fixtures::find_instance_by_suffix;
use crate::kani_middle::std_abstraction::is_native_iterator_size_hint;
use rustc_public::mir::TerminatorKind;
use std::collections::{HashMap, HashSet};

const SOURCE: &str = r#"
    pub fn chars_type(s: &str) -> core::str::Chars<'_> { s.chars() }
    fn scalar(c: char) -> u32 { c as u32 }
    pub fn map_type(s: &str) -> core::iter::Map<core::str::Chars<'_>, fn(char) -> u32> {
        s.chars().map(scalar as fn(char) -> u32)
    }
    pub fn take_type(s: &str) -> core::iter::Take<core::str::Chars<'_>> { s.chars().take(4) }
    pub fn exact_type(s: &[u8]) -> core::slice::Iter<'_, u8> { s.iter() }
    pub fn take_exact_type(s: &[u8]) -> core::iter::Take<core::slice::Iter<'_, u8>> {
        s.iter().take(4)
    }
    pub fn rev_type(s: &str) -> core::iter::Rev<core::str::Chars<'_>> { s.chars().rev() }
    pub fn copied_type(s: &[u8]) -> core::iter::Copied<core::slice::Iter<'_, u8>> { s.iter().copied() }
    pub fn cloned_type(s: &[u8]) -> core::iter::Cloned<core::slice::Iter<'_, u8>> { s.iter().cloned() }
    fn byte(x: &u8) -> u8 { *x }
    pub fn map_exact_type(s: &[u8]) -> core::iter::Map<core::slice::Iter<'_, u8>, fn(&u8) -> u8> {
        s.iter().map(byte as fn(&u8) -> u8)
    }
    pub struct Fake { pub marker: u8 }
    impl Iterator for Fake {
        type Item = u8;
        fn next(&mut self) -> Option<u8> { None }
        fn size_hint(&self) -> (usize, Option<usize>) { panic!("must run the custom body") }
    }
    pub fn take_unknown_type() -> core::iter::Take<Fake> { Fake { marker: 0 }.take(0) }
    pub fn real(s: &str) -> (usize, Option<usize>) { s.chars().size_hint() }
    pub fn taken(s: &str) -> (usize, Option<usize>) { s.chars().take(4).size_hint() }
    pub fn borrowed(s: &mut core::str::Chars<'_>) -> (usize, Option<usize>) {
        Iterator::size_hint(&s)
    }
    pub fn fake(s: &Fake) -> (usize, Option<usize>) { s.size_hint() }
"#;

fn bv(n: u64) -> Expr {
    Expr::bitvec_const(n, POINTER_WIDTH)
}

fn value(sort: &Sort, pos: u64, len: u64, limit: u64) -> Expr {
    if let Some(width) = sort.bitvec_width() {
        return Expr::bitvec_const(0u64, width);
    }
    if let Some(array) = sort.array_sort() {
        return Expr::const_array(
            array.index_sort.clone(),
            value(&array.element_sort, pos, len, limit),
        );
    }
    let dt = sort.datatype_sort().expect("iterator struct");
    assert_eq!(dt.constructors.len(), 1);
    let ctor = &dt.constructors[0];
    let fields = ctor
        .fields
        .iter()
        .map(|field| match &*field.name {
            "fld_pos" => bv(pos),
            "fld_len" => bv(len),
            "fld_n" => bv(limit),
            _ => value(&field.sort, pos, len, limit),
        })
        .collect();
    Expr::datatype_constructor(&dt.name, &ctor.name, fields, sort.clone())
}

fn declarations(sort: &Sort, seen: &mut HashSet<String>, out: &mut String) {
    if let Some(array) = sort.array_sort() {
        declarations(&array.element_sort, seen, out);
    }
    if let Some(dt) = sort.datatype_sort()
        && seen.insert(dt.name.to_string())
    {
        for ctor in &dt.constructors {
            for field in &ctor.fields {
                declarations(&field.sort, seen, out);
            }
        }
        out.push_str(&ay_bindings::Constraint::declare_datatype(dt.clone()).to_string());
        out.push('\n');
    }
}

fn assert_formula(formula: Expr, expected: bool, sort: Option<&Sort>) {
    let mut defs = String::new();
    if let Some(sort) = sort {
        declarations(sort, &mut HashSet::new(), &mut defs);
    }
    for (formula, expected) in [(formula.clone(), expected), (formula.not(), !expected)] {
        let commands = ay_frontend::parse(&format!(
            "(set-logic ALL)\n{defs}(assert {formula})\n(check-sat)\n"
        ))
        .unwrap();
        let mut solver = ay_dpll::Executor::new();
        solver.set_timeout(Some(std::time::Duration::from_secs(5)));
        let output = solver.execute_all(&commands).unwrap();
        let wanted = if expected { "sat" } else { "unsat" };
        assert!(output.iter().any(|line| line.trim() == wanted), "{wanted}: {output:?}");
    }
}

fn bounds_equal(bounds: Bounds, lower: u64, upper: u64) -> Expr {
    bounds.lower.eq(bv(lower)).and(bounds.upper.eq(bv(upper)))
}

#[test]
fn chars_lower_bound_matches_native_div_ceil_without_usize_overflow() {
    for bytes in [0, 1, 2, 3, 4, 5, 6, 7, u64::MAX] {
        assert_formula(bounds_equal(chars_bounds(bv(bytes)), bytes.div_ceil(4), bytes), true, None);
    }
    assert_formula(bounds_equal(chars_bounds(bv(3)), 3, 3), false, None);
    assert_formula(bounds_equal(chars_bounds(bv(2)), 2, 2), false, None);
}

#[test]
fn native_unicode_hint_uses_remaining_bytes_after_each_scalar() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let body = find_instance_by_suffix(ctx.tcx, "chars_type").body().unwrap();
        let chc = ChcCtx::new(ctx.tcx, &body, "chars_type", ChcConfig::default());
        let ty = body.locals()[0].ty;
        let sort = ChcCtx::translate_ty(ty).unwrap();
        for text in ["", "abc", "é", "é🦀"] {
            let mut native = text.chars();
            loop {
                let pos = (text.len() - native.as_str().len()) as u64;
                let iter = value(&sort, pos, text.len() as u64, 0);
                let bounds = chc.iterator_size_hint_bounds(&iter, ty, 0).unwrap();
                let (lower, upper) = native.size_hint();
                assert_formula(
                    bounds_equal(bounds, lower as u64, upper.unwrap() as u64),
                    true,
                    Some(&sort),
                );
                assert!(chc.typed_iterator_remaining_len(&iter, ty).is_none());
                assert!(chc.try_extract_iterator_remaining_len(&iter).is_none());
                if native.next().is_none() {
                    break;
                }
            }
        }
    });
}

#[test]
fn map_preserves_bounds_while_take_limits_both_bounds() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        for (name, cases) in [
            ("map_type", vec![(0, 2, 6)]),
            ("rev_type", vec![(0, 2, 6)]),
            ("take_type", vec![(0, 0, 0), (1, 1, 1), (4, 2, 4), (9, 2, 6)]),
        ] {
            let body = find_instance_by_suffix(ctx.tcx, name).body().unwrap();
            let chc = ChcCtx::new(ctx.tcx, &body, name, ChcConfig::default());
            let ty = body.locals()[0].ty;
            let sort = ChcCtx::translate_ty(ty).unwrap();
            for (limit, lower, upper) in cases {
                let iter = value(&sort, 0, 6, limit);
                let bounds = chc.iterator_size_hint_bounds(&iter, ty, 0).unwrap();
                assert_formula(bounds_equal(bounds, lower, upper), true, Some(&sort));
                assert!(chc.try_extract_iterator_remaining_len(&iter).is_none());
                if name != "take_type" || limit != 0 {
                    assert!(chc.typed_iterator_remaining_len(&iter, ty).is_none());
                }
            }
        }
    });
}

#[test]
fn exact_transparent_wrappers_read_the_current_cursor_instead_of_a_sidecar() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        for name in ["exact_type", "copied_type", "cloned_type", "map_exact_type"] {
            let body = find_instance_by_suffix(ctx.tcx, name).body().unwrap();
            let chc = ChcCtx::new(ctx.tcx, &body, name, ChcConfig::default());
            let ty = body.locals()[0].ty;
            let sort = ChcCtx::translate_ty(ty).unwrap();
            let advanced = value(&sort, 2, 6, 0);
            let remaining = chc
                .typed_iterator_remaining_len(&advanced, ty)
                .unwrap_or_else(|| panic!("missing current cardinality for {name}: {sort:?}"));
            assert_formula(remaining.eq(bv(4)), true, Some(&sort));
            let bounds = chc.iterator_size_hint_bounds(&advanced, ty, 0).unwrap();
            assert_formula(bounds_equal(bounds, 4, 4), true, Some(&sort));
        }
    });
}

#[test]
fn exact_take_cardinality_and_zero_take_do_not_use_unknown_inner_hint() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        for name in ["take_exact_type", "take_unknown_type"] {
            let body = find_instance_by_suffix(ctx.tcx, name).body().unwrap();
            let chc = ChcCtx::new(ctx.tcx, &body, name, ChcConfig::default());
            let ty = body.locals()[0].ty;
            let sort = ChcCtx::translate_ty(ty).unwrap();
            let zero = value(&sort, 0, 6, 0);
            assert_formula(
                bounds_equal(chc.iterator_size_hint_bounds(&zero, ty, 0).unwrap(), 0, 0),
                true,
                Some(&sort),
            );
            assert_formula(
                chc.typed_iterator_remaining_len(&zero, ty).unwrap().eq(bv(0)),
                true,
                Some(&sort),
            );
            let limited = value(&sort, 2, 6, 9);
            if name == "take_unknown_type" {
                assert!(chc.iterator_size_hint_bounds(&limited, ty, 0).is_none());
                assert!(chc.typed_iterator_remaining_len(&limited, ty).is_none());
            } else {
                assert_formula(
                    bounds_equal(chc.iterator_size_hint_bounds(&limited, ty, 0).unwrap(), 4, 4),
                    true,
                    Some(&sort),
                );
                assert_formula(
                    chc.typed_iterator_remaining_len(&limited, ty).unwrap().eq(bv(4)),
                    true,
                    Some(&sort),
                );
            }
        }
    });
}

#[test]
fn preprocessing_authenticates_size_hint_and_refuses_custom_methods_and_stubs() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        for (name, accepted) in
            [("real", true), ("taken", true), ("borrowed", true), ("fake", false)]
        {
            let body = find_instance_by_suffix(ctx.tcx, name).body().unwrap();
            let chc = ChcCtx::new(ctx.tcx, &body, name, ChcConfig::default());
            let (func, def, instance) = body
                .blocks
                .iter()
                .find_map(|block| {
                    let TerminatorKind::Call { func, .. } = &block.terminator.kind else {
                        return None;
                    };
                    let TyKind::RigidTy(RigidTy::FnDef(def, args)) =
                        func.ty(body.locals()).ok()?.kind()
                    else {
                        return None;
                    };
                    use rustc_public::CrateDef;
                    if !def.name().ends_with("::size_hint") {
                        return None;
                    }
                    Some((func, def, Instance::resolve(def, &args).ok()?))
                })
                .expect("size_hint call");
            assert_eq!(is_native_iterator_size_hint(ctx.tcx, &instance), accepted, "{name}");
            assert_eq!(chc.native_iterator_size_hint_call(func), accepted, "{name}");
            assert_eq!(
                crate::kani_middle::std_abstraction::preserve_core_iterator_boundary(
                    ctx.tcx, &instance
                ),
                accepted,
                "{name}"
            );
            if accepted {
                let _stubs = crate::kani_middle::transform::UnitStubsTestScope::install(
                    HashMap::from([(def, def)]),
                );
                assert!(!is_native_iterator_size_hint(ctx.tcx, &instance));
                assert!(!chc.native_iterator_size_hint_call(func));
            }
        }
    });
}
