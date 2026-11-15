// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
use crate::codegen_ay::chc::ChcConfig;
use crate::codegen_ay::context::with_test_ay_ctx_for_source;
use crate::codegen_ay::test_fixtures::find_instance_by_suffix;
use rustc_public::mir::TerminatorKind;
use std::collections::{HashMap, HashSet};

const SOURCE: &str = r#"
    #![allow(dead_code)]
    pub fn real(source: &str) -> core::str::Chars<'_> { source.chars() }
    pub struct Fake;
    impl Fake { pub fn chars(&self) -> u8 { 7 } }
    pub fn fake(source: &Fake) -> u8 { source.chars() }
    pub fn next_type(source: &mut core::str::Chars<'_>) -> Option<char> { source.next() }
    pub fn empty_literal() -> core::str::Chars<'static> { "".chars() }
    pub fn empty_offset() -> core::str::Chars<'static> {
        const EMPTY: &str = "xé".split_at(1).1.split_at(0).0;
        EMPTY.chars()
    }
    pub fn nonempty_literal() -> core::str::Chars<'static> { "é".chars() }
    pub fn empty_bytes() -> core::slice::Iter<'static, u8> { b"".iter() }
    pub fn empty_rebound(choose: bool) -> core::str::Chars<'static> {
        let mut source = ""; let mut other = "";
        let selected = if choose { &mut source } else { &mut other };
        *selected = "é";
        source.chars()
    }
"#;

fn bv(value: u64) -> Expr {
    Expr::bitvec_const(value, POINTER_WIDTH)
}

fn select(value: &Expr, name: &str) -> Expr {
    value.clone().field_select(
        value.sort().datatype_name().unwrap(),
        name,
        field_sort(value.sort(), name).unwrap(),
    )
}

fn assert_formula_in(formula: Expr, expected: bool, declarations: &str) {
    for (formula, expected) in [(formula.clone(), expected), (formula.not(), !expected)] {
        let commands = ay_frontend::parse(&format!(
            "(set-logic ALL)\n{declarations}\n(assert {formula})\n(check-sat)\n"
        ))
        .unwrap();
        let mut solver = ay_dpll::Executor::new();
        solver.set_timeout(Some(std::time::Duration::from_secs(5)));
        let output = solver.execute_all(&commands).unwrap();
        let wanted = if expected { "sat" } else { "unsat" };
        assert!(output.iter().any(|line| line.trim() == wanted), "{wanted}: {output:?}");
    }
}

fn assert_formula(formula: Expr, expected: bool) {
    assert_formula_in(formula, expected, "");
}

fn bytes(value: &[u8]) -> Expr {
    value.iter().enumerate().fold(
        Expr::const_array(Sort::bitvec(64), Expr::bitvec_const(0u8, 8)),
        |data, (index, byte)| data.store(bv(index as u64), Expr::bitvec_const(*byte, 8)),
    )
}

#[test]
fn empty_chars_uses_typed_constant_metadata_and_preserves_its_actual_address() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        for (name, expected_empty) in [
            ("empty_literal", true),
            ("empty_offset", true),
            ("nonempty_literal", false),
            ("empty_bytes", false),
            ("empty_rebound", false),
            ("real", false),
        ] {
            let body = find_instance_by_suffix(ctx.tcx, name).body().unwrap();
            let mut chc = ChcCtx::new(ctx.tcx, &body, name, ChcConfig::default());
            chc.declare_block_relations();
            let (func, receiver) = body
                .blocks
                .iter()
                .find_map(|block| match &block.terminator.kind {
                    TerminatorKind::Call { func, args, .. } => Some((func, &args[0])),
                    _ => None,
                })
                .unwrap();
            assert_eq!(is_const_empty_str(&chc, receiver), expected_empty, "{name}");
            if !expected_empty {
                continue;
            }
            let ty = authenticated_output_ty(&chc, func, body.locals()).unwrap();
            let sort = ChcCtx::translate_ty(ty).unwrap();
            let pointer = chc.translate_operand_with_modified(receiver, &HashSet::new()).unwrap();
            let address = PtrRepr::classify(&pointer).unwrap().data().as_expr().clone();
            let (chars, valid) =
                build_chars_value(&chc, &sort, bytes(&[]), bv(0), bv(0), address.clone()).unwrap();
            let iter = select(&chars, "fld_iter");
            let storage = select(&iter, "fld_vec");
            assert_eq!(select(&storage, "fld_ptr"), address, "{name}");
            assert_eq!(select(&storage, "fld_len"), bv(0), "{name}");
            assert_eq!(select(&iter, "fld_pos"), bv(0), "{name}");
            assert_eq!(valid, Expr::bool_const(true), "{name}");
        }
    });
}

#[test]
fn next_decodes_each_utf8_width_and_rejects_invalid_sequences() {
    for text in ["x", "é", "€", "🦀", "\u{d7ff}", "\u{e000}", "\u{10ffff}"] {
        let (payload, step, valid) =
            decode_utf8_scalar(&bytes(text.as_bytes()), &bv(0), &bv(text.len() as u64)).unwrap();
        let expected = text.chars().next().unwrap() as u32;
        assert_formula(
            valid
                .and(payload.eq(Expr::bitvec_const(expected, 32)))
                .and(step.eq(bv(text.len() as u64))),
            true,
        );
    }
    for value in
        [&[0x80][..], &[0xc0, 0x80], &[0xed, 0xa0, 0x80], &[0xf4, 0x90, 0x80, 0x80], &[0xe2, 0x82]]
    {
        assert!(std::str::from_utf8(value).is_err());
        let (_, _, valid) =
            decode_utf8_scalar(&bytes(value), &bv(0), &bv(value.len() as u64)).unwrap();
        assert_formula(valid, false);
    }
}

#[test]
fn multibyte_next_returns_the_scalar_and_advances_the_same_chars_owner() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let body = find_instance_by_suffix(ctx.tcx, "real").body().unwrap();
        let chc = ChcCtx::new(ctx.tcx, &body, "real", ChcConfig::default());
        let sort = ChcCtx::translate_ty(body.locals()[0].ty).unwrap();
        let next_body = find_instance_by_suffix(ctx.tcx, "next_type").body().unwrap();
        let output = ChcCtx::translate_ty(next_body.locals()[0].ty).unwrap();
        // Production registers the return datatype before emitting the rule.
        // The standalone formula solver needs that same declaration.
        let declarations =
            ay_bindings::Constraint::declare_datatype(output.datatype_sort().unwrap().clone())
                .to_string();
        let (chars, _) =
            build_chars_value(&chc, &sort, bytes("xé🦀".as_bytes()), bv(6), bv(1), bv(4097))
                .unwrap();
        let (value, advanced, valid) = build_chars_next(&chc, chars, &output).unwrap();
        let char_value = chc.option_unwrap_value_on_some_path(value.clone()).unwrap();
        let position = select(&select(&advanced, "fld_iter"), "fld_pos");
        assert_formula_in(
            valid
                .and(chc.option_is_some(value))
                .and(char_value.eq(Expr::bitvec_const('é' as u32, 32)))
                .and(position.eq(bv(3))),
            true,
            &declarations,
        );
        let (value, advanced, valid) = build_chars_next(&chc, advanced, &output).unwrap();
        let char_value = chc.option_unwrap_value_on_some_path(value.clone()).unwrap();
        let position = select(&select(&advanced, "fld_iter"), "fld_pos");
        assert_formula_in(
            valid
                .and(chc.option_is_some(value))
                .and(char_value.eq(Expr::bitvec_const('🦀' as u32, 32)))
                .and(position.eq(bv(7))),
            true,
            &declarations,
        );
        let (value, exhausted, valid) = build_chars_next(&chc, advanced, &output).unwrap();
        assert_formula_in(
            valid
                .and(chc.option_is_some(value).not())
                .and(select(&select(&exhausted, "fld_iter"), "fld_pos").eq(bv(7))),
            true,
            &declarations,
        );
    });
}

#[test]
fn constructor_authenticates_the_real_diagnostic_item_and_refuses_stubs() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let body = find_instance_by_suffix(ctx.tcx, "real").body().unwrap();
        let chc = ChcCtx::new(ctx.tcx, &body, "real", ChcConfig::default());
        let func = body
            .blocks
            .iter()
            .find_map(|block| match &block.terminator.kind {
                TerminatorKind::Call { func, .. } => Some(func),
                _ => None,
            })
            .unwrap();
        assert!(authenticated_output_ty(&chc, func, body.locals()).is_some());
        let TyKind::RigidTy(RigidTy::FnDef(def, _)) = func.ty(body.locals()).unwrap().kind() else {
            panic!("direct constructor")
        };
        let _stubs =
            crate::kani_middle::transform::UnitStubsTestScope::install(HashMap::from([(def, def)]));
        assert!(authenticated_output_ty(&chc, func, body.locals()).is_none());
    });
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let body = find_instance_by_suffix(ctx.tcx, "fake").body().unwrap();
        let chc = ChcCtx::new(ctx.tcx, &body, "fake", ChcConfig::default());
        for block in &body.blocks {
            if let TerminatorKind::Call { func, .. } = &block.terminator.kind {
                assert!(authenticated_output_ty(&chc, func, body.locals()).is_none());
            }
        }
    });
}

#[test]
fn constructor_preserves_multibyte_substring_offsets_and_storage_identity() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let body = find_instance_by_suffix(ctx.tcx, "real").body().unwrap();
        let chc = ChcCtx::new(ctx.tcx, &body, "real", ChcConfig::default());
        let sort = ChcCtx::translate_ty(body.locals()[0].ty).unwrap();
        let data = "xé🦀!".as_bytes().iter().enumerate().fold(
            Expr::const_array(Sort::bitvec(64), Expr::bitvec_const(0u8, 8)),
            |data, (index, byte)| data.store(bv(index as u64), Expr::bitvec_const(*byte, 8)),
        );
        let (chars, valid) =
            build_chars_value(&chc, &sort, data.clone(), bv(6), bv(1), bv(4097)).unwrap();
        let iter = select(&chars, "fld_iter");
        let slice = select(&iter, "fld_vec");
        assert_eq!(select(&iter, "fld_pos"), bv(1));
        assert_eq!(select(&slice, "fld_len"), bv(7));
        assert_eq!(select(&slice, "fld_ptr"), bv(4096));
        assert_eq!(select(&slice, "fld_data"), data);
        assert_eq!(valid, Expr::bool_const(true));
    });
}

#[test]
fn constructor_keeps_symbolic_offsets_and_guards_index_overflow() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let body = find_instance_by_suffix(ctx.tcx, "real").body().unwrap();
        let chc = ChcCtx::new(ctx.tcx, &body, "real", ChcConfig::default());
        let sort = ChcCtx::translate_ty(body.locals()[0].ty).unwrap();
        let data = Expr::var("bytes", Sort::array(Sort::bitvec(64), Sort::bitvec(8)));
        let offset = Expr::var("offset", Sort::bitvec(64));
        let length = Expr::var("length", Sort::bitvec(64));
        let (chars, valid) =
            build_chars_value(&chc, &sort, data.clone(), length, offset.clone(), bv(4096)).unwrap();
        let iter = select(&chars, "fld_iter");
        assert_eq!(select(&iter, "fld_pos"), offset);
        assert_eq!(select(&select(&iter, "fld_vec"), "fld_data"), data);
        assert!(valid.to_string().contains("bvuge"));
        assert_eq!(
            build_chars_value(&chc, &sort, data, bv(2), bv(u64::MAX), bv(0)).unwrap().1,
            Expr::bool_const(false)
        );
    });
}
