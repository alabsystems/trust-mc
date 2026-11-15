// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
use crate::callee_body::CalleeBody;
use crate::codegen_ay::chc::ChcConfig;
use crate::codegen_ay::context::with_test_ay_ctx_for_source;
use crate::codegen_ay::test_fixtures::find_instance_by_suffix;
use rustc_public::mir::{Rvalue, StatementKind};

const SOURCE: &str = r#"
    pub fn scalar(x: u8) -> (u8,) { (x,) }
    pub fn wide(x: u128) -> (u128,) { (x,) }
    pub fn address(x: &u8) -> (&u8,) { (x,) }
    pub fn address_word(x: &u64) -> (&u64,) { (x,) }
    pub fn referent(x: &u32) -> (&u32,) { (x,) }
    pub struct Pair(pub u8, pub u16);
    pub fn aggregate(x: Pair) -> (Pair,) { (x,) }
"#;

#[test]
fn singleton_tuple_preserves_scalar_address_and_datatype_payloads() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        for name in ["scalar", "wide", "address", "aggregate"] {
            let body = find_instance_by_suffix(ctx.tcx, name).callee_body().unwrap();
            let mut chc = ChcCtx::new(ctx.tcx, &body, name, ChcConfig::default());
            let (place, kind, operands) = body
                .blocks
                .iter()
                .flat_map(|block| &block.statements)
                .find_map(|statement| match &statement.kind {
                    StatementKind::Assign(place, Rvalue::Aggregate(kind, operands))
                        if matches!(kind, AggregateKind::Tuple) =>
                    {
                        Some((place, kind, operands))
                    }
                    _ => None,
                })
                .expect("fixture must retain the singleton tuple aggregate");
            assert_eq!(operands.len(), 1);
            let sort = ChcCtx::translate_ty(body.locals()[1].ty).unwrap();
            let payload = if let Some(width) = sort.bitvec_width() {
                Expr::bitvec_const(7u64, width)
            } else {
                let dt = sort.datatype_sort().unwrap();
                let constructor = &dt.constructors[0];
                let fields = constructor
                    .fields
                    .iter()
                    .enumerate()
                    .map(|(index, field)| {
                        Expr::bitvec_const(index as u64 + 1, field.sort.bitvec_width().unwrap())
                    })
                    .collect();
                Expr::datatype_constructor(&dt.name, &constructor.name, fields, sort.clone())
            };
            let locals = HashMap::from([(1, payload.clone())]);
            let fields = HashMap::new();
            let translated = chc.with_inline_walk_frame(&body, |chc| {
                if name == "address" {
                    chc.tag_inline_walk_address_local(1);
                }
                let expected = inline_aggregate_to_expr(
                    chc,
                    kind,
                    operands,
                    &locals,
                    &PlaceResolver::FieldMap(&fields),
                    body.locals(),
                    Some(place.local),
                );
                let production = super::super::inline_shared::inline_rvalue_to_expr(
                    chc,
                    &Rvalue::Aggregate(kind.clone(), operands.clone()),
                    &locals,
                    &PlaceResolver::FieldMap(&fields),
                    body.locals(),
                    Some(place.local),
                );
                assert_eq!(production, expected, "production tuple dispatch: {name}");
                production
            });
            assert_eq!(translated, Some(payload), "{name} must keep its payload exactly");
        }
    });
}

#[test]
fn singleton_reference_tuple_refuses_an_element_value_in_place_of_its_address() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let body = find_instance_by_suffix(ctx.tcx, "address").callee_body().unwrap();
        let mut chc = ChcCtx::new(ctx.tcx, &body, "address", ChcConfig::default());
        let (place, kind, operands) = body
            .blocks
            .iter()
            .flat_map(|block| &block.statements)
            .find_map(|statement| match &statement.kind {
                StatementKind::Assign(place, Rvalue::Aggregate(kind, operands))
                    if matches!(kind, AggregateKind::Tuple) =>
                {
                    Some((place, kind, operands))
                }
                _ => None,
            })
            .unwrap();
        let locals = HashMap::from([(1, Expr::bitvec_const(7u8, 8))]);
        let fields = HashMap::new();
        assert!(
            inline_aggregate_to_expr(
                &mut chc,
                kind,
                operands,
                &locals,
                &PlaceResolver::FieldMap(&fields),
                body.locals(),
                Some(place.local),
            )
            .is_none(),
            "a native reference is not the zero-extended byte stored at it"
        );
    });
}

#[test]
fn singleton_reference_tuple_refuses_matching_width_without_address_identity() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let body = find_instance_by_suffix(ctx.tcx, "address_word").callee_body().unwrap();
        let mut chc = ChcCtx::new(ctx.tcx, &body, "address_word", ChcConfig::default());
        let (place, kind, operands) = body
            .blocks
            .iter()
            .flat_map(|block| &block.statements)
            .find_map(|statement| match &statement.kind {
                StatementKind::Assign(place, Rvalue::Aggregate(kind, operands))
                    if matches!(kind, AggregateKind::Tuple) =>
                {
                    Some((place, kind, operands))
                }
                _ => None,
            })
            .unwrap();
        let locals = HashMap::from([(1, Expr::bitvec_const(7u64, 64))]);
        let fields = HashMap::new();
        chc.with_inline_walk_frame(&body, |chc| {
            assert!(
                inline_aggregate_to_expr(
                    chc,
                    kind,
                    operands,
                    &locals,
                    &PlaceResolver::FieldMap(&fields),
                    body.locals(),
                    Some(place.local)
                )
                .is_none()
            );
            assert!(
                super::super::inline_shared::inline_rvalue_to_expr(
                    chc,
                    &Rvalue::Aggregate(kind.clone(), operands.clone()),
                    &locals,
                    &PlaceResolver::FieldMap(&fields),
                    body.locals(),
                    Some(place.local),
                )
                .is_none(),
                "production fallback must retain the tuple refusal"
            );
            chc.tag_inline_walk_referent_local(1);
            assert!(
                super::super::inline_shared::inline_rvalue_to_expr(
                    chc,
                    &Rvalue::Aggregate(kind.clone(), operands.clone()),
                    &locals,
                    &PlaceResolver::FieldMap(&fields),
                    body.locals(),
                    Some(place.local),
                )
                .is_none(),
                "pointer-shaped logical values need richer Fn carrier provenance"
            );
            chc.tag_inline_walk_address_local(1);
            assert_eq!(
                inline_aggregate_to_expr(
                    chc,
                    kind,
                    operands,
                    &locals,
                    &PlaceResolver::FieldMap(&fields),
                    body.locals(),
                    Some(place.local)
                ),
                Some(Expr::bitvec_const(7u64, 64))
            );
        });
    });
}

#[test]
fn singleton_logical_referent_requires_positive_current_frame_authority() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let body = find_instance_by_suffix(ctx.tcx, "referent").callee_body().unwrap();
        let mut chc = ChcCtx::new(ctx.tcx, &body, "referent", ChcConfig::default());
        let (destination, rvalue) = body
            .blocks
            .iter()
            .flat_map(|block| &block.statements)
            .find_map(|statement| match &statement.kind {
                StatementKind::Assign(
                    place,
                    value @ Rvalue::Aggregate(AggregateKind::Tuple, _),
                ) => Some((place.local, value)),
                _ => None,
            })
            .unwrap();
        let value = Expr::bitvec_const(7u32, 32);
        let locals = HashMap::from([(1, value.clone())]);
        let fields = HashMap::new();
        let translate = |chc: &mut ChcCtx<'_, '_>| {
            super::super::inline_shared::inline_rvalue_to_expr(
                chc,
                rvalue,
                &locals,
                &PlaceResolver::FieldMap(&fields),
                body.locals(),
                Some(destination),
            )
        };
        chc.with_inline_walk_frame(&body, |chc| {
            assert!(translate(chc).is_none(), "absence of an address tag is insufficient");
            chc.tag_inline_walk_referent_local(1);
            assert_eq!(translate(chc), Some(value.clone()));
            chc.with_inline_walk_frame(&body, |chc| {
                assert!(
                    translate(chc).is_none(),
                    "a nested body's local1 has no inherited authority"
                );
            });
            assert_eq!(translate(chc), Some(value.clone()));
            chc.forget_inline_walk_referent_local(1);
            chc.tag_inline_walk_referent_local(1);
            assert!(translate(chc).is_none(), "an uncertain arm/write dominates later marks");
        });
    });
}
