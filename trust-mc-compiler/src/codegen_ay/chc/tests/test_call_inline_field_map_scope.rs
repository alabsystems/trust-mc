// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Regression tests for inline receiver field-map scope.
//!
//! Part of #4138 / #4132: only the receiver parameter should seed the
//! memory-backed inline field map.

#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use crate::codegen_ay::chc::call::inline_field_map::{DIRECT_DEREF_FIELD, build_self_field_map};
use crate::codegen_ay::chc::call::inline_shared::field_map_projection::{
    resolve_projected_place, try_extract_dt_field_without_accessor,
};
use ay_bindings::{Expr, Sort};
use rustc_public::mir::{Operand, ProjectionElem, Rvalue, StatementKind};
use rustc_public::ty::{RigidTy, TyKind};
use std::collections::HashMap;

const FIELD_MAP_SCOPE_SOURCE: &str = r#"
    #![allow(dead_code)]

    struct Pair {
        left: u8,
        right: u8,
    }

    impl Pair {
        fn sum_with(&self, other: &Pair) -> u8 {
            self.left + other.right
        }
    }
"#;

const ENUM_FIELD_MAP_SOURCE: &str = r#"
    #![allow(dead_code)]

    enum MaybeByte {
        Some(u8),
        None,
    }

    struct Holder {
        value: MaybeByte,
    }

    impl Holder {
        fn payload_or_zero(&self) -> u8 {
            match self.value {
                MaybeByte::Some(v) => v,
                MaybeByte::None => 0,
            }
        }
    }
"#;

const TWO_PAYLOAD_ENUM_FIELD_MAP_SOURCE: &str = r#"
    #![allow(dead_code)]

    enum EitherByte {
        Left(u8),
        Right(u8),
    }

    struct Holder {
        value: EitherByte,
    }

    impl Holder {
        fn payload(&self) -> u8 {
            match self.value {
                EitherByte::Left(v) | EitherByte::Right(v) => v,
            }
        }
    }
"#;

const FIELD_DEREF_CHAIN_SOURCE: &str = r#"
    #![allow(dead_code)]

    #[derive(Clone, Copy)]
    struct Inner {
        value: u8,
    }

    struct Holder<'a>(&'a Inner);

    impl Holder<'_> {
        fn copy_inner(&self) -> Inner {
            *self.0
        }
    }
"#;

fn find_receiver_field_place(body: &rustc_public::mir::Body) -> Place {
    body.blocks
        .iter()
        .find_map(|block| {
            block.statements.iter().find_map(|stmt| {
                let StatementKind::Assign(_, rvalue) = &stmt.kind else {
                    return None;
                };
                let place = match rvalue {
                    Rvalue::Use(Operand::Copy(place) | Operand::Move(place)) => place,
                    _ => return None,
                };
                let is_receiver_field = place.local == 1
                    && matches!(place.projection.first(), Some(ProjectionElem::Deref))
                    && place
                        .projection
                        .iter()
                        .any(|proj| matches!(proj, ProjectionElem::Field(0, _)));
                is_receiver_field.then(|| place.clone())
            })
        })
        .expect("sum_with MIR should contain a `(*self).left` field projection")
}

fn find_receiver_enum_payload_place(body: &rustc_public::mir::Body) -> Place {
    body.blocks
        .iter()
        .find_map(|block| {
            block.statements.iter().find_map(|stmt| {
                let StatementKind::Assign(_, rvalue) = &stmt.kind else {
                    return None;
                };
                let place = match rvalue {
                    Rvalue::Use(Operand::Copy(place) | Operand::Move(place)) => place,
                    _ => return None,
                };
                let is_enum_payload = place.local == 1
                    && matches!(place.projection.first(), Some(ProjectionElem::Deref))
                    && matches!(place.projection.get(1), Some(ProjectionElem::Field(0, _)))
                    && place
                        .projection
                        .iter()
                        .any(|proj| matches!(proj, ProjectionElem::Downcast(_)))
                    && matches!(place.projection.last(), Some(ProjectionElem::Field(0, _)));
                is_enum_payload.then(|| place.clone())
            })
        })
        .expect(
            "payload_or_zero MIR should contain a `(*self).value as Some).0` payload projection",
        )
}

fn build_receiver_field_deref_place(body: &rustc_public::mir::Body) -> Place {
    let receiver_ty = body.locals()[1].ty;
    let field_ty = match receiver_ty.kind() {
        TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => match inner.kind() {
            TyKind::RigidTy(RigidTy::Adt(def, args)) => {
                def.variants()[0].fields()[0].ty_with_args(&args)
            }
            other => panic!("expected receiver pointee ADT, got {other:?}"),
        },
        other => panic!("expected receiver ref type, got {other:?}"),
    };

    Place {
        local: 1,
        projection: vec![
            ProjectionElem::Deref,
            ProjectionElem::Field(0, field_ty),
            ProjectionElem::Deref,
        ],
    }
}

fn without_downcast(place: &Place) -> Place {
    Place {
        local: place.local,
        projection: place
            .projection
            .iter()
            .filter(|proj| !matches!(proj, ProjectionElem::Downcast(_)))
            .cloned()
            .collect(),
    }
}

#[test]
fn test_build_self_field_map_only_populates_receiver_param() {
    with_test_ay_ctx_for_source(FIELD_MAP_SCOPE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "sum_with");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "sum_with", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let params = vec![
            Expr::var("self_ptr", Sort::bitvec(crate::codegen_ay::types::POINTER_WIDTH)),
            Expr::var("other_ptr", Sort::bitvec(crate::codegen_ay::types::POINTER_WIDTH)),
        ];
        let field_map = build_self_field_map(&mut chc_ctx, &body, &params);

        assert!(
            field_map.contains_key(&(1, 0)),
            "receiver field map should include self.left for local _1"
        );
        assert!(
            field_map.keys().all(|(local, _)| *local == 1),
            "build_self_field_map must stay scoped to the receiver param; got keys {:?}",
            field_map.keys().collect::<Vec<_>>()
        );
    });
}

#[test]
fn test_resolve_projected_place_prefers_receiver_field_map_entry() {
    with_test_ay_ctx_for_source(FIELD_MAP_SCOPE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "sum_with");
        let body = instance.body().expect("function body");
        let place = find_receiver_field_place(&body);
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "sum_with", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let expected = Expr::var("self_left", Sort::bitvec(8));
        let local_exprs = HashMap::from([(
            place.local,
            Expr::var("self_ptr", Sort::bitvec(crate::codegen_ay::types::POINTER_WIDTH)),
        )]);
        let self_field_map = HashMap::from([((place.local, 0usize), expected.clone())]);

        let resolved = resolve_projected_place(
            &mut chc_ctx,
            &local_exprs,
            &place,
            &self_field_map,
            body.locals(),
        )
        .expect("receiver field projection should resolve through the self field map");

        assert_eq!(
            resolved, expected,
            "resolve_projected_place should use the cached receiver field entry for `(*self).left`"
        );
    });
}

#[test]
fn test_resolve_projected_place_ignores_direct_deref_entry_mid_field() {
    with_test_ay_ctx_for_source(FIELD_MAP_SCOPE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "sum_with");
        let body = instance.body().expect("function body");
        let place = find_receiver_field_place(&body);
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "sum_with", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let pair_sort =
            struct_sort("Pair", [("fld_left", Sort::bitvec(8)), ("fld_right", Sort::bitvec(8))]);
        let base_pair = Expr::var("base_pair", pair_sort.clone());
        let conflicting_whole_object = Expr::var("wrong_pair", pair_sort.clone());
        let expected = base_pair.clone().field_select("Pair", "fld_left", Sort::bitvec(8));
        let wrong =
            conflicting_whole_object.clone().field_select("Pair", "fld_left", Sort::bitvec(8));

        let local_exprs = HashMap::from([(place.local, base_pair)]);
        let self_field_map =
            HashMap::from([((place.local, DIRECT_DEREF_FIELD), conflicting_whole_object)]);

        let resolved = resolve_projected_place(
            &mut chc_ctx,
            &local_exprs,
            &place,
            &self_field_map,
            body.locals(),
        )
        .expect("receiver field projection should keep using the base Pair expression");

        assert_eq!(
            resolved, expected,
            "resolve_projected_place must ignore DIRECT_DEREF_FIELD while walking `(*self).left`"
        );
        assert_ne!(
            resolved, wrong,
            "mid-field projection must not select from the conflicting whole-object deref entry"
        );
    });
}

#[test]
fn test_resolve_projected_place_ignores_direct_deref_entry_after_field_chain() {
    with_test_ay_ctx_for_source(FIELD_DEREF_CHAIN_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "copy_inner");
        let body = instance.body().expect("function body");
        let place = build_receiver_field_deref_place(&body);
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "copy_inner", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let inner_sort = struct_sort("Inner", [("fld_value", Sort::bitvec(8))]);
        let holder_sort = struct_sort("Holder", [("fld_0", inner_sort.clone())]);
        let updated_inner = Expr::datatype_constructor(
            "Inner",
            "Inner_mk",
            vec![Expr::var("updated_value", Sort::bitvec(8))],
            inner_sort.clone(),
        );
        let stale_inner = Expr::datatype_constructor(
            "Inner",
            "Inner_mk",
            vec![Expr::var("stale_value", Sort::bitvec(8))],
            inner_sort,
        );
        let updated_holder = Expr::datatype_constructor(
            "Holder",
            "Holder_mk",
            vec![updated_inner.clone()],
            holder_sort,
        );

        let local_exprs = HashMap::from([(place.local, updated_holder)]);
        let self_field_map =
            HashMap::from([((place.local, DIRECT_DEREF_FIELD), stale_inner.clone())]);

        let resolved = resolve_projected_place(
            &mut chc_ctx,
            &local_exprs,
            &place,
            &self_field_map,
            body.locals(),
        )
        .expect("receiver field deref should keep using the projected field value");

        assert_eq!(
            resolved, updated_inner,
            "resolve_projected_place must preserve the field-selected value for `*self.0`"
        );
        assert_ne!(
            resolved, stale_inner,
            "field-chain deref must not fall back to the stale whole-object DIRECT_DEREF_FIELD entry"
        );
    });
}

// --- try_extract_dt_field_without_accessor tests (Part of #4138) ---

#[test]
fn test_extract_dt_field_from_bare_constructor() {
    let pair_sort =
        struct_sort("Pair", [("fld_left", Sort::bitvec(8)), ("fld_right", Sort::bitvec(8))]);
    let left = Expr::var("left_val", Sort::bitvec(8));
    let right = Expr::var("right_val", Sort::bitvec(8));
    let ctor =
        Expr::datatype_constructor("Pair", "Pair", vec![left.clone(), right.clone()], pair_sort);

    assert_eq!(
        try_extract_dt_field_without_accessor(&ctor, 0),
        Some(left),
        "field_idx 0 should extract the first constructor arg"
    );
    assert_eq!(
        try_extract_dt_field_without_accessor(&ctor, 1),
        Some(right),
        "field_idx 1 should extract the second constructor arg"
    );
    assert_eq!(
        try_extract_dt_field_without_accessor(&ctor, 2),
        None,
        "out-of-range field_idx should return None"
    );
}

#[test]
fn test_extract_dt_field_from_ite_both_constructors() {
    let option_sort = enum_sort(
        "OptionU8",
        [("Some_OptionU8", vec![("fld_0", Sort::bitvec(8))]), ("None_OptionU8", vec![])],
    );
    let val_a = Expr::var("a", Sort::bitvec(8));
    let val_b = Expr::var("b", Sort::bitvec(8));
    let some_a = Expr::datatype_constructor(
        "OptionU8",
        "Some_OptionU8",
        vec![val_a.clone()],
        option_sort.clone(),
    );
    let some_b = Expr::datatype_constructor(
        "OptionU8",
        "Some_OptionU8",
        vec![val_b.clone()],
        option_sort.clone(),
    );
    let cond = Expr::var("flag", Sort::bool());
    let ite_expr = Expr::ite(cond.clone(), some_a, some_b);

    let extracted = try_extract_dt_field_without_accessor(&ite_expr, 0)
        .expect("ite with both Some branches should extract field 0");

    // Result should be ite(flag, a, b)
    let expected = Expr::ite(cond, val_a, val_b);
    assert_eq!(extracted, expected, "should reconstruct ite over extracted fields");
}

#[test]
fn test_extract_dt_field_from_ite_one_nullary_branch() {
    let option_sort = enum_sort(
        "OptionU8",
        [("Some_OptionU8", vec![("fld_0", Sort::bitvec(8))]), ("None_OptionU8", vec![])],
    );
    let payload = Expr::var("payload", Sort::bitvec(8));
    let some_val = Expr::datatype_constructor(
        "OptionU8",
        "Some_OptionU8",
        vec![payload.clone()],
        option_sort.clone(),
    );
    let none_val =
        Expr::datatype_constructor("OptionU8", "None_OptionU8", vec![], option_sort.clone());
    let cond = Expr::var("is_some", Sort::bool());
    let ite_expr = Expr::ite(cond, some_val, none_val);

    let extracted = try_extract_dt_field_without_accessor(&ite_expr, 0)
        .expect("ite with one nullary branch should return the payload branch");

    assert_eq!(
        extracted, payload,
        "nullary branch falls through; payload branch returned directly"
    );
}

#[test]
fn test_extract_dt_field_from_symbolic_returns_none() {
    let pair_sort =
        struct_sort("Pair", [("fld_left", Sort::bitvec(8)), ("fld_right", Sort::bitvec(8))]);
    let symbolic = Expr::var("unknown_pair", pair_sort);

    assert_eq!(
        try_extract_dt_field_without_accessor(&symbolic, 0),
        None,
        "symbolic (non-constructor) expressions should return None"
    );
}

#[test]
fn test_resolve_projected_place_extracts_enum_payload_without_accessor_when_downcast_missing() {
    with_test_ay_ctx_for_source(ENUM_FIELD_MAP_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "payload_or_zero");
        let body = instance.body().expect("function body");
        let mir_payload_place = find_receiver_enum_payload_place(&body);
        let place = without_downcast(&mir_payload_place);
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "payload_or_zero", ChcConfig::default());
        chc_ctx.declare_block_relations();

        assert!(
            !place.projection.iter().any(|proj| matches!(proj, ProjectionElem::Downcast(_))),
            "test precondition: the synthetic place must exercise the no-Downcast path"
        );

        let maybe_byte_sort = enum_sort(
            "MaybeByte",
            [("Some_MaybeByte", vec![("fld_0", Sort::bitvec(8))]), ("None_MaybeByte", vec![])],
        );
        let payload = Expr::var("payload", Sort::bitvec(8));
        let some_value = Expr::datatype_constructor(
            "MaybeByte",
            "Some_MaybeByte",
            vec![payload.clone()],
            maybe_byte_sort.clone(),
        );
        let none_value =
            Expr::datatype_constructor("MaybeByte", "None_MaybeByte", vec![], maybe_byte_sort);
        let reconstructed = Expr::ite(Expr::var("is_some", Sort::bool()), some_value, none_value);

        let local_exprs = HashMap::from([(
            place.local,
            Expr::var("self_ptr", Sort::bitvec(crate::codegen_ay::types::POINTER_WIDTH)),
        )]);
        let self_field_map = HashMap::from([((place.local, 0usize), reconstructed)]);

        let resolved = resolve_projected_place(
            &mut chc_ctx,
            &local_exprs,
            &place,
            &self_field_map,
            body.locals(),
        )
        .expect("projection should recover payload from reconstructed enum without a DT accessor");

        assert_eq!(
            resolved, payload,
            "resolve_projected_place should recover the Some payload directly when Downcast metadata is absent"
        );
    });
}

#[test]
fn test_resolve_projected_place_rebuilds_payload_ite_when_both_variants_have_fields() {
    with_test_ay_ctx_for_source(TWO_PAYLOAD_ENUM_FIELD_MAP_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "payload");
        let body = instance.body().expect("function body");
        let mir_payload_place = find_receiver_enum_payload_place(&body);
        let place = without_downcast(&mir_payload_place);
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "payload", ChcConfig::default());
        chc_ctx.declare_block_relations();

        assert!(
            !place.projection.iter().any(|proj| matches!(proj, ProjectionElem::Downcast(_))),
            "test precondition: the synthetic place must exercise the no-Downcast path"
        );

        let either_byte_sort = enum_sort(
            "EitherByte",
            [
                ("Left_EitherByte", vec![("fld_0", Sort::bitvec(8))]),
                ("Right_EitherByte", vec![("fld_0", Sort::bitvec(8))]),
            ],
        );
        let left_payload = Expr::var("left_payload", Sort::bitvec(8));
        let right_payload = Expr::var("right_payload", Sort::bitvec(8));
        let left_value = Expr::datatype_constructor(
            "EitherByte",
            "Left_EitherByte",
            vec![left_payload.clone()],
            either_byte_sort.clone(),
        );
        let right_value = Expr::datatype_constructor(
            "EitherByte",
            "Right_EitherByte",
            vec![right_payload.clone()],
            either_byte_sort,
        );
        let cond = Expr::var("is_left", Sort::bool());
        let reconstructed = Expr::ite(cond.clone(), left_value, right_value);

        let local_exprs = HashMap::from([(
            place.local,
            Expr::var("self_ptr", Sort::bitvec(crate::codegen_ay::types::POINTER_WIDTH)),
        )]);
        let self_field_map = HashMap::from([((place.local, 0usize), reconstructed)]);

        let resolved = resolve_projected_place(
            &mut chc_ctx,
            &local_exprs,
            &place,
            &self_field_map,
            body.locals(),
        )
        .expect("projection should recover both payload branches without a DT accessor");

        assert_eq!(
            resolved,
            Expr::ite(cond, left_payload, right_payload),
            "resolve_projected_place should rebuild ite(payload_left, payload_right) when both enum variants carry fields"
        );
    });
}
