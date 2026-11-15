// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Enums whose discriminant VALUES are not their variant indices, and enums
//! whose payload variant comes first (review of fix/chc-lost-writes, lostwrite
//! track round 3).
//!
//! A MIR `SwitchInt` on `Discriminant(_)` compares against discriminant values
//! (`#[repr(u8)] enum PF { Val(u8) = 7, Nothing = 2 }` switches on 7 and 2).
//! The Option-like and two-payload discriminant paths returned the variant
//! INDEX, so neither arm matched and the `otherwise -> unreachable` edge was
//! certified on a safe program; a constant's direct tag was read as the index
//! too. Each test here fails on the index convention.

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use crate::codegen_ay::types::POINTER_WIDTH;

const EXPLICIT_DISCR_SOURCE: &str = r#"
    #![allow(dead_code)]

    #[derive(Clone, Copy)]
    #[repr(u8)]
    pub enum PF { Val(u8) = 7, Nothing = 2 }

    #[derive(Clone, Copy)]
    #[repr(u8)]
    pub enum PL { Nothing = 2, Val(u8) = 7 }

    #[derive(Clone, Copy)]
    #[repr(u8)]
    pub enum TwoP { A(u8) = 5, B(u16) = 9 }

    #[derive(Clone, Copy)]
    #[repr(u8)]
    pub enum Perm { A(u8) = 1, B = 0 }

    const CA: Perm = Perm::A(5);

    fn mk_pf(c: bool) -> PF { if c { PF::Val(3) } else { PF::Nothing } }
    fn mk_pl(c: bool) -> PL { if c { PL::Val(3) } else { PL::Nothing } }
    fn mk_twop(c: bool) -> TwoP { if c { TwoP::A(3) } else { TwoP::B(4) } }

    pub fn probe_pf_tuple(c: bool) -> u8 {
        let d = (mk_pf(c), 1u8);
        match d.0 { PF::Val(w) => w, PF::Nothing => 0 }
    }

    pub fn probe_pl_tuple(c: bool) -> u8 {
        let d = (mk_pl(c), 1u8);
        match d.0 { PL::Val(w) => w, PL::Nothing => 0 }
    }

    pub fn probe_twop_tuple(c: bool) -> u8 {
        let d = (mk_twop(c), 1u8);
        match d.0 { TwoP::A(w) => w, TwoP::B(_) => 0 }
    }

    pub fn probe_pf_local(c: bool) -> u8 {
        let d = mk_pf(c);
        match d { PF::Val(w) => w, PF::Nothing => 0 }
    }

    pub fn probe_perm_const_ref() -> u8 {
        let r: &Perm = &CA;
        match *r { Perm::A(x) => x, Perm::B => 0 }
    }

    pub fn probe_option_u8(c: bool) -> u8 {
        let o = if c { Some(3u8) } else { None };
        match o { Some(w) => w, None => 0 }
    }
"#;

/// The local of `body` whose type is the ADT named `name`.
fn adt_local_ty(body: &rustc_public::mir::Body, name: &str) -> rustc_public::ty::Ty {
    body.locals()
        .iter()
        .map(|decl| decl.ty)
        .find(|ty| {
            matches!(ty.kind(), TyKind::RigidTy(RigidTy::Adt(def, _)) if def.trimmed_name() == name)
        })
        .unwrap_or_else(|| panic!("expected a local of type {name}"))
}

/// The `Discriminant(place)` rvalue of `body` whose place projects a field.
fn field_discriminant_place(body: &rustc_public::mir::Body) -> Place {
    body.blocks
        .iter()
        .flat_map(|block| block.statements.iter())
        .find_map(|stmt| match &stmt.kind {
            rustc_public::mir::StatementKind::Assign(_, rustc_public::mir::Rvalue::Discriminant(p))
                if !p.projection.is_empty() =>
            {
                Some(p.clone())
            }
            _ => None,
        })
        .expect("expected a Discriminant of a projected place")
}

fn bv_const_value(expr: &Expr) -> Option<u128> {
    match expr.value() {
        ExprValue::BitVecConst { value, width } if *width == POINTER_WIDTH => {
            value.to_string().parse::<u128>().ok()
        }
        _ => None,
    }
}

/// The two constant branches of `ite(_, a, b)`.
fn ite_branches(expr: &Expr) -> (u128, u128) {
    let ExprValue::Ite { then_expr, else_expr, .. } = expr.value() else {
        panic!("expected an ite over two discriminant constants, got {expr}");
    };
    (
        bv_const_value(then_expr).unwrap_or_else(|| panic!("then branch not a constant: {expr}")),
        bv_const_value(else_expr).unwrap_or_else(|| panic!("else branch not a constant: {expr}")),
    )
}

/// A literal constructor of `sort`'s datatype, its payload (if any) `payload`.
fn ctor_literal(sort: &ay_bindings::Sort, payload_ctor: bool, payload: u64) -> Expr {
    let dt = sort.datatype_sort().expect("an enum datatype sort");
    let ctor = dt
        .constructors
        .iter()
        .find(|c| c.fields.is_empty() != payload_ctor)
        .expect("a constructor of the requested arity");
    let fields = ctor
        .fields
        .iter()
        .map(|f| Expr::bitvec_const(payload, f.sort.bitvec_width().expect("bitvec payload")))
        .collect();
    Expr::datatype_constructor(dt.name.clone(), ctor.name.clone(), fields, sort.clone())
}

/// An Option-like enum's discriminant is its variants' discriminant VALUES:
/// `PF::Val(_)` is 7 and `PF::Nothing` is 2, for a literal constructor and for
/// a symbolic value alike. The index convention gave 0 and 1, which match no
/// arm of `match d.0`.
#[test]
fn test_option_like_discriminant_is_the_discriminant_value() {
    with_test_ay_ctx_for_source(EXPLICIT_DISCR_SOURCE, |ctx| {
        for (probe, name, payload_value, empty_value) in
            [("probe_pf_tuple", "PF", 7u128, 2u128), ("probe_pl_tuple", "PL", 7, 2)]
        {
            let instance = find_instance_by_suffix(ctx.tcx, probe);
            let body = instance.body().expect("function body");
            let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, probe, ChcConfig::default());
            chc_ctx.declare_block_relations();
            let ty = adt_local_ty(&body, name);
            let sort = ChcCtx::translate_ty(ty).expect("enum sort");
            let place = field_discriminant_place(&body);

            let val = chc_ctx
                .translate_adt_discriminant(&place, ty, ctor_literal(&sort, true, 3))
                .expect("payload literal discriminant");
            assert_eq!(bv_const_value(&val), Some(payload_value), "{name}::Val(3) gave {val}");
            let empty = chc_ctx
                .translate_adt_discriminant(&place, ty, ctor_literal(&sort, false, 0))
                .expect("empty literal discriminant");
            assert_eq!(bv_const_value(&empty), Some(empty_value), "{name}::Nothing gave {empty}");

            let symbolic = Expr::var("probe_enum_value", sort.clone());
            let sym = chc_ctx
                .translate_adt_discriminant(&place, ty, symbolic)
                .expect("symbolic discriminant");
            assert_eq!(ite_branches(&sym), (payload_value, empty_value), "{name}: {sym}");
        }
    });
}

/// A two-variant enum with both payloads maps its variants to 5 and 9.
#[test]
fn test_two_payload_discriminant_is_the_discriminant_value() {
    with_test_ay_ctx_for_source(EXPLICIT_DISCR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_twop_tuple");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_twop_tuple", ChcConfig::default());
        chc_ctx.declare_block_relations();
        let ty = adt_local_ty(&body, "TwoP");
        let sort = ChcCtx::translate_ty(ty).expect("enum sort");
        let place = field_discriminant_place(&body);
        let sym = chc_ctx
            .translate_adt_discriminant(&place, ty, Expr::var("probe_twop_value", sort))
            .expect("symbolic discriminant");
        assert_eq!(ite_branches(&sym), (5, 9), "TwoP: {sym}");
    });
}

/// An Option-like ADT's datatype lists its constructors in VARIANT order
/// (`option_like_constructors`, lostwrite round 2): `PF`'s payload variant is
/// variant 0, `PL`'s is variant 1, and core `Option` keeps its shared
/// `None`-first order (its `None` is variant 0).
#[test]
fn test_option_like_constructors_follow_variant_order() {
    with_test_ay_ctx_for_source(EXPLICIT_DISCR_SOURCE, |ctx| {
        let pf_body = find_instance_by_suffix(ctx.tcx, "probe_pf_tuple").body().unwrap();
        let pl_body = find_instance_by_suffix(ctx.tcx, "probe_pl_tuple").body().unwrap();
        let opt_body = find_instance_by_suffix(ctx.tcx, "probe_option_u8").body().unwrap();
        for (body, name, payload_first) in
            [(&pf_body, "PF", true), (&pl_body, "PL", false), (&opt_body, "Option", false)]
        {
            let sort = ChcCtx::translate_ty(adt_local_ty(body, name)).expect("enum sort");
            let dt = sort.datatype_sort().expect("datatype");
            assert_eq!(dt.constructors.len(), 2, "{name}: {dt:?}");
            assert_eq!(
                !dt.constructors[0].fields.is_empty(),
                payload_first,
                "{name}: constructor 0 must be variant 0, got {:?}",
                dt.constructors
            );
        }
    });
}

/// A flattened local's Bool tag convention (`flattened_bool_tag_true_variant`)
/// and its discriminant read (`translate_discriminant`) agree: `fld0 == true`
/// yields the discriminant VALUE of the variant the convention names.
#[test]
fn test_flattened_bool_tag_true_variant_matches_discriminant_read() {
    with_test_ay_ctx_for_source(EXPLICIT_DISCR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_pf_local");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_pf_local", ChcConfig::default());
        chc_ctx.declare_block_relations();
        let discr_values = [7u128, 2u128];
        let mut checked = 0;
        for (local, decl) in body.locals().iter().enumerate() {
            let is_pf = matches!(
                decl.ty.kind(),
                TyKind::RigidTy(RigidTy::Adt(def, _)) if def.trimmed_name() == "PF"
            );
            if !is_pf {
                continue;
            }
            let Some(true_variant) = chc_ctx.flattened_bool_tag_true_variant(local) else {
                continue;
            };
            let place = Place { local, projection: vec![] };
            let Some(discr) = chc_ctx.translate_discriminant(&place, &HashSet::new()) else {
                continue;
            };
            let ExprValue::Ite { cond, .. } = discr.value() else {
                continue;
            };
            if !cond.sort().is_bool() {
                continue;
            }
            let (then_v, else_v) = ite_branches(&discr);
            assert_eq!(then_v, discr_values[true_variant], "_{local}: {discr}");
            assert_eq!(else_v, discr_values[1 - true_variant], "_{local}: {discr}");
            checked += 1;
        }
        assert!(checked > 0, "expected a flattened PF local with a Bool tag");
    });
}

/// A constant reference's DIRECT tag is the discriminant value: `&CA` for
/// `const CA: Perm = Perm::A(5)` (`A = 1, B = 0`) has discriminant 1. Reading
/// the tag byte 1 as a variant index named `B` (discriminant 0).
#[test]
fn test_const_ref_direct_tag_decodes_by_discriminant_value() {
    with_test_ay_ctx_for_source(EXPLICIT_DISCR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_perm_const_ref");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_perm_const_ref", ChcConfig::default());
        chc_ctx.declare_block_relations();
        let values: Vec<u64> =
            chc_ctx.ref_resolution.const_ref_discriminants.values().copied().collect();
        assert_eq!(values, vec![1], "const ref discriminants: {values:?}");
    });
}
