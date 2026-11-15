// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Rule E (design trust-mc-reds-final §4.4): an enum discriminant is the VALUE
//! `discriminant_for_variant` names, never a variant index. The exact arm
//! (`single_layout_enum_discriminant`) reads it from the layout; the
//! unresolved-referent fallback ranges over the values
//! (`enum_discriminant_value_set`) and is booked as an audited SoundHavoc only
//! when the place has a `Deref`.

#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use crate::codegen_ay::chc::codegen_ctx::{FallbackSoundness, fallback_soundness};
use crate::codegen_ay::chc::stmt::{DISCR_UNRESOLVED_DIRECT_PLACE, DISCR_UNRESOLVED_REFERENT};
use crate::codegen_ay::types::POINTER_WIDTH;

const SOURCE: &str = r#"
    #![allow(dead_code, unused_variables)]
    use std::convert::Infallible;
    #[repr(u8)]
    pub enum Explicit { A = 3, B = 7 }
    #[repr(i8)]
    pub enum Signed { M = -1, P = 1 }
    pub enum OneInhabited { A(Infallible), B }
    pub enum Two { A(u8), B }
    pub fn probe_discr(e: Explicit, s: Signed, z: OneInhabited, t: Two) {}
"#;

/// Every 64-bit constant in `expr`.
fn bv64_constants(expr: &Expr) -> Vec<u64> {
    let mut out = Vec::new();
    let mut stack = vec![expr];
    while let Some(e) = stack.pop() {
        if let ExprValue::BitVecConst { value, width } = e.value()
            && *width == POINTER_WIDTH
        {
            out.push(u64::try_from(value).unwrap());
        }
        stack.extend(expr_children(e));
    }
    out.sort_unstable();
    out
}

/// Runs `f` with a context and the signature's parameter types.
fn with_params(f: impl FnOnce(&ChcCtx<'_, '_>, &[rustc_public::ty::Ty]) + Send) {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_discr");
        let body = instance.body().expect("body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_discr", ChcConfig::default());
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_discr");
        f(&chc_ctx, sig.inputs());
    });
}

fn discr_symbol() -> Expr {
    Expr::var("discr_probe", ay_bindings::Sort::bitvec(POINTER_WIDTH))
}

fn adt_def(ty: rustc_public::ty::Ty) -> rustc_public::ty::AdtDef {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Adt(def, _)) => def,
        other => panic!("expected an enum, got {other:?}"),
    }
}

/// The fallback names the variants' discriminant values (3 and 7), not the
/// index range `[0, 2)`, which excludes both.
#[test]
fn test_value_set_names_explicit_discriminants() {
    with_params(|chc_ctx, params| {
        let set = chc_ctx.enum_discriminant_value_set(adt_def(params[0]), &discr_symbol());
        let seen = bv64_constants(&set);
        assert_eq!(seen, vec![3, 7], "the set is {{3, 7}}, got {set:?}");
    });
}

/// A negative discriminant is sign-extended to the pointer width, the
/// encoder's convention.
#[test]
fn test_value_set_sign_extends_negative_discriminants() {
    with_params(|chc_ctx, params| {
        let set = chc_ctx.enum_discriminant_value_set(adt_def(params[1]), &discr_symbol());
        let seen = bv64_constants(&set);
        assert_eq!(seen, vec![1, u64::MAX], "the set is {{1, -1}}, got {set:?}");
    });
}

/// The exact arm reads the one inhabited variant from the layout
/// (`A(Infallible)` is index 0, the value is `B`'s 1), and declines an enum
/// with two inhabited variants.
#[test]
fn test_exact_arm_reads_the_layouts_variant() {
    with_params(|chc_ctx, params| {
        let exact = chc_ctx
            .single_layout_enum_discriminant(params[2])
            .expect("a one-inhabited-variant enum has a Single layout");
        assert_eq!(bv64_constants(&exact), vec![1], "the value is B's, got {exact:?}");
        assert!(
            chc_ctx.single_layout_enum_discriminant(params[3]).is_none(),
            "two inhabited variants have no exact discriminant"
        );
        assert!(
            chc_ctx.single_layout_enum_discriminant(params[0]).is_none(),
            "a tagged enum has no exact discriminant"
        );
    });
}

/// The referent havoc is an audited SoundHavoc; reaching the fallback on a
/// place with no `Deref` is not.
#[test]
fn test_unresolved_referent_booking() {
    assert_eq!(fallback_soundness(DISCR_UNRESOLVED_REFERENT), FallbackSoundness::SoundHavoc);
    assert_eq!(fallback_soundness(DISCR_UNRESOLVED_DIRECT_PLACE), FallbackSoundness::FailClose);
}
