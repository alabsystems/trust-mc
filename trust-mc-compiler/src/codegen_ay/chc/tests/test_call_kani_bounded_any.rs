// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Native model of `<Vec<T> as kani::BoundedArbitrary>::bounded_any`.
//!
//! The library returns a `Vec` of length `0..=N` with capacity `N` and
//! arbitrary elements. The model must admit every such value and nothing
//! else: these tests pin the length range, the capacity and the element gate.
//! `String` keeps its library body (T4a review, 2026-09-24: with the lane's
//! no-op `String` drop, a model-built `String` proved a use after free clean).

#![allow(clippy::unwrap_used, clippy::panic)]

use super::super::call::codegen_call_kani_any_vec::{
    BoundedAnyTarget, bounded_any_element_is_exact, bounded_any_value, is_bounded_any_ctor_name,
};
use super::common::*;

#[test]
fn bounded_any_instance_names() {
    for name in [
        "kani::bounded_arbitrary::<impl kani::BoundedArbitrary for std::vec::Vec<T>>::bounded_any",
        "kani::bounded_arbitrary::<impl kani::BoundedArbitrary for std::vec::Vec<bool>>::bounded_any::<4>",
    ] {
        assert!(is_bounded_any_ctor_name(name), "{name}");
    }
    for name in [
        // The generator's closure is not the generator.
        "kani::bounded_arbitrary::<impl kani::BoundedArbitrary for std::vec::Vec<T>>::bounded_any::{closure#0}",
        "kani::bounded_arbitrary::<impl kani::BoundedArbitrary for std::vec::Vec<u8>>::bounded_any::<4>::{closure#0}",
        // Containers the model does not cover keep their library bodies.
        "kani::bounded_arbitrary::<impl kani::BoundedArbitrary for std::string::String>::bounded_any",
        "kani::bounded_arbitrary::<impl kani::BoundedArbitrary for std::string::String>::bounded_any::<5>",
        "kani::bounded_arbitrary::<impl kani::BoundedArbitrary for std::option::Option<T>>::bounded_any",
        "kani::bounded_arbitrary::<impl kani::BoundedArbitrary for std::boxed::Box<[T]>>::bounded_any",
        "my_crate::bounded_arbitrary::<impl kani::BoundedArbitrary for std::vec::Vec<T>>::bounded_any",
        "kani::any_vec",
    ] {
        assert!(!is_bounded_any_ctor_name(name), "{name}");
    }
}

const PROBE_SOURCE: &str = r#"
#![allow(dead_code)]
pub enum Tag { A, B }
pub struct Plain { x: u8 }
pub struct Dropper(u8);
impl Drop for Dropper { fn drop(&mut self) {} }
pub fn bounded_probe(a: Vec<u8>, b: Vec<bool>, c: Vec<char>, d: Vec<Tag>) {}
pub fn bounded_gate_probe(
    unit: Vec<()>,
    empty_arr: Vec<[u8; 0]>,
    unit_pair: Vec<((), [u16; 0])>,
    plain: Vec<Plain>,
    dropper: Vec<Dropper>,
    mixed: Vec<(u8, ())>,
    arr: Vec<[u32; 2]>,
    float: Vec<f64>,
) {}
"#;

fn vec_elem(ty: rustc_public::ty::Ty) -> rustc_public::ty::Ty {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Adt(_, args)) => match args.0.first() {
            Some(rustc_public::ty::GenericArgKind::Type(t)) => *t,
            other => panic!("Vec without an element type: {other:?}"),
        },
        other => panic!("not an ADT: {other:?}"),
    }
}

fn field(value: &Expr, index: usize) -> Expr {
    match value.value() {
        ExprValue::DatatypeConstructor { args, .. } => args[index].clone(),
        other => panic!("not a constructor: {other:?}"),
    }
}

#[test]
fn bounded_any_value_admits_exactly_the_library_values() {
    with_test_ay_ctx_for_source(PROBE_SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "bounded_probe");
        let inputs = sig.inputs();
        let instance = find_instance_by_suffix(ctx.tcx, "bounded_probe");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "bounded_probe", ChcConfig::default());

        // Vec<u8>: len = ite(f <= 4, f, 4), cap = 4, a fresh data array.
        let vec_u8 = ChcCtx::translate_ty(inputs[0]).expect("Vec<u8> sort");
        let (value, len) =
            bounded_any_value(&mut chc_ctx, BoundedAnyTarget::Vec(vec_elem(inputs[0])), 4, &vec_u8)
                .expect("Vec<u8> is modeled");
        assert_eq!(value.sort(), &vec_u8);
        assert_eq!(field(&value, 1), len, "fld_len is the length term");
        let ExprValue::Ite { cond, then_expr, else_expr } = len.value() else {
            panic!("length must be the folded ite, got {len:?}");
        };
        let four = Expr::bitvec_const(4u64, 64);
        assert_eq!(*else_expr, four, "the fold's other arm is N");
        assert_eq!(
            *cond,
            then_expr.clone().bvule(four.clone()),
            "the fold keeps f only when f <= N"
        );
        assert!(matches!(then_expr.value(), ExprValue::Var { .. }), "f is fresh");
        assert_eq!(field(&value, 2), four, "Vec::from([T; N]) then truncate: capacity N");
        assert!(matches!(field(&value, 3).value(), ExprValue::Var { .. }), "fresh element array");
        assert_eq!(chc_ctx.sound_fallback_count(), 0, "u8 elements are exact: nothing recorded");

        // N = 0: the empty Vec, no fresh length.
        let (_, len0) =
            bounded_any_value(&mut chc_ctx, BoundedAnyTarget::Vec(vec_elem(inputs[0])), 0, &vec_u8)
                .expect("N = 0 is modeled");
        assert_eq!(len0, Expr::bitvec_const(0u64, 64));

        // Element gate: bool is exact in its Bool sort; char and enums are not.
        assert!(bounded_any_element_is_exact(vec_elem(inputs[1])), "bool");
        assert!(!bounded_any_element_is_exact(vec_elem(inputs[2])), "char");
        assert!(!bounded_any_element_is_exact(vec_elem(inputs[3])), "enum");
        let vec_char = ChcCtx::translate_ty(inputs[2]).expect("Vec<char> sort");
        assert!(
            bounded_any_value(
                &mut chc_ctx,
                BoundedAnyTarget::Vec(vec_elem(inputs[2])),
                4,
                &vec_char
            )
            .is_none(),
            "an element type the array over-approximates keeps the library body"
        );
    });
}

/// The element gate admits only what the model represents exactly (T4a review,
/// 2026-09-24): a zero-sized element (std's capacity is `usize::MAX`, not N), a
/// user type (its `Drop` runs in the library's `truncate`; a hand-written
/// `Arbitrary` may restrict or panic) is declined and keeps the library body.
#[test]
fn bounded_any_element_gate_declines_what_the_model_leaves_out() {
    with_test_ay_ctx_for_source(PROBE_SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "bounded_gate_probe");
        let inputs = sig.inputs();
        let elem = |i: usize| vec_elem(inputs[i]);
        assert!(!bounded_any_element_is_exact(elem(0)), "() is zero-sized");
        assert!(!bounded_any_element_is_exact(elem(1)), "[u8; 0] is zero-sized");
        assert!(!bounded_any_element_is_exact(elem(2)), "((), [u16; 0]) is zero-sized");
        assert!(!bounded_any_element_is_exact(elem(3)), "a user struct is declined");
        assert!(!bounded_any_element_is_exact(elem(4)), "a type with Drop is declined");
        assert!(bounded_any_element_is_exact(elem(5)), "(u8, ()) occupies a byte");
        assert!(bounded_any_element_is_exact(elem(6)), "[u32; 2]");
        assert!(bounded_any_element_is_exact(elem(7)), "f64");

        let instance = find_instance_by_suffix(ctx.tcx, "bounded_gate_probe");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "bounded_gate_probe", ChcConfig::default());
        for i in [0usize, 1, 3, 4] {
            let Some(sort) = ChcCtx::translate_ty(inputs[i]) else {
                continue;
            };
            assert!(
                bounded_any_value(&mut chc_ctx, BoundedAnyTarget::Vec(elem(i)), 3, &sort).is_none(),
                "input {i}: a declined element type must keep the library body"
            );
        }
    });
}
