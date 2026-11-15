// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Exact equality of the remaining elements of standard iterators.
//!
//! Pointer/state equality is not sequence equality: distinct storage can hold
//! equal elements, and the model's pointer fields can coincide for different
//! data. Only the authenticated default Iterator::eq and known sequence
//! carriers enter this lane. Adapters and custom equality retain their bodies.

#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use ay_bindings::{Expr, Sort};
use rustc_public::mir::mono::Instance;
use rustc_public::mir::{LocalDecl, Operand};
use rustc_public::ty::{FloatTy, GenericArgKind, RigidTy, Ty, TyKind, UintTy};
use rustc_public::{CrateDef, rustc_internal};

#[path = "inline_iterator_eq_len.rs"]
mod length;
use length::unadvanced_iterator_len;

use super::ChcCtx;
use super::codegen_call_slice_helpers::ResolvedSliceBacking;
use crate::codegen_ay::provenance::Val;
use crate::codegen_ay::shared::compare_loops;
use crate::codegen_ay::types::POINTER_WIDTH;

#[derive(Clone, Copy, PartialEq, Eq)]
enum SequenceKind {
    Slice(Ty),
    Chars,
}

pub(super) fn inline_iterator_eq_expr(
    ctx: &ChcCtx<'_, '_>,
    func: &Operand,
    callee_path: &str,
    args: &[Expr],
    arg_operands: &[Operand],
    locals: &[LocalDecl],
) -> Option<Expr> {
    if args.len() != 2
        || arg_operands.len() != 2
        || !callee_path.ends_with("::eq")
        || !callee_path.contains("Iterator")
    {
        return None;
    }
    let function_ty = ctx.resolve_body_ty(func.ty(locals).ok()?);
    let TyKind::RigidTy(RigidTy::FnDef(def, generics)) = function_ty.kind() else {
        return None;
    };
    let instance = Instance::resolve(def, &generics).ok()?;
    if crate::kani_middle::transform::unit_has_stubs() {
        return None;
    }
    let resolved = rustc_internal::internal(ctx.tcx, instance.def.def_id());
    if !crate::kani_middle::std_abstraction::is_sysroot_core_definition(ctx.tcx, resolved) {
        return None;
    }
    let item = ctx.tcx.opt_associated_item(resolved)?;
    let method = item.trait_item_def_id().unwrap_or(resolved);
    let owner = ctx.tcx.trait_of_assoc(method)?;
    // An override is a different program, even if it implements Iterator.
    if method != resolved
        || ctx.tcx.item_name(method).as_str() != "eq"
        || !crate::kani_middle::std_abstraction::is_sysroot_core_definition_at(
            ctx.tcx,
            owner,
            &["iter", "traits", "iterator", "Iterator"],
        )
    {
        return None;
    }
    let signature = function_ty.kind().fn_sig()?.skip_binder();
    let [lhs_ty, rhs_ty] = signature.inputs() else { return None };
    let kind = sequence_kind(ctx, ctx.resolve_body_ty(*lhs_ty))?;
    if sequence_kind(ctx, ctx.resolve_body_ty(*rhs_ty))? != kind {
        return None;
    }
    let elem = match kind {
        SequenceKind::Slice(elem) => elem,
        // UTF-8 decoding is injective. Two valid Chars byte suffixes encode
        // the same char sequence iff those suffixes contain identical bytes.
        SequenceKind::Chars => Ty::unsigned_ty(UintTy::U8),
    };
    let lhs = sequence_backing(&args[0], kind == SequenceKind::Chars)?;
    let rhs = sequence_backing(&args[1], kind == SequenceKind::Chars)?;
    if lhs.data.as_expr().sort() != rhs.data.as_expr().sort() {
        return None;
    }
    let elem_eq = |a: Expr, b: Expr| scalar_element_eq(elem, &a, &b);
    // Check the element semantics even for unequal lengths. A custom
    // PartialEq can panic or mutate state before iteration observes the end.
    // References, heterogeneous/custom equality and unsupported layouts must
    // never become encoding equality or a constant length-only result.
    let zero = Expr::bitvec_const(0u64, POINTER_WIDTH);
    elem_eq(
        lhs.data.as_expr().clone().select(zero.clone()),
        rhs.data.as_expr().clone().select(zero),
    )?;
    ChcCtx::slice_eq_formula_with(
        &lhs,
        &rhs,
        &elem_eq,
        arg_operands.iter().find_map(|arg| unadvanced_iterator_len(ctx, arg, locals)),
        compare_loops::eq_is_encoding_eq(elem),
    )
}

// Slice iterator storage flattens aggregate elements. Raw equality on that
// BV would compare padding/inactive payloads instead of Rust values. Until
// those layouts are decoded here, their real PartialEq bodies own the call.
fn scalar_element_eq(elem: Ty, lhs: &Expr, rhs: &Expr) -> Option<Expr> {
    match elem.kind() {
        TyKind::RigidTy(RigidTy::Tuple(fields)) if fields.is_empty() => {
            Some(Expr::bool_const(true))
        }
        TyKind::RigidTy(
            RigidTy::Bool
            | RigidTy::Char
            | RigidTy::Int(_)
            | RigidTy::Uint(_)
            | RigidTy::Float(FloatTy::F32 | FloatTy::F64),
        ) => compare_loops::rust_value_eq(elem, lhs, rhs),
        _ => None,
    }
}

fn sequence_kind(ctx: &ChcCtx<'_, '_>, ty: Ty) -> Option<SequenceKind> {
    // Taking &mut Iterator by value still mutates an observable iterator.
    // This expression-only lane models owned, consumed sequence values.
    let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() else { return None };
    let internal = rustc_internal::internal(ctx.tcx, def.def_id());
    if !crate::kani_middle::std_abstraction::is_sysroot_core_definition(ctx.tcx, internal) {
        return None;
    }
    let is_at = |path: &[&str]| {
        crate::kani_middle::std_abstraction::is_sysroot_core_definition_at(ctx.tcx, internal, path)
    };
    if is_at(&["slice", "iter", "Iter"]) || is_at(&["slice", "iter", "IterMut"]) {
        let elem = args.0.iter().find_map(|arg| match arg {
            GenericArgKind::Type(elem) => Some(ctx.resolve_body_ty(*elem)),
            _ => None,
        })?;
        Some(SequenceKind::Slice(elem))
    } else if is_at(&["str", "iter", "Chars"]) {
        Some(SequenceKind::Chars)
    } else {
        None
    }
}

fn sequence_backing(value: &Expr, chars: bool) -> Option<ResolvedSliceBacking> {
    // Chars has exactly one known slice-iterator member. Do not recursively
    // search arbitrary wrappers: Take/Map/Filter/Rev change the sequence.
    let iter = if chars { field(value, "fld_iter")? } else { value.clone() };
    let pos = field(&iter, "fld_pos")?;
    let storage = field(&iter, "fld_vec")?;
    let len = field(&storage, "fld_len")?;
    let data = field(&storage, "fld_data")?;
    if pos.sort() != &Sort::bitvec(POINTER_WIDTH)
        || len.sort() != pos.sort()
        || &data.sort().array_sort()?.index_sort != pos.sort()
    {
        return None;
    }
    let remaining = Expr::ite(
        pos.clone().bvult(len.clone()),
        len.bvsub(pos.clone()),
        Expr::bitvec_const(0u64, POINTER_WIDTH),
    );
    Some(ResolvedSliceBacking {
        data: Val::of_value(data),
        len: Val::of_value(remaining),
        offset: Val::of_value(pos),
    })
}

fn field(value: &Expr, name: &str) -> Option<Expr> {
    let sort = ChcCtx::get_dt_field_sort(value, name)?;
    let datatype = value.sort().datatype_name()?;
    Some(value.clone().field_select(datatype, name, sort))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn bv(value: u64) -> Expr {
        Expr::bitvec_const(value, POINTER_WIDTH)
    }

    fn iterator(bytes: &[u8], pos: u64, ptr: u64, default: u8, chars: bool) -> Expr {
        iterator_state(bytes, bv(pos), bv(bytes.len() as u64), ptr, default, chars)
    }

    fn iterator_state(
        bytes: &[u8],
        pos: Expr,
        len: Expr,
        ptr: u64,
        default: u8,
        chars: bool,
    ) -> Expr {
        let index_sort = Sort::bitvec(POINTER_WIDTH);
        let data = bytes.iter().enumerate().fold(
            Expr::const_array(index_sort, Expr::bitvec_const(default, 8)),
            |data, (index, byte)| data.store(bv(index as u64), Expr::bitvec_const(*byte, 8)),
        );
        let slice_sort = crate::codegen_ay::names::struct_sort(
            "IteratorEqSlice",
            [
                ("fld_ptr", Sort::bitvec(64)),
                ("fld_len", Sort::bitvec(64)),
                ("fld_data", data.sort().clone()),
            ],
        );
        let slice = Expr::datatype_constructor(
            "IteratorEqSlice",
            "IteratorEqSlice_mk",
            vec![bv(ptr), len, data],
            slice_sort.clone(),
        );
        let iter_sort = crate::codegen_ay::names::struct_sort(
            "IteratorEqIter",
            [("fld_vec", slice_sort), ("fld_pos", Sort::bitvec(64))],
        );
        let iter = Expr::datatype_constructor(
            "IteratorEqIter",
            "IteratorEqIter_mk",
            vec![slice, pos],
            iter_sort.clone(),
        );
        if !chars {
            return iter;
        }
        let chars_sort =
            crate::codegen_ay::names::struct_sort("IteratorEqChars", [("fld_iter", iter_sort)]);
        Expr::datatype_constructor("IteratorEqChars", "IteratorEqChars_mk", vec![iter], chars_sort)
    }

    fn equals(lhs: Expr, rhs: Expr, chars: bool) -> Expr {
        let lhs = sequence_backing(&lhs, chars).unwrap();
        let rhs = sequence_backing(&rhs, chars).unwrap();
        ChcCtx::slice_eq_formula_with(&lhs, &rhs, &|a, b| Some(a.eq(b)), None, true).unwrap()
    }

    fn assert_value(value: Expr, expected: bool) {
        // Ask AY for both directions: a closed formula has exactly its
        // reference sequence verdict, not merely an unsatisfiable encoding.
        for (asserted, wanted) in [(value.clone(), expected), (value.not(), !expected)] {
            let commands =
                ay_frontend::parse(&format!("(set-logic ALL)\n(assert {asserted})\n(check-sat)\n"))
                    .unwrap();
            let mut solver = ay_dpll::Executor::new();
            solver.set_timeout(Some(std::time::Duration::from_secs(5)));
            let output = solver.execute_all(&commands).unwrap();
            let verdict = if wanted { "sat" } else { "unsat" };
            assert!(
                output.iter().any(|line| line.trim() == verdict),
                "expected {verdict}: {output:?}"
            );
        }
    }

    #[test]
    fn different_elements_at_the_same_pointer_are_unequal() {
        assert_value(
            equals(iterator(&[1, 2], 0, 0, 0, false), iterator(&[1, 3], 0, 0, 0, false), false),
            false,
        );
    }

    #[test]
    fn equal_values_in_distinct_storage_are_equal() {
        assert_value(
            equals(iterator(&[1, 2], 0, 100, 9, false), iterator(&[1, 2], 0, 200, 8, false), false),
            true,
        );
    }

    #[test]
    fn equal_suffixes_can_have_different_positions_and_original_lengths() {
        assert_value(
            equals(
                iterator(&[9, 1, 2], 1, 100, 9, false),
                iterator(&[1, 2], 0, 200, 8, false),
                false,
            ),
            true,
        );
    }

    #[test]
    fn consumed_prefixes_and_unread_array_cells_do_not_affect_equality() {
        assert_value(
            equals(
                iterator(&[9, 1, 2], 1, 0, 7, false),
                iterator(&[8, 1, 2], 1, 0, 6, false),
                false,
            ),
            true,
        );
    }

    #[test]
    fn exhausted_iterators_are_equal_despite_different_state() {
        assert_value(
            equals(iterator(&[1, 2], 2, 100, 9, false), iterator(&[3], 1, 200, 8, false), false),
            true,
        );
    }

    #[test]
    fn remaining_lengths_must_match() {
        assert_value(
            equals(iterator(&[1, 2], 0, 0, 0, false), iterator(&[1, 2, 3], 0, 0, 0, false), false),
            false,
        );
    }

    #[test]
    fn chars_compare_utf8_suffix_contents() {
        assert_value(
            equals(
                iterator("é🦀".as_bytes(), 0, 100, 0, true),
                iterator("é🦀".as_bytes(), 0, 200, 1, true),
                true,
            ),
            true,
        );
        assert_value(
            equals(
                iterator("é🦀".as_bytes(), 0, 100, 0, true),
                iterator("é🐍".as_bytes(), 0, 200, 1, true),
                true,
            ),
            false,
        );
        assert_value(
            equals(
                iterator("xé".as_bytes(), 1, 100, 0, true),
                iterator("é".as_bytes(), 0, 200, 1, true),
                true,
            ),
            true,
        );
    }

    #[test]
    fn symbolic_remaining_ranges_match_all_valid_finite_sequences() {
        let names = ["left_pos", "left_len", "right_pos", "right_len"];
        let vars: Vec<_> = names.iter().map(|name| Expr::var(*name, Sort::bitvec(64))).collect();
        let left = [9u8, 1, 2];
        let right = [8u8, 1, 2];
        let value = equals(
            iterator_state(&left, vars[0].clone(), vars[1].clone(), 100, 0, false),
            iterator_state(&right, vars[2].clone(), vars[3].clone(), 200, 0, false),
            false,
        );
        assert!(
            value.to_string().contains("forall"),
            "dynamic range must exercise the quantified formula"
        );
        // Independent reference: enumerate every valid (pos, len) pair and
        // compare the host slices. No modeled array or pointer equality is
        // used to decide the expected answer.
        let mut matching_states = Vec::new();
        for left_len in 0..=left.len() {
            for left_pos in 0..=left_len {
                for right_len in 0..=right.len() {
                    for right_pos in 0..=right_len {
                        if left[left_pos..left_len] == right[right_pos..right_len] {
                            matching_states.push(Expr::and_many(
                                vars.iter()
                                    .zip([left_pos, left_len, right_pos, right_len])
                                    .map(|(var, value)| var.clone().eq(bv(value as u64)))
                                    .collect(),
                            ));
                        }
                    }
                }
            }
        }
        let expected = Expr::or_many(matching_states);
        let valid = Expr::and_many(vec![
            vars[0].clone().bvule(vars[1].clone()),
            vars[1].clone().bvule(bv(3)),
            vars[2].clone().bvule(vars[3].clone()),
            vars[3].clone().bvule(bv(3)),
        ]);
        let declarations = names
            .iter()
            .map(|name| format!("(declare-const {name} (_ BitVec 64))\n"))
            .collect::<String>();
        let smt = format!(
            "(set-logic ALL)\n{declarations}(assert {valid})\n(assert (not (= {value} {expected})))\n(check-sat)\n"
        );
        let commands = ay_frontend::parse(&smt).unwrap();
        let mut solver = ay_dpll::Executor::new();
        solver.set_timeout(Some(std::time::Duration::from_secs(5)));
        let output = solver.execute_all(&commands).unwrap();
        assert!(
            output.iter().any(|line| line.trim() == "unsat"),
            "symbolic sequence mismatch: {output:?}"
        );
    }

    #[test]
    fn long_constant_sequences_use_the_exact_quantified_range() {
        let lhs = [1u8; 17];
        let mut rhs = lhs;
        rhs[16] = 2;
        assert_value(
            equals(iterator(&lhs, 0, 0, 9, false), iterator(&lhs, 0, 1, 8, false), false),
            true,
        );
        assert_value(
            equals(iterator(&lhs, 0, 0, 9, false), iterator(&rhs, 0, 0, 8, false), false),
            false,
        );
    }
}

#[cfg(all(test, feature = "compiler-corpus-tests"))]
mod type_tests {
    use super::*;
    use crate::codegen_ay::chc::ChcConfig;
    use crate::codegen_ay::context::with_test_ay_ctx_for_source;
    use crate::codegen_ay::test_fixtures::find_instance_by_suffix;

    #[test]
    fn only_owned_standard_sequence_types_are_carriers() {
        const SOURCE: &str = r#"
            #![allow(dead_code, unused_variables)]
            pub struct Fake { fld_vec: u8, fld_pos: usize }
            pub fn inputs(
                a: core::slice::Iter<'_, u8>,
                b: core::str::Chars<'_>,
                c: core::iter::Take<core::slice::Iter<'_, u8>>,
                d: core::iter::Rev<core::slice::Iter<'_, u8>>,
                e: &mut core::slice::Iter<'_, u8>,
                f: Fake,
            ) {}
        "#;
        with_test_ay_ctx_for_source(SOURCE, |ctx| {
            let body = find_instance_by_suffix(ctx.tcx, "inputs").body().unwrap();
            let chc = ChcCtx::new(ctx.tcx, &body, "inputs", ChcConfig::default());
            assert!(matches!(
                sequence_kind(&chc, body.locals()[1].ty),
                Some(SequenceKind::Slice(_))
            ));
            assert!(matches!(sequence_kind(&chc, body.locals()[2].ty), Some(SequenceKind::Chars)));
            for local in 3..=6 {
                assert!(sequence_kind(&chc, body.locals()[local].ty).is_none(), "local {local}");
            }
        });
    }

    #[test]
    fn unit_elements_ignore_their_placeholder_bits() {
        const SOURCE: &str = "pub fn units(a: core::slice::Iter<'_, ()>) {}";
        with_test_ay_ctx_for_source(SOURCE, |ctx| {
            let body = find_instance_by_suffix(ctx.tcx, "units").body().unwrap();
            let chc = ChcCtx::new(ctx.tcx, &body, "units", ChcConfig::default());
            let Some(SequenceKind::Slice(elem)) = sequence_kind(&chc, body.locals()[1].ty) else {
                panic!("standard unit iterator should be recognized");
            };
            assert_eq!(
                scalar_element_eq(elem, &Expr::bool_const(true), &Expr::bool_const(false)),
                Some(Expr::bool_const(true))
            );
        });
    }

    #[test]
    fn custom_element_equality_is_not_replaced_by_bit_equality() {
        const SOURCE: &str = r#"
            #![allow(dead_code)]
            pub struct Parity(u8);
            impl PartialEq for Parity {
                fn eq(&self, rhs: &Self) -> bool { self.0 % 2 == rhs.0 % 2 }
            }
            pub fn items(a: core::slice::Iter<'_, Parity>) {}
        "#;
        with_test_ay_ctx_for_source(SOURCE, |ctx| {
            let body = find_instance_by_suffix(ctx.tcx, "items").body().unwrap();
            let chc = ChcCtx::new(ctx.tcx, &body, "items", ChcConfig::default());
            let Some(SequenceKind::Slice(elem)) = sequence_kind(&chc, body.locals()[1].ty) else {
                panic!("standard slice iterator should be recognized");
            };
            assert!(!compare_loops::eq_is_encoding_eq(elem));
            assert!(
                scalar_element_eq(elem, &Expr::bitvec_const(1u8, 8), &Expr::bitvec_const(3u8, 8))
                    .is_none()
            );
        });
    }
}
