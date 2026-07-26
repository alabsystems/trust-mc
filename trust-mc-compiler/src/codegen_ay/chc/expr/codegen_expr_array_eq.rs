// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Shared fixed-array equality helpers for CHC call and statement codegen.

use ay_bindings::Expr;
use rustc_public::mir::{LocalDecl, Operand};
use rustc_public::ty::{RigidTy, TyKind};

/// Build the semantic equality for `SpecArrayEq::spec_eq` / `[T; N] == [T; N]`.
///
/// Array-sorted operands use finite `0..N` lane equality instead of full SMT
/// array extensional equality. Flat BV / datatype layouts keep direct equality.
pub(in crate::codegen_ay::chc) fn build_spec_array_eq(
    lhs: &Expr,
    rhs: &Expr,
    len: Option<usize>,
) -> Option<Expr> {
    if lhs.sort() != rhs.sort() {
        return None;
    }
    if lhs.sort().is_bitvec() || lhs.sort().is_datatype() || lhs.sort().is_bool() {
        return Some(lhs.clone().eq(rhs.clone()));
    }
    if lhs.sort().is_array() {
        return build_finite_array_eq(lhs, rhs, len?);
    }
    None
}

/// Build element-wise equality for finite SMT arrays over the concrete `0..len`
/// lane set rather than the infinite logical index domain.
pub(in crate::codegen_ay::chc) fn build_finite_array_eq(
    lhs: &Expr,
    rhs: &Expr,
    len: usize,
) -> Option<Expr> {
    if lhs.sort() != rhs.sort() {
        return None;
    }
    let array_sort = lhs.sort().array_sort()?;
    let idx_width = array_sort.index_sort.bitvec_width()?;
    let mut conj = Expr::bool_const(true);
    for i in 0..len {
        let idx = Expr::bitvec_const(i as u64, idx_width);
        conj = conj.and(lhs.clone().select(idx.clone()).eq(rhs.clone().select(idx)));
    }
    Some(conj)
}

/// Extract the concrete `N` from a `SpecArrayEq<..., N>` def-path.
pub(in crate::codegen_ay::chc) fn parse_spec_array_eq_length(callee_path: &str) -> Option<usize> {
    let spec_pos = callee_path.find("SpecArrayEq<")?;
    let after_spec = &callee_path[spec_pos + "SpecArrayEq<".len()..];
    let generics_end = find_matching_generic_end(after_spec)?;
    let generics = &after_spec[..generics_end];
    let last_comma = find_last_top_level_comma(generics)?;
    generics[last_comma + 1..].trim().parse().ok()
}

/// Recover the concrete array length from a `SpecArrayEq` path or MIR operand
/// type. Call sites with only MIR array metadata can pass `callee_path = None`.
pub(in crate::codegen_ay::chc) fn recover_spec_array_eq_len(
    callee_path: Option<&str>,
    arg: Option<&Operand>,
    locals: &[LocalDecl],
) -> Option<usize> {
    callee_path
        .and_then(parse_spec_array_eq_length)
        .or_else(|| arg.and_then(|operand| array_len_from_operand(operand, locals)))
}

fn array_len_from_operand(arg: &Operand, locals: &[LocalDecl]) -> Option<usize> {
    let ty = arg.ty(locals).ok()?;
    array_len_from_ty(ty)
}

fn array_len_from_ty(mut ty: rustc_public::ty::Ty) -> Option<usize> {
    for _ in 0..4 {
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Array(_, len_const)) => {
                return len_const.eval_target_usize().ok().map(|len| len as usize);
            }
            TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => ty = inner,
            _ => return None,
        }
    }
    None
}

fn find_matching_generic_end(generics: &str) -> Option<usize> {
    let mut depth = 1usize;
    for (idx, ch) in generics.char_indices() {
        match ch {
            '<' => depth += 1,
            '>' => {
                depth = depth.checked_sub(1)?;
                if depth == 0 {
                    return Some(idx);
                }
            }
            _ => {}
        }
    }
    None
}

fn find_last_top_level_comma(generics: &str) -> Option<usize> {
    let mut depth = 0usize;
    let mut last_comma = None;
    for (idx, ch) in generics.char_indices() {
        match ch {
            '<' => depth += 1,
            '>' => depth = depth.checked_sub(1)?,
            ',' if depth == 0 => last_comma = Some(idx),
            _ => {}
        }
    }
    last_comma
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::codegen_ay::context::with_test_ay_ctx_for_source;
    use crate::codegen_ay::test_fixtures::find_instance_by_suffix;
    use ay_bindings::Sort;
    use rustc_public::mir::{Rvalue, StatementKind};

    #[test]
    fn test_build_spec_array_eq_returns_bool_eq_for_matching_bv_args() {
        let a = Expr::bitvec_const(0xDEAD_BEEF_CAFE_BABEu64 as u128, 128);
        let b = Expr::bitvec_const(0xDEAD_BEEF_CAFE_BABEu64 as u128, 128);
        let result =
            build_spec_array_eq(&a, &b, Some(2)).expect("BV-backed arrays should use direct eq");
        assert!(result.sort().is_bool(), "result should be Bool");
        assert_eq!(result, a.eq(b));
    }

    #[test]
    fn test_build_spec_array_eq_rejects_sort_mismatch() {
        let a = Expr::bitvec_const(0u64, 128);
        let b = Expr::bitvec_const(0u64, 64);
        assert!(build_spec_array_eq(&a, &b, Some(2)).is_none());
    }

    #[test]
    fn test_build_finite_array_eq_handles_array_sorted_operands() {
        let idx_sort = Sort::bitvec(64);
        let elem_sort = Sort::bitvec(64);
        let arr_sort = Sort::array(idx_sort, elem_sort);
        let a = Expr::var("arr_a", arr_sort.clone());
        let b = Expr::var("arr_b", arr_sort);
        let result = build_finite_array_eq(&a, &b, 2)
            .expect("finite array equality should inline over concrete lanes");
        assert!(result.sort().is_bool(), "result should be Bool");
        let idx0 = Expr::bitvec_const(0u64, 64);
        let idx1 = Expr::bitvec_const(1u64, 64);
        let expected = Expr::bool_const(true)
            .and(a.clone().select(idx0.clone()).eq(b.clone().select(idx0)))
            .and(a.select(idx1.clone()).eq(b.select(idx1)));
        assert_eq!(result, expected);
    }

    #[test]
    fn test_parse_spec_array_eq_length_handles_nested_generics() {
        assert_eq!(
            parse_spec_array_eq_length(
                "<std::simd::Mask<i64, 2> as std::array::equality::SpecArrayEq<std::simd::Mask<i64, 2>, 2>>::spec_eq"
            ),
            Some(2)
        );
        assert_eq!(
            parse_spec_array_eq_length(
                "<u8 as core::array::equality::SpecArrayEq<u8, 16>>::spec_eq"
            ),
            Some(16)
        );
        assert_eq!(parse_spec_array_eq_length("std::cmp::PartialEq::eq"), None);
    }

    #[test]
    fn test_recover_spec_array_eq_len_falls_back_to_ref_operand_type() {
        const SOURCE: &str = r#"
            pub fn probe(arg: &[u8; 4]) -> &[u8; 4] {
                arg
            }
        "#;

        with_test_ay_ctx_for_source(SOURCE, |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "probe");
            let body = instance.body().expect("function body");
            let operand = body
                .blocks
                .iter()
                .flat_map(|block| block.statements.iter())
                .find_map(|stmt| match &stmt.kind {
                    StatementKind::Assign(_, Rvalue::Use(operand)) => Some(operand),
                    _ => None,
                })
                .expect("probe should contain a use of the ref arg");
            assert_eq!(
                recover_spec_array_eq_len(
                    Some("std::cmp::PartialEq::eq"),
                    Some(operand),
                    body.locals(),
                ),
                Some(4)
            );
        });
    }

    #[test]
    fn test_recover_spec_array_eq_len_handles_direct_array_operand_type() {
        const SOURCE: &str = r#"
            pub fn probe(arg: [u8; 4]) -> [u8; 4] {
                arg
            }
        "#;

        with_test_ay_ctx_for_source(SOURCE, |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "probe");
            let body = instance.body().expect("function body");
            let operand = body
                .blocks
                .iter()
                .flat_map(|block| block.statements.iter())
                .find_map(|stmt| match &stmt.kind {
                    StatementKind::Assign(_, Rvalue::Use(operand)) => Some(operand),
                    _ => None,
                })
                .expect("probe should contain a use of the array arg");
            assert_eq!(recover_spec_array_eq_len(None, Some(operand), body.locals()), Some(4));
        });
    }
}
