// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Shared fixed-array equality helpers for CHC call and statement codegen.

use ay_bindings::{Expr, Sort};
use rustc_public::CrateDef;
use rustc_public::mir::mono::Instance;
use rustc_public::mir::{LocalDecl, Operand};
use rustc_public::ty::{RigidTy, TyKind};

impl<'tcx, 'body> crate::codegen_ay::chc::ChcCtx<'tcx, 'body> {
    /// Only the resolved, body-providing default implementation performs
    /// semantic element comparisons. The bytewise specialization must retain
    /// the typed-array fast path and must never become an untyped body walk.
    pub(in crate::codegen_ay::chc) fn spec_array_has_default_body(
        &self,
        instance: &Instance,
    ) -> bool {
        crate::kani_middle::std_abstraction::is_default_spec_array_comparison(self.tcx, instance)
    }

    /// A homogeneous element model cannot stand in for a user-defined
    /// `PartialEq<U>` between different array or slice element types. Read
    /// both instantiated inputs: preprocessing may already have lowered an
    /// array comparison into the corresponding slice comparison.
    pub(in crate::codegen_ay::chc) fn has_heterogeneous_sequence_elements(
        &self,
        func: &Operand,
        locals: &[LocalDecl],
    ) -> bool {
        let Some(sig) =
            func.ty(locals).ok().and_then(|ty| self.resolve_body_ty(ty).kind().fn_sig())
        else {
            return false;
        };
        let sig = sig.skip_binder();
        let inputs = sig.inputs();
        let [lhs, rhs] = inputs else { return false };
        let lhs = crate::codegen_ay::shared::compare_loops::peel_refs(self.resolve_body_ty(*lhs));
        let rhs = crate::codegen_ay::shared::compare_loops::peel_refs(self.resolve_body_ty(*rhs));
        if let (
            TyKind::RigidTy(RigidTy::Array(_, lhs_len)),
            TyKind::RigidTy(RigidTy::Array(_, rhs_len)),
        ) = (lhs.kind(), rhs.kind())
            && lhs_len.eval_target_usize() == Ok(0)
            && rhs_len.eval_target_usize() == Ok(0)
        {
            return false;
        }
        let element = |ty: rustc_public::ty::Ty| match ty.kind() {
            TyKind::RigidTy(RigidTy::Array(elem, _) | RigidTy::Slice(elem)) => {
                Some(self.resolve_body_ty(elem))
            }
            _ => None,
        };
        matches!((element(lhs), element(rhs)), (Some(lhs), Some(rhs)) if lhs != rhs)
    }

    /// Authenticate the resolved method and its owning core trait. Printed
    /// paths are only diagnostic spellings; they confer no model authority.
    pub(in crate::codegen_ay::chc) fn authenticated_spec_array_comparison_is_ne(
        &self,
        def: rustc_public::DefId,
    ) -> Option<bool> {
        crate::kani_middle::std_abstraction::authenticated_spec_array_comparison_is_ne(
            self.tcx, def,
        )
    }

    /// All element types of the resolved core trait application must have
    /// Rust equality equal to encoding equality. Identity alone does not make
    /// the default float/custom-PartialEq implementation bytewise.
    pub(in crate::codegen_ay::chc) fn spec_array_elements_are_faithful(
        &self,
        func: &Operand,
        locals: &[LocalDecl],
    ) -> bool {
        let Some(ty) = func.ty(locals).ok().map(|ty| self.resolve_body_ty(ty)) else {
            return false;
        };
        let TyKind::RigidTy(RigidTy::FnDef(_, args)) = ty.kind() else { return false };
        let mut element_ty = None;
        for arg in &args.0 {
            if let rustc_public::ty::GenericArgKind::Type(ty) = arg {
                let ty = self.resolve_body_ty(*ty);
                // Faithful T == T and U == U do not establish T == U:
                // the heterogeneous PartialEq implementation can be custom.
                if element_ty.is_some_and(|previous| previous != ty)
                    || !crate::codegen_ay::shared::compare_loops::eq_is_encoding_eq(ty)
                {
                    return false;
                }
                element_ty = Some(ty);
            }
        }
        element_ty.is_some()
    }

    pub(in crate::codegen_ay::chc) fn spec_array_comparison_for_operand(
        &self,
        func: &Operand,
        locals: &[LocalDecl],
    ) -> Option<bool> {
        let ty = self.resolve_body_ty(func.ty(locals).ok()?);
        let TyKind::RigidTy(RigidTy::FnDef(def, args)) = ty.kind() else { return None };
        let instance = Instance::resolve(def, &args).ok()?;
        self.authenticated_spec_array_comparison_is_ne(instance.def.def_id())
    }
}

/// Does an SMT array occur anywhere in `sort`?
///
/// SMT equality on an array is extensional over the whole index domain, while
/// `PartialEq` on `[T; N]` compares indices `0..N`. Two encodings of the same
/// Rust array (a decoded constant over a constant default, a flattened state
/// slot over a fresh one) can agree on every index Rust sees and still be
/// unequal, so no fast path may decide `==` on such a sort with `=`.
pub(in crate::codegen_ay::chc) fn sort_contains_array(sort: &Sort) -> bool {
    fn walk(sort: &Sort, depth: usize) -> bool {
        if depth == 0 {
            return true;
        }
        match sort.inner() {
            ay_bindings::SortInner::Array(_) => true,
            ay_bindings::SortInner::Datatype(dt) => dt
                .constructors
                .iter()
                .flat_map(|ctor| ctor.fields.iter())
                .any(|field| walk(&field.sort, depth - 1)),
            _ => false,
        }
    }
    walk(sort, 8)
}

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
    if lhs.sort().is_datatype() && sort_contains_array(lhs.sort()) {
        // Extensional equality over an embedded array is not `PartialEq`.
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
                    StatementKind::Assign(_, Rvalue::Use(operand, ..)) => Some(operand),
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
                    StatementKind::Assign(_, Rvalue::Use(operand, ..)) => Some(operand),
                    _ => None,
                })
                .expect("probe should contain a use of the array arg");
            assert_eq!(recover_spec_array_eq_len(None, Some(operand), body.locals()), Some(4));
        });
    }
}
