// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Array-sort primitive cmp helpers for StubKind-routed comparisons.
//!
//! Part of #3806: repr-SIMD values flowing through `kani::any()` can reach the
//! generic primitive cmp stub as Array-sort operands instead of the string-path
//! comparison dispatcher. Reuse the fixed-array lexicographic helpers here so
//! the stub path stays precise instead of falling back.

use ay_bindings::Expr;
use rustc_public::mir::Operand;
use rustc_public::ty::{RigidTy, TyKind};

use crate::codegen_ay::stubs::StubKind;

const MAX_LEXICO_LANES: usize = 16;

pub(in crate::codegen_ay::chc) fn compute_array_cmp_result(
    stub: StubKind,
    lhs: &Expr,
    rhs: &Expr,
    arg: &Operand,
    locals: &[rustc_public::mir::LocalDecl],
    is_signed: bool,
) -> Option<Expr> {
    if !lhs.sort().is_array() || !rhs.sort().is_array() {
        return None;
    }

    match stub {
        // Part of #3875: Element-wise array equality for finite arrays.
        // Full SMT array equality (= a b) checks ALL indices including
        // uninitialized positions beyond N, which fails for symbolic array bases.
        StubKind::PrimitivePartialEqEq | StubKind::PrimitivePartialEqNe => {
            let len = array_len_from_operand(arg, locals)
                .or_else(|| array_len_from_body_locals(arg, locals))?;
            if len > MAX_LEXICO_LANES {
                return None;
            }
            let arr = lhs.sort().array_sort()?;
            let idx_width = arr.index_sort.bitvec_width()?;
            let mut conj = Expr::bool_const(true);
            for i in 0..len {
                let idx = Expr::bitvec_const(i as u64, idx_width);
                let l_elem = lhs.clone().select(idx.clone());
                let r_elem = rhs.clone().select(idx);
                conj = conj.and(l_elem.eq(r_elem));
            }
            if matches!(stub, StubKind::PrimitivePartialEqNe) {
                Some(conj.not())
            } else {
                Some(conj)
            }
        }
        StubKind::OrdCmp
        | StubKind::PrimitivePartialOrdLt
        | StubKind::PrimitivePartialOrdLe
        | StubKind::PrimitivePartialOrdGt
        | StubKind::PrimitivePartialOrdGe => {
            let len = array_len_from_operand(arg, locals)
                .or_else(|| array_len_from_body_locals(arg, locals))?;
            if len > MAX_LEXICO_LANES {
                return None;
            }

            match stub {
                StubKind::OrdCmp => build_lexicographic_cmp(lhs, rhs, len, is_signed),
                StubKind::PrimitivePartialOrdLt => {
                    build_lexicographic_ord(lhs, rhs, len, "lt", is_signed)
                }
                StubKind::PrimitivePartialOrdLe => {
                    build_lexicographic_ord(lhs, rhs, len, "le", is_signed)
                }
                StubKind::PrimitivePartialOrdGt => {
                    build_lexicographic_ord(lhs, rhs, len, "gt", is_signed)
                }
                StubKind::PrimitivePartialOrdGe => {
                    build_lexicographic_ord(lhs, rhs, len, "ge", is_signed)
                }
                _ => None,
            }
        }
        _ => None,
    }
}

fn array_len_from_operand(arg: &Operand, locals: &[rustc_public::mir::LocalDecl]) -> Option<usize> {
    extract_fixed_array_len(arg.ty(locals).ok()?)
}

fn array_len_from_body_locals(
    arg: &Operand,
    locals: &[rustc_public::mir::LocalDecl],
) -> Option<usize> {
    let elem_ty = peel_refs_to_slice_elem(arg.ty(locals).ok()?)?;
    let mut found_len: Option<usize> = None;
    for local_decl in locals {
        if let Some(len) = extract_array_len_from_ty(local_decl.ty, elem_ty) {
            match found_len {
                None => found_len = Some(len),
                Some(existing) if existing == len => {}
                Some(_) => return None,
            }
        }
    }
    found_len
}

fn peel_refs_to_slice_elem(ty: rustc_public::ty::Ty) -> Option<rustc_public::ty::Ty> {
    let mut inner = ty;
    for _ in 0..3 {
        match inner.kind() {
            TyKind::RigidTy(RigidTy::Slice(elem)) => return Some(elem),
            TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) => inner = pointee,
            _ => return None,
        }
    }
    None
}

fn extract_array_len_from_ty(
    ty: rustc_public::ty::Ty,
    elem_ty: rustc_public::ty::Ty,
) -> Option<usize> {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Array(arr_elem, const_len)) => {
            if arr_elem == elem_ty {
                const_len.eval_target_usize().ok().map(|n| n as usize)
            } else {
                None
            }
        }
        TyKind::RigidTy(RigidTy::Ref(_, inner, _)) | TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => {
            extract_array_len_from_ty(inner, elem_ty)
        }
        TyKind::RigidTy(RigidTy::Adt(adt_def, args)) => {
            let variants = adt_def.variants();
            if variants.len() == 1 && variants[0].fields().len() == 1 {
                let field_ty = variants[0].fields()[0].ty_with_args(&args);
                extract_array_len_from_ty(field_ty, elem_ty)
            } else {
                None
            }
        }
        _ => None,
    }
}

fn extract_fixed_array_len(ty: rustc_public::ty::Ty) -> Option<usize> {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Array(_, const_len)) => {
            const_len.eval_target_usize().ok().map(|n| n as usize)
        }
        TyKind::RigidTy(RigidTy::Ref(_, inner, _)) | TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => {
            extract_fixed_array_len(inner)
        }
        TyKind::RigidTy(RigidTy::Adt(adt_def, args)) => {
            let variants = adt_def.variants();
            if variants.len() == 1 && variants[0].fields().len() == 1 {
                let field_ty = variants[0].fields()[0].ty_with_args(&args);
                extract_fixed_array_len(field_ty)
            } else {
                None
            }
        }
        _ => None,
    }
}

fn build_lexicographic_cmp(lhs: &Expr, rhs: &Expr, len: usize, is_signed: bool) -> Option<Expr> {
    let arr = lhs.sort().array_sort()?;
    if !arr.element_sort.is_bitvec() {
        return None;
    }
    let idx_width = arr.index_sort.bitvec_width()?;
    let neg1 = Expr::bitvec_const(-1i128, 32);
    let pos1 = Expr::bitvec_const(1, 32);

    let mut result = Expr::bitvec_const(0, 32);
    for i in (0..len).rev() {
        let idx = Expr::bitvec_const(i as u64, idx_width);
        let l = lhs.clone().select(idx.clone());
        let r = rhs.clone().select(idx);
        let lt = if is_signed { l.clone().bvslt(r.clone()) } else { l.clone().bvult(r.clone()) };
        let gt = if is_signed { l.bvsgt(r) } else { l.bvugt(r) };
        result = Expr::ite(lt, neg1.clone(), Expr::ite(gt, pos1.clone(), result));
    }
    Some(result)
}

fn build_lexicographic_ord(
    lhs: &Expr,
    rhs: &Expr,
    len: usize,
    method: &str,
    is_signed: bool,
) -> Option<Expr> {
    let cmp = build_lexicographic_cmp(lhs, rhs, len, is_signed)?;
    let zero = Expr::bitvec_const(0i128, 32);
    let neg1 = Expr::bitvec_const(-1i128, 32);
    let pos1 = Expr::bitvec_const(1, 32);
    Some(match method {
        "lt" => cmp.eq(neg1),
        "le" => cmp.clone().eq(neg1).or(cmp.eq(zero)),
        "gt" => cmp.eq(pos1),
        "ge" => cmp.clone().eq(pos1).or(cmp.eq(zero)),
        _ => return None,
    })
}
