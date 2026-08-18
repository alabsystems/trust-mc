// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Raw pointer comparison and ordering for inline known calls.
//!
//! Extracted from `inline_known_calls.rs` — Part of #4206.

use ay_bindings::Expr;
use rustc_public::mir::{LocalDecl, Operand};
use rustc_public::ty::{RigidTy, TyKind};

use super::ChcCtx;
use crate::codegen_ay::provenance::{Loc, Val};
use crate::codegen_ay::ptr_repr::PtrRepr;

pub(super) fn operand_is_raw_pointer_like(operand: &Operand, caller_locals: &[LocalDecl]) -> bool {
    fn ty_is_raw_pointer_like(ty: rustc_public::ty::Ty) -> bool {
        match ty.kind() {
            TyKind::RigidTy(RigidTy::RawPtr(..)) => true,
            TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => ty_is_raw_pointer_like(inner),
            _ => false,
        }
    }

    operand.ty(caller_locals).ok().is_some_and(ty_is_raw_pointer_like)
}

pub(super) fn inline_plain_eq_expr(is_eq: bool, translated_args: &[Expr]) -> Option<Expr> {
    if translated_args.len() != 2 {
        return None;
    }
    let lhs = translated_args.first()?.clone();
    let rhs = translated_args.get(1)?.clone();
    if lhs.sort() != rhs.sort() {
        return None;
    }
    let sort = lhs.sort();
    if !(sort.is_bool() || sort.is_int() || sort.is_bitvec() || sort.datatype_name().is_some()) {
        return None;
    }
    Some(if is_eq { lhs.eq(rhs) } else { lhs.ne(rhs) })
}

pub(super) fn inline_raw_pointer_cmp_expr(method: &str, translated_args: &[Expr]) -> Option<Expr> {
    let lhs = translated_args.first()?.clone();
    let rhs = translated_args.get(1).cloned();
    match method {
        "cmp" if translated_args.len() == 2 => raw_pointer_cmp_from_exprs(&lhs, rhs.as_ref()?),
        "eq" if translated_args.len() == 2 => {
            Some(raw_pointer_cmp_from_exprs(&lhs, rhs.as_ref()?)?.eq(Expr::bitvec_const(0, 32)))
        }
        "ne" if translated_args.len() == 2 => {
            Some(raw_pointer_cmp_from_exprs(&lhs, rhs.as_ref()?)?.ne(Expr::bitvec_const(0, 32)))
        }
        "lt" | "le" | "gt" | "ge" if translated_args.len() == 2 => {
            raw_pointer_ord_pred(method, &lhs, rhs.as_ref()?)
        }
        "min" | "max" if translated_args.len() == 2 => {
            let keep_lhs = raw_pointer_ord_pred(
                if method == "min" { "le" } else { "ge" },
                &lhs,
                rhs.as_ref()?,
            )?;
            Some(Expr::ite(keep_lhs, lhs, rhs?))
        }
        "clamp" if translated_args.len() == 3 => {
            let max_expr = translated_args.get(2)?.clone();
            let range_ok = raw_pointer_ord_pred("le", rhs.as_ref()?, &max_expr)?;
            let lt_min = raw_pointer_ord_pred("lt", &lhs, rhs.as_ref()?)?;
            let gt_max = raw_pointer_ord_pred("gt", &lhs, &max_expr)?;
            let clamped = Expr::ite(lt_min, rhs?, Expr::ite(gt_max, max_expr, lhs.clone()));
            // Part of #4030: nested inline callers only propagate panic/assert
            // conditions when the fallback matches the `__assert_fail_inline*`
            // naming contract consumed by extract_inline_assert_guard().
            // Using an arbitrary pending var here leaves bad clamp bounds as
            // unconstrained data instead of a failing guard, which produces SAT
            // counterexamples in ptr-comparison helpers that rely on `Ord::clamp`.
            let fallback = super::declare_pending_var(
                super::chc_fresh_name("__assert_fail_inline_raw_ptr_clamp"),
                lhs.sort().clone(),
            );
            Some(Expr::ite(range_ok, clamped, fallback))
        }
        _ => None,
    }
}

fn raw_pointer_ord_pred(method: &str, lhs: &Expr, rhs: &Expr) -> Option<Expr> {
    let cmp = raw_pointer_cmp_from_exprs(lhs, rhs)?;
    let less = Expr::bitvec_const(-1i128, 32);
    let greater = Expr::bitvec_const(1, 32);
    match method {
        "lt" => Some(cmp.eq(less)),
        "le" => Some(cmp.ne(greater)),
        "gt" => Some(cmp.eq(greater)),
        "ge" => Some(cmp.ne(less)),
        _ => None,
    }
}

fn raw_pointer_cmp_from_exprs(lhs: &Expr, rhs: &Expr) -> Option<Expr> {
    let (lhs_ptr, lhs_meta) = raw_pointer_components(lhs)?;
    let (rhs_ptr, rhs_meta) = raw_pointer_components(rhs)?;
    raw_pointer_cmp_from_components(lhs_ptr, lhs_meta, rhs_ptr, rhs_meta)
}

/// Splits a raw-pointer operand into its address and (optional) metadata.
///
/// Wave 4 of the address-vs-value conversion: the two halves have different
/// provenance, so they get different types — `Loc` for the address, `Val` for
/// the metadata — and no signature downstream can transpose them.
///
/// The `width == POINTER_WIDTH` / `width == 2 * POINTER_WIDTH` pair that used to
/// open this function is deleted. The second arm read bits 127..64 as metadata
/// whenever the operand happened to be double-width, which a thin pointer
/// zero-extended into a BV128 slot satisfies exactly as well as a real fat one —
/// and then compared that padding as if it were a slice length. `PtrRepr`
/// separates the two structurally; `WidenedThin` reports no metadata, so the
/// comparison falls back to the address-only lane instead of ordering on
/// fabricated bits.
///
/// The datatype arm is unchanged and reports DECLARED roles: the fields are
/// named `fld_ptr`/`ptr`/`fld_data` and `fld_len`/`fld_vtable`/`fld_meta`.
fn raw_pointer_components(expr: &Expr) -> Option<(Loc, Option<Val>)> {
    if let Some(repr) = PtrRepr::classify(expr) {
        return Some(repr.into_parts());
    }

    let dt = expr.sort().datatype_sort()?;
    let cons = dt.constructors.first()?;
    let ptr_field = cons.fields.iter().find(|field| {
        (field.name == "fld_ptr" || field.name == "ptr" || field.name == "fld_data")
            && field.sort.is_bitvec()
    })?;
    let ptr = Loc::of_address(expr.clone().field_select(
        &dt.name,
        &ptr_field.name,
        ptr_field.sort.clone(),
    ));
    let metadata = cons
        .fields
        .iter()
        .find(|field| {
            (field.name == "fld_len" || field.name == "fld_vtable" || field.name == "fld_meta")
                && field.sort.is_bitvec()
        })
        .map(|field| {
            Val::of_value(expr.clone().field_select(&dt.name, &field.name, field.sort.clone()))
        });
    Some((ptr, metadata))
}

fn raw_pointer_cmp_from_components(
    lhs_ptr: Loc,
    lhs_meta: Option<Val>,
    rhs_ptr: Loc,
    rhs_meta: Option<Val>,
) -> Option<Expr> {
    let (lhs_ptr, rhs_ptr) = (lhs_ptr.into_expr(), rhs_ptr.into_expr());
    let ptr_width = ChcCtx::max_bitvec_width(&lhs_ptr, &rhs_ptr)?;
    let lhs_ptr_width = lhs_ptr.sort().bitvec_width()?;
    let rhs_ptr_width = rhs_ptr.sort().bitvec_width()?;
    let lhs_ptr = lhs_ptr.zero_extend(ptr_width.saturating_sub(lhs_ptr_width));
    let rhs_ptr = rhs_ptr.zero_extend(ptr_width.saturating_sub(rhs_ptr_width));
    let ptr_lt = lhs_ptr.clone().bvult(rhs_ptr.clone());
    let ptr_eq = lhs_ptr.eq(rhs_ptr);
    let tie_cmp = match (lhs_meta, rhs_meta) {
        (None, None) => Expr::bitvec_const(0, 32),
        (Some(lhs_meta), Some(rhs_meta)) => {
            let (lhs_meta, rhs_meta) = (lhs_meta.into_expr(), rhs_meta.into_expr());
            let meta_width = ChcCtx::max_bitvec_width(&lhs_meta, &rhs_meta)?;
            let lhs_meta_width = lhs_meta.sort().bitvec_width()?;
            let rhs_meta_width = rhs_meta.sort().bitvec_width()?;
            let lhs_meta = lhs_meta.zero_extend(meta_width.saturating_sub(lhs_meta_width));
            let rhs_meta = rhs_meta.zero_extend(meta_width.saturating_sub(rhs_meta_width));
            let meta_lt = lhs_meta.clone().bvult(rhs_meta.clone());
            let meta_eq = lhs_meta.eq(rhs_meta);
            Expr::ite(
                meta_lt,
                Expr::bitvec_const(-1i128, 32),
                Expr::ite(meta_eq, Expr::bitvec_const(0, 32), Expr::bitvec_const(1, 32)),
            )
        }
        _ => return None,
    };

    Some(Expr::ite(
        ptr_lt,
        Expr::bitvec_const(-1i128, 32),
        Expr::ite(ptr_eq, tie_cmp, Expr::bitvec_const(1, 32)),
    ))
}
