// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! BinaryOp / CheckedBinaryOp rvalue translation for CHC statement encoding.
//!
//! Extracted from `codegen_stmt_rvalue.rs` per #3920 to reduce merge-conflict
//! contention on the 968-line parent file.

use std::collections::HashSet;

use ay_bindings::{Expr, ExprValue, Sort};
use rustc_public::mir::{BinOp, Operand, Rvalue};
use rustc_public::ty::{RigidTy, TyKind};
use tracing::{debug, warn};

use crate::codegen_ay::types::{POINTER_WIDTH, ty_to_bv_width};

use super::super::codegen_expr_array_eq::{build_spec_array_eq, recover_spec_array_eq_len};
use super::super::fieldless_constructor_cmp::try_fieldless_constructor_comparison;
use super::ChcCtx;
use super::codegen_ctx::globals::{chc_fresh_name, declare_pending_var};
use super::codegen_expr_signedness::{ExprSignedness, ty_signedness};
use crate::codegen_ay::chc::call::codegen_call_kani_model_dst::is_zst_ty;
use crate::codegen_ay::chc::float_assertion_patterns::{
    should_bypass_float_assertion_sub, try_build_float_assertion_comparison,
};
use crate::codegen_ay::chc::float_fast_math_patterns::{
    try_build_float_fast_math_equiv_comparison, try_build_float_finite_comparison,
};
use crate::codegen_ay::chc::float_roundtrip_patterns::try_build_float_roundtrip_comparison;
use crate::codegen_ay::shared::signedness_fallback_for_binop;

fn operand_is_raw_pointer_like(operand: &Operand, locals: &[rustc_public::mir::LocalDecl]) -> bool {
    fn ty_is_raw_pointer_like(ty: rustc_public::ty::Ty) -> bool {
        match ty.kind() {
            TyKind::RigidTy(RigidTy::RawPtr(..)) => true,
            TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => ty_is_raw_pointer_like(inner),
            _ => false,
        }
    }

    operand.ty(locals).ok().is_some_and(ty_is_raw_pointer_like)
}

/// True when `operand` is a raw pointer / reference whose *pointee* is a
/// zero-sized type. Used to detect ZST address comparisons (see the
/// nondeterminism guard in `translate_rvalue_binop`).
fn operand_pointee_is_zst(operand: &Operand, locals: &[rustc_public::mir::LocalDecl]) -> bool {
    let Ok(ty) = operand.ty(locals) else {
        return false;
    };
    let pointee = match ty.kind() {
        TyKind::RigidTy(RigidTy::RawPtr(inner, _)) | TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => {
            inner
        }
        _ => return false,
    };
    is_zst_ty(pointee)
}

/// True when both operands refer to the exact same MIR place (same local and
/// projection). A ZST pointer compared with itself is trivially equal and must
/// NOT be modeled as nondeterministic.
fn operands_same_place(a: &Operand, b: &Operand) -> bool {
    fn place_of(op: &Operand) -> Option<&rustc_public::mir::Place> {
        match op {
            Operand::Copy(p) | Operand::Move(p) => Some(p),
            Operand::Constant(_) => None,
        }
    }
    match (place_of(a), place_of(b)) {
        (Some(pa), Some(pb)) => pa.local == pb.local && pa.projection == pb.projection,
        _ => false,
    }
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Translate a `BinaryOp` or `CheckedBinaryOp` rvalue.
    ///
    /// Handles signedness inference, float IEEE 754 comparison overrides,
    /// element-wise array equality, and float assertion bypass patterns.
    ///
    /// Part of #3920: extracted from `translate_rvalue_with_modified`.
    pub(in crate::codegen_ay::chc) fn translate_rvalue_binop(
        &mut self,
        rvalue: &Rvalue,
        op: &BinOp,
        lhs_op: &Operand,
        rhs_op: &Operand,
        modified_locals: &HashSet<usize>,
        dest_local: Option<usize>,
    ) -> Option<Expr> {
        let lhs_ty = lhs_op.ty(self.body.locals()).ok()?;

        if matches!(op, BinOp::Offset) {
            return self.translate_pointer_offset_with_modified(lhs_op, rhs_op, modified_locals);
        }

        // Soundness (ZST address-equality nondeterminism): rustc is ALLOWED to
        // place two distinct zero-sized-type locals at the SAME address. Our
        // stack-address model assigns each local a distinct obj_id, so
        // `&a as *const _ == &b as *const _` for ZST-pointee pointers folds to a
        // proven-false constant. That kills any control flow guarded on the
        // addresses coinciding (e.g. `if a == b { null() } else { &z }`), which
        // in turn suppresses the memory-safety obligation that the guarded branch
        // would raise (a null deref). Model the equality of two DISTINCT
        // ZST-pointee pointers as a fresh nondeterministic boolean so BOTH
        // outcomes stay reachable and the downstream obligation fires. Non-ZST
        // pointers and self-comparisons are unaffected. (zst/main.rs missed_bug.)
        if matches!(op, BinOp::Eq | BinOp::Ne)
            && operand_pointee_is_zst(lhs_op, self.body.locals())
            && operand_pointee_is_zst(rhs_op, self.body.locals())
            && !operands_same_place(lhs_op, rhs_op)
        {
            debug!(
                ?op,
                "CHC: modeling ZST-pointee address equality as nondeterministic (zst missed_bug)"
            );
            return Some(declare_pending_var(chc_fresh_name("__zst_addr_eq_nondet"), Sort::bool()));
        }
        // Part of #3875: Element-wise array equality for MIR-inlined spec_eq.
        // rustc can MIR-inline SpecArrayEq::spec_eq, turning it into a BinOp::Eq
        // on [T; N] arrays. Full SMT extensional equality is unsound for finite
        // arrays with symbolic bases (uninitialized indices beyond N may differ).
        // Must intercept before ty_to_bv_width (which returns None for array types).
        if matches!(op, BinOp::Eq | BinOp::Ne) {
            let array_len = recover_spec_array_eq_len(None, Some(lhs_op), self.body.locals());
            if array_len.is_some() {
                let lhs = self.translate_operand_with_modified(lhs_op, modified_locals)?;
                let rhs = self.translate_operand_with_modified(rhs_op, modified_locals)?;
                if let Some(bool_eq) = build_spec_array_eq(&lhs, &rhs, array_len) {
                    let result: Expr =
                        if matches!(op, BinOp::Ne) { bool_eq.not() } else { bool_eq };
                    return Some(result);
                }
            }
        }
        let int_bv_width = match ty_to_bv_width(lhs_ty) {
            Some(width) => width,
            None if matches!(
                op,
                BinOp::Lt | BinOp::Le | BinOp::Ge | BinOp::Gt | BinOp::Cmp | BinOp::Eq | BinOp::Ne
            ) =>
            {
                // Part of #4030: wide raw-pointer comparisons can lower to MIR
                // BinOp::{Eq,Ne,...} inside inlined helper bodies (for example
                // `check_clamp::<[u8]>`). These comparisons operate on pointer
                // expressions, not on integer widths, so do not bail out just
                // because the pointee type has no scalar BV width.
                POINTER_WIDTH
            }
            None => return None,
        };
        let is_float = matches!(lhs_ty.kind(), TyKind::RigidTy(RigidTy::Float(_)));
        if is_float
            && matches!(op, BinOp::Sub | BinOp::SubUnchecked)
            && dest_local.is_some_and(|idx| should_bypass_float_assertion_sub(self, idx))
        {
            return Some(Expr::bitvec_const(0u64, int_bv_width));
        }
        let lhs = self.translate_operand_with_modified(lhs_op, modified_locals)?;
        let rhs = self.translate_operand_with_modified(rhs_op, modified_locals)?;
        if matches!(op, BinOp::Eq | BinOp::Ne)
            && let Some(result) = option_like_datatype_eq(&lhs, &rhs, matches!(op, BinOp::Eq))
        {
            return Some(result);
        }
        if matches!(op, BinOp::Eq | BinOp::Ne)
            && let Some(result) =
                try_fieldless_constructor_comparison(&lhs, &rhs, matches!(op, BinOp::Eq))
        {
            return Some(result);
        }
        let raw_pointer_ordering = operand_is_raw_pointer_like(lhs_op, self.body.locals())
            && operand_is_raw_pointer_like(rhs_op, self.body.locals());
        // Part of #3446: Only detect signedness when at least one operand
        // is a bitvec. Non-bitvec sorts (datatype, int, bool) don't need
        // signedness, and calling signedness detection on non-numeric types
        // triggers spurious signedness_fallback counts that demote valid
        // PROOFs. Mirrors the cmp_handlers.rs gate from #3427.
        let needs_signedness =
            !raw_pointer_ordering && (lhs.sort().is_bitvec() || rhs.sort().is_bitvec());
        // For shift operations, only the value operand's (LHS) signedness matters.
        // The shift amount is often a different type in MIR (e.g., u32 << i32),
        // causing a mixed-signedness conflict that triggers a spurious fallback.
        // For non-shift ops, check both operands (#1889).
        let inferred_signed = if !needs_signedness {
            Some(false) // unused for non-bitvec paths; no fallback recorded
        } else if matches!(op, BinOp::Shl | BinOp::ShlUnchecked | BinOp::Shr | BinOp::ShrUnchecked)
        {
            self.operand_signedness(lhs_op)
        } else {
            self.is_signed_integer_op(lhs_op, rhs_op)
        };
        // Part of #3099: when operand signedness is unknown, try the
        // destination local's MIR type before recording a fallback.
        // In Rust MIR, the destination of arithmetic ops preserves the
        // operand integer type.
        // Part of #3253: skip destination fallback for all comparison ops.
        // Their destination is `bool`, and ty_signedness_shallow(bool)
        // returns Some(false) (unsigned), NOT None. For ordered
        // comparisons this is a soundness bug (bvult vs bvslt); for
        // Eq/Ne it causes wrong width coercion (zero-extend vs
        // sign-extend) on mixed-width operands.
        let is_comparison = matches!(
            op,
            BinOp::Lt | BinOp::Le | BinOp::Ge | BinOp::Gt | BinOp::Cmp | BinOp::Eq | BinOp::Ne
        );
        let inferred_signed = if inferred_signed.is_none() && !is_comparison {
            let dest_signed = dest_local.and_then(|idx| {
                let local_ty = self.body.locals().get(idx)?.ty;
                ty_signedness(local_ty)
            });
            if dest_signed.is_some() {
                debug!(
                    ?op,
                    ?dest_signed,
                    "CHC: signedness resolved from destination type (Part of #3099)"
                );
                dest_signed
            } else if matches!(op, BinOp::Div | BinOp::Rem) {
                // Part of #2749: genuinely unknown signedness on div/rem is high-risk.
                warn!(
                    ?op,
                    "CHC: div/rem with unknown signedness — recording fallback (Part of #2749)"
                );
                self.record_fallback();
                None
            } else {
                None
            }
        } else {
            inferred_signed
        };
        let is_signed = inferred_signed
            .unwrap_or_else(|| signedness_fallback_for_binop(*op, "translate_rvalue_binop"));
        // Part of #3140: IEEE 754 float comparison override.
        // Floats are encoded as unsigned bitvectors, but bvult/bvule is
        // unsound for negative IEEE 754 values. Use sign-aware comparison
        // helpers that correctly handle negative floats and -0.0 == +0.0.
        // Part of #4110: float-to-int round-trip assertion bypass.
        // Detects `(float_to_int_unchecked(f) as Float) == f.trunc()` before
        // operand translation to avoid the full IntToFloat + trunc + float Eq
        // encoding that overwhelms the solver.
        if is_float
            && is_comparison
            && let Some(roundtrip_cmp) =
                try_build_float_roundtrip_comparison(self, *op, lhs_op, rhs_op, modified_locals)
        {
            return Some(roundtrip_cmp);
        }
        if is_float
            && is_comparison
            && let Some(pattern_cmp) =
                try_build_float_assertion_comparison(self, *op, lhs_op, rhs_op, modified_locals)
        {
            return Some(pattern_cmp);
        }
        if is_float
            && is_comparison
            && let Some(finite_cmp) =
                try_build_float_finite_comparison(self, *op, lhs_op, rhs_op, modified_locals)
        {
            return Some(finite_cmp);
        }
        if is_float
            && is_comparison
            && let Some(fast_math_cmp) =
                try_build_float_fast_math_equiv_comparison(self, *op, lhs_op, rhs_op)
        {
            return Some(fast_math_cmp);
        }
        if is_float && is_comparison && lhs.sort().is_bitvec() {
            use crate::codegen_ay::float_compare::{
                bv_float_cmp, bv_float_eq, bv_float_ge, bv_float_gt, bv_float_le, bv_float_lt,
                bv_float_ne,
            };
            let width = int_bv_width;
            let result = match op {
                BinOp::Lt => bv_float_lt(&lhs, &rhs, width),
                BinOp::Le => bv_float_le(&lhs, &rhs, width),
                BinOp::Gt => bv_float_gt(&lhs, &rhs, width),
                BinOp::Ge => bv_float_ge(&lhs, &rhs, width),
                BinOp::Cmp => bv_float_cmp(&lhs, &rhs, width),
                // Part of #3798: use IEEE 754 equality for float Eq/Ne.
                // Raw BV equality (lhs.eq(rhs)) makes `x != x` always false,
                // breaking `f64::is_nan()` (which lowers to `self != self`).
                // This causes `kani::assume(!x.is_nan())` to be vacuous,
                // letting NaN through to ordered comparisons → Genuine CTREX.
                // bv_float_eq/ne handle both NaN (NaN==NaN→false) and
                // ±0.0 (+0.0==-0.0→true), matching Rust IEEE 754 semantics.
                BinOp::Eq => bv_float_eq(&lhs, &rhs, width),
                BinOp::Ne => bv_float_ne(&lhs, &rhs, width),
                _ => {
                    return match rvalue {
                        Rvalue::BinaryOp(_, _, _) => {
                            self.translate_binop(*op, lhs, rhs, is_signed, int_bv_width, is_float)
                        }
                        Rvalue::CheckedBinaryOp(_, _, _) => {
                            self.translate_checked_binop(*op, lhs, rhs, is_signed, int_bv_width)
                        }
                        _ => None,
                    };
                }
            };
            return Some(result);
        }

        match rvalue {
            Rvalue::BinaryOp(_, _, _) => {
                self.translate_binop(*op, lhs, rhs, is_signed, int_bv_width, is_float)
            }
            Rvalue::CheckedBinaryOp(_, _, _) => {
                self.translate_checked_binop(*op, lhs, rhs, is_signed, int_bv_width)
            }
            _ => None, // external enum: Rvalue
        }
    }
}

#[derive(Clone)]
enum OptionLikeView {
    None,
    Some(Expr),
    Symbolic { is_some: Expr, payload: Expr },
}

fn option_like_datatype_eq(lhs: &Expr, rhs: &Expr, is_eq: bool) -> Option<Expr> {
    if lhs.sort() != rhs.sort() || !is_option_like_sort(lhs.sort()) {
        return None;
    }
    let lhs = option_like_view(lhs)?;
    let rhs = option_like_view(rhs)?;
    let eq = option_like_view_eq(lhs, rhs);
    Some(if is_eq { eq } else { eq.not() })
}

fn is_option_like_sort(sort: &Sort) -> bool {
    let Some(dt) = sort.datatype_sort() else {
        return false;
    };
    if dt.constructors.len() != 2 {
        return false;
    }
    let mut arities = dt.constructors.iter().map(|ctor| ctor.fields.len()).collect::<Vec<_>>();
    arities.sort_unstable();
    arities == [0, 1]
}

fn option_like_view(expr: &Expr) -> Option<OptionLikeView> {
    match expr.value() {
        ExprValue::DatatypeConstructor { args, .. } if args.is_empty() => {
            Some(OptionLikeView::None)
        }
        ExprValue::DatatypeConstructor { args, .. } if args.len() == 1 => {
            Some(OptionLikeView::Some(args[0].clone()))
        }
        ExprValue::Ite { cond, then_expr, else_expr } => {
            let then_view = option_like_view(then_expr)?;
            let else_view = option_like_view(else_expr)?;
            match (then_view, else_view) {
                (OptionLikeView::Some(payload), OptionLikeView::None) => {
                    Some(OptionLikeView::Symbolic { is_some: cond.clone(), payload })
                }
                (OptionLikeView::None, OptionLikeView::Some(payload)) => {
                    Some(OptionLikeView::Symbolic { is_some: cond.clone().not(), payload })
                }
                _ => None,
            }
        }
        _ => None,
    }
}

fn option_like_view_eq(lhs: OptionLikeView, rhs: OptionLikeView) -> Expr {
    match (lhs, rhs) {
        (OptionLikeView::None, OptionLikeView::None) => Expr::bool_const(true),
        (OptionLikeView::Some(lhs), OptionLikeView::Some(rhs)) => lhs.eq(rhs),
        (OptionLikeView::None, OptionLikeView::Some(_))
        | (OptionLikeView::Some(_), OptionLikeView::None) => Expr::bool_const(false),
        (OptionLikeView::Symbolic { is_some, payload }, OptionLikeView::Some(expected))
        | (OptionLikeView::Some(expected), OptionLikeView::Symbolic { is_some, payload }) => {
            is_some.and(payload.eq(expected))
        }
        (OptionLikeView::Symbolic { is_some, .. }, OptionLikeView::None)
        | (OptionLikeView::None, OptionLikeView::Symbolic { is_some, .. }) => is_some.not(),
        (
            OptionLikeView::Symbolic { is_some: lhs_is_some, payload: lhs_payload },
            OptionLikeView::Symbolic { is_some: rhs_is_some, payload: rhs_payload },
        ) => {
            let same_discriminant = lhs_is_some.clone().eq(rhs_is_some.clone());
            let same_payload_when_some =
                lhs_is_some.and(rhs_is_some).implies(lhs_payload.eq(rhs_payload));
            same_discriminant.and(same_payload_when_some)
        }
    }
}
