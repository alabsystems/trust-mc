// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Operand translation for AY codegen.
//!
//! This module handles MIR Operand translation to AY expressions:
//! - Copy/Move operands: dispatches to place translation
//! - Constant operands: extracts scalar values from allocations
//!
//! Scalar extraction from allocations is in operand_scalar.rs.
//! Reference/provenance following is in operand_ref.rs.

use super::{
    ConstOperand, ConstantKind, Expr, LayoutOf, MirConst, Operand, RigidTy, SortInner,
    StatementCodegen, TyConstKind, TyKind,
};
use crate::codegen_ay::types::POINTER_WIDTH;
use std::sync::atomic::{AtomicUsize, Ordering};
use tracing::{debug, warn};

/// Global statement-level counter for constant zero-value fallbacks (#2463).
///
/// `codegen_constant` is immutable (`&self`), so this counter mirrors other
/// static fallback metrics that cannot use per-instance mutable state.
static CONSTANT_ZERO_FALLBACK_COUNT: AtomicUsize = AtomicUsize::new(0);

fn record_constant_zero_fallback() {
    CONSTANT_ZERO_FALLBACK_COUNT.fetch_add(1, Ordering::Relaxed);
}

pub(in crate::codegen_ay) fn take_constant_zero_fallback_count() -> usize {
    CONSTANT_ZERO_FALLBACK_COUNT.swap(0, Ordering::Relaxed)
}

/// Non-destructive read of the constant zero fallback counter (Part of #3080).
pub(in crate::codegen_ay) fn get_constant_zero_fallback_count() -> usize {
    CONSTANT_ZERO_FALLBACK_COUNT.load(Ordering::Relaxed)
}

#[cfg(test)]
pub(in crate::codegen_ay) fn set_constant_zero_fallback_count_for_test(count: usize) {
    CONSTANT_ZERO_FALLBACK_COUNT.store(count, Ordering::Relaxed);
}

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Translate a MIR Operand into a AY expression.
    ///
    /// Dispatches to codegen_place for Copy/Move, codegen_constant for Constants.
    ///
    /// REQUIRES: operand is a valid operand from self.body
    /// ENSURES: Returns Some(expr) with expr.sort() matching operand type
    /// ENSURES: Returns None if operand cannot be translated
    pub(super) fn codegen_operand(&mut self, operand: &Operand) -> Option<Expr> {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => self.codegen_place(place),
            Operand::Constant(constant) => self
                .codegen_constant(constant)
                .or_else(|| self.codegen_uninit_const_arbitrary(constant)),
        }
    }

    /// A `MaybeUninit<T>` constant is UNINITIALIZED memory — semantically an arbitrary
    /// value of `T`. `codegen_constant` (`&self`) can only zero-fallback for it, which is
    /// UNSOUND (uninit ≠ 0 — it may produce false proofs) and demotes the verdict; it now
    /// returns `None` for MaybeUninit so this `&mut self` path models it soundly as a
    /// FRESH unconstrained value of the (transparent) inner sort — the universally-
    /// quantified semantics, matching the `MaybeUninit::uninit()` precheck
    /// (dispatch/precheck.rs). Only fires when codegen_constant could not extract a value.
    fn codegen_uninit_const_arbitrary(&mut self, constant: &ConstOperand) -> Option<Expr> {
        let ty = constant.const_.ty();
        let TyKind::RigidTy(RigidTy::Adt(def, _)) = ty.kind() else {
            return None;
        };
        if !def.0.name().contains("MaybeUninit") {
            return None;
        }
        let sort = Self::infer_sort_from_ty(ty)?;
        let name = self.ctx.fresh_name("maybe_uninit_const");
        Some(self.ctx.declare_var(&name, sort))
    }

    /// Translate a MIR constant into a AY expression.
    ///
    /// Extracts scalar values (bool, int, uint) from the MIR constant's allocation bytes.
    /// For unsupported constant kinds, falls back to a zero value for primitive sorts
    /// (Bool, BitVec, Int). Returns None for compound sorts (Array, Datatype) or when
    /// the type's sort cannot be inferred.
    ///
    /// REQUIRES: constant is a valid constant operand from MIR
    /// ENSURES: On Some, result.sort() matches constant's type
    /// ENSURES: On None, constant could not be translated (unsupported kind/sort)
    fn codegen_constant(&self, constant: &ConstOperand) -> Option<Expr> {
        let mir_const = &constant.const_;
        let ty = mir_const.ty();

        debug!("codegen_constant: ty={:?}, kind={:?}", ty.kind(), mir_const.kind());

        // Try to extract the scalar value from the constant
        let extracted = match mir_const.kind() {
            ConstantKind::Allocated(alloc) => self.codegen_scalar_from_alloc(alloc, ty),
            ConstantKind::Ty(ty_const) => match ty_const.kind() {
                TyConstKind::Value(value_ty, alloc) => {
                    debug!("codegen_constant: TyConstKind::Value value_ty={:?}", value_ty.kind());
                    self.codegen_scalar_from_alloc(alloc, *value_ty)
                }
                // ZSTs carry zero bits of information — any value is
                // semantically correct. Produce canonical value directly
                // to avoid false constant_zero_fallback counts that cause
                // PROOF demotion. Matches CHC path (codegen_expr_constant.rs:53).
                // Part of #3094.
                TyConstKind::ZSTValue(_) => Some(Expr::bool_const(true)),
                TyConstKind::Bound(..) | TyConstKind::Param(_) | TyConstKind::Unevaluated(..) => {
                    None
                }
            },
            // ZSTs carry zero bits — matches CHC path (codegen_expr_constant.rs:58).
            // Part of #3094.
            ConstantKind::ZeroSized => Some(Expr::bool_const(true)),
            ConstantKind::Param(_) | ConstantKind::Unevaluated(_) => None,
        };

        debug!("codegen_constant: extracted={:?}", extracted);

        if let Some(expr) = extracted {
            return Some(expr);
        }

        // Part of #3094: For constant references, follow provenance to extract
        // the pointee value. Without this, Ref types fall through to the
        // zero-value fallback, causing incorrect discriminant values and PROOF demotion.
        if let TyKind::RigidTy(RigidTy::Ref(_, pointee_ty, _)) = ty.kind() {
            return self.codegen_const_ref(mir_const, pointee_ty);
        }

        // MaybeUninit<T> with no extractable value is UNINITIALIZED memory == an
        // arbitrary value of T. Return None (NOT the unsound zero-fallback) so
        // codegen_operand (&mut self) can model it as a fresh unconstrained value — the
        // sound universally-quantified semantics. Fixing uninit to 0 would demote the
        // proof (and could mask a bug that only triggers on non-zero garbage).
        if let TyKind::RigidTy(RigidTy::Adt(def, _)) = ty.kind() {
            if def.0.name().contains("MaybeUninit") {
                return None;
            }
        }

        // Fallback: create a tracked zero constant only for primitive sorts.
        // Return None for non-primitive sorts to preserve the ENSURES contract.
        let sort = Self::infer_sort_from_ty(ty)?;
        let zero_expr = match sort.inner() {
            SortInner::Bool => Expr::bool_const(false),
            SortInner::BitVec(bv) => Expr::bitvec_const(0, bv.width),
            SortInner::Int => Expr::int_const(0),
            SortInner::Real
            | SortInner::Array(_)
            | SortInner::Datatype(_)
            | SortInner::String
            | SortInner::FloatingPoint(_, _)
            | SortInner::Uninterpreted(_)
            | SortInner::RegLan => return None,
            _ => return None,
        };

        record_constant_zero_fallback();
        warn!(?ty, "codegen_constant: zero-value fallback for unextracted constant");
        Some(zero_expr)
    }

    /// Codegen a constant reference expression (#3094, #3159).
    ///
    /// For ZST pointees (`&()`), returns a non-null sentinel pointer (0x1000).
    /// For sized pointees, follows provenance to extract the pointee value.
    /// Returns None for unextractable references (format strings, `&str`, etc.)
    /// to avoid false zero-value fallback demotion.
    fn codegen_const_ref(
        &self,
        mir_const: &MirConst,
        pointee_ty: rustc_public::ty::Ty,
    ) -> Option<Expr> {
        // Part of #3159: ZST refs have no data to extract via provenance.
        if LayoutOf::new(pointee_ty).size_of() == Some(0) {
            debug!(?pointee_ty, "codegen_const_ref: ZST ref, sentinel pointer");
            return Some(Expr::bitvec_const(0x1000u128, POINTER_WIDTH));
        }
        if let Some(pointee_expr) = self.try_codegen_const_ref_pointee(mir_const, pointee_ty) {
            debug!(?pointee_ty, "codegen_const_ref: extracted pointee via provenance");
            return Some(pointee_expr);
        }
        // &[T] slice constants are fat pointers to element data.
        // Construct a Slice_T datatype expression with concrete element values.
        if let TyKind::RigidTy(RigidTy::Slice(elem_ty)) = pointee_ty.kind() {
            if let Some(slice_expr) = self.try_codegen_const_typed_slice(mir_const, elem_ty) {
                debug!(?pointee_ty, "codegen_const_ref: extracted &[T] as Slice_T");
                return Some(slice_expr);
            }
        }
        // Part of #3189: &str constants are fat pointers to string data.
        // Construct a Slice_bv8 datatype expression with the actual string bytes.
        if let TyKind::RigidTy(RigidTy::Str) = pointee_ty.kind() {
            if let Some(slice_expr) = self.try_codegen_const_str_slice(mir_const) {
                debug!(?pointee_ty, "codegen_const_ref: extracted &str as Slice_bv8");
                return Some(slice_expr);
            }
        }
        // Unextractable references (format strings, etc.) should NOT use
        // the zero-value fallback. Returning None is a sound over-approximation.
        debug!(?pointee_ty, "codegen_const_ref: unextractable Ref, returning None");
        None
    }
}
