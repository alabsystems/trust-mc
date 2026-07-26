// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Type and operand signedness analysis for CHC codegen.
//!
//! Extracted from include!() to proper module via extension trait pattern.
//! Part of #2306: include!() to proper module migration.
//!
//! Instance methods that use `&self` are in the `ExprSignedness` trait.
//! `ty_signedness` and `ty_signedness_for_cast` are module-level `pub(in crate::codegen_ay::chc)`
//! functions; the shared core (`ty_signedness_shallow`, `is_pointer_wrapper_adt`)
//! lives in `codegen_ay::shared` (Part of #2944).

use rustc_public::CrateDef;
use rustc_public::abi::IntegerType;
use rustc_public::mir::{BinOp, LocalDecl, Operand, ProjectionElem, Rvalue};
use rustc_public::ty::{AdtKind, GenericArgKind, RigidTy, TyKind};
use tracing::{trace, warn};

use super::ChcCtx;
use crate::codegen_ay::shared::IntoOption;
// Signedness fallback functions/statics moved to codegen_ay::shared (#2881).
use crate::codegen_ay::shared::{
    SignednessFallbackKind, is_pointer_wrapper_adt, signedness_fallback_with_kind,
    ty_signedness_shallow,
};

/// Determine signedness from operand type with operation-specific fallback.
///
/// `kind` selects the correct fallback semantics when the type is unknown
/// (Part of #3129). Previously all callers got comparison semantics (signed=true),
/// which is incorrect for division, shifts, and casts.
pub(in crate::codegen_ay::chc) fn arg_signedness_or_fallback(
    arg: &Operand,
    locals: &[rustc_public::mir::LocalDecl],
    context: &str,
    kind: SignednessFallbackKind,
) -> bool {
    let operand_ty = match arg {
        Operand::Copy(place) | Operand::Move(place) if place.local >= locals.len() => {
            warn!(
                context,
                local = place.local,
                locals_len = locals.len(),
                "signedness operand local out of bounds; using fallback"
            );
            None
        }
        _ => arg.ty(locals).ok(), // external enum: Operand
    };
    operand_ty
        .and_then(ty_signedness)
        .unwrap_or_else(|| signedness_fallback_with_kind(context, kind))
}

/// Determine signedness for a comparison operand, treating ZST types as unsigned.
///
/// Comparison stubs call this instead of `arg_signedness_or_fallback` directly.
/// ZST types (fieldless structs, empty tuples) have no data to compare, so
/// signedness is irrelevant. Defaulting to unsigned for these types avoids
/// spurious signedness_fallback counts that trigger PROOF demotion.
/// Part of #3248.
pub(in crate::codegen_ay::chc) fn arg_signedness_for_cmp(
    arg: &Operand,
    locals: &[rustc_public::mir::LocalDecl],
) -> bool {
    // Check if the deref'd argument type is a ZST struct.
    if let Ok(ty) = arg.ty(locals) {
        if is_zst_for_signedness(ty) {
            return false; // unsigned — no data to compare
        }
    }
    arg_signedness_or_fallback(arg, locals, "ord_cmp", SignednessFallbackKind::Comparison)
}

/// Check if a type is a ZST for signedness purposes.
/// Returns true for empty tuples and fieldless structs (after Ref deref).
fn is_zst_for_signedness(ty: rustc_public::ty::Ty) -> bool {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Ref(_, ref inner, _) | RigidTy::RawPtr(ref inner, _)) => {
            is_zst_for_signedness(*inner)
        }
        TyKind::RigidTy(RigidTy::Tuple(ref elements)) if elements.is_empty() => true,
        TyKind::RigidTy(RigidTy::Adt(def, _)) => {
            def.kind() == AdtKind::Struct
                && def.variants().first().is_some_and(|v| v.fields().is_empty())
        }
        _ => false,
    }
}

/// Extension trait for signedness analysis instance methods.
pub(in crate::codegen_ay::chc) trait ExprSignedness {
    /// Determine signedness of an operand's type (#666, #672).
    fn operand_signedness(&self, operand: &Operand) -> Option<bool>;
    /// Determine signedness of an operand for cast operations (#2082).
    fn operand_signedness_for_cast(&self, operand: &Operand) -> Option<bool>;
    /// Infer signedness of an rvalue result for local propagation (#1889).
    fn rvalue_signedness(&self, rvalue: &Rvalue) -> Option<bool>;
    /// Update signedness tracking for a local based on an assignment rvalue (#1889).
    fn update_local_signedness_from_rvalue(&mut self, local_idx: usize, rvalue: &Rvalue);
    /// Determine signedness for a binary operation by checking both operands (#1889).
    fn is_signed_integer_op(&self, lhs: &Operand, rhs: &Operand) -> Option<bool>;
}

impl<'tcx, 'body> ExprSignedness for ChcCtx<'tcx, 'body> {
    fn operand_signedness(&self, operand: &Operand) -> Option<bool> {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                let ty = place.ty(self.body.locals()).into_option();
                if let Some(signed) = ty.and_then(ty_signedness) {
                    return Some(signed);
                }

                let mut core_len = place.projection.len();
                while core_len > 0
                    && matches!(place.projection[core_len - 1], ProjectionElem::OpaqueCast(_))
                {
                    core_len -= 1;
                }
                let core_projections = &place.projection[..core_len];
                if let Some(ProjectionElem::Field(_, field_ty)) = core_projections.last()
                    && let Some(signed) = ty_signedness(*field_ty)
                {
                    return Some(signed);
                }

                if core_projections.is_empty() {
                    if let Some(signed) = self.encode.local_signedness.get(&place.local) {
                        return Some(*signed);
                    }
                    let local_ty = self.body.locals()[place.local].ty;
                    return ty_signedness(local_ty);
                }

                None
            }
            Operand::Constant(_) => operand.ty(self.body.locals()).ok().and_then(ty_signedness),
        }
    }

    fn operand_signedness_for_cast(&self, operand: &Operand) -> Option<bool> {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                let ty = place.ty(self.body.locals()).into_option();
                if let Some(signed) = ty.and_then(ty_signedness_for_cast) {
                    return Some(signed);
                }

                let mut core_len = place.projection.len();
                while core_len > 0
                    && matches!(place.projection[core_len - 1], ProjectionElem::OpaqueCast(_))
                {
                    core_len -= 1;
                }
                let core_projections = &place.projection[..core_len];
                if let Some(ProjectionElem::Field(_, field_ty)) = core_projections.last()
                    && let Some(signed) = ty_signedness_for_cast(*field_ty)
                {
                    return Some(signed);
                }

                if core_projections.is_empty() {
                    if let Some(signed) = self.encode.local_signedness.get(&place.local) {
                        return Some(*signed);
                    }
                    let local_ty = self.body.locals()[place.local].ty;
                    return ty_signedness_for_cast(local_ty);
                }

                None
            }
            Operand::Constant(_) => {
                operand.ty(self.body.locals()).ok().and_then(ty_signedness_for_cast)
            }
        }
    }

    fn rvalue_signedness(&self, rvalue: &Rvalue) -> Option<bool> {
        match rvalue {
            Rvalue::Use(operand) => self.operand_signedness(operand),
            Rvalue::BinaryOp(op, lhs, rhs) | Rvalue::CheckedBinaryOp(op, lhs, rhs) => {
                // For shift operations, only the value operand's (LHS) signedness
                // matters; the shift amount may have a different type in MIR.
                if matches!(op, BinOp::Shl | BinOp::ShlUnchecked | BinOp::Shr | BinOp::ShrUnchecked)
                {
                    self.operand_signedness(lhs)
                } else {
                    self.is_signed_integer_op(lhs, rhs)
                }
            }
            Rvalue::UnaryOp(_, operand) => self.operand_signedness(operand),
            Rvalue::Cast(_, _, target_ty) => ty_signedness(*target_ty),
            other => {
                trace!(?other, "CHC: rvalue_signedness - no signedness info for rvalue kind");
                None
            }
        }
    }

    fn update_local_signedness_from_rvalue(&mut self, local_idx: usize, rvalue: &Rvalue) {
        if let Some(signed) = self.rvalue_signedness(rvalue) {
            self.encode.local_signedness.insert(local_idx, signed);
        } else {
            self.encode.local_signedness.remove(&local_idx);
        }
    }

    fn is_signed_integer_op(&self, lhs: &Operand, rhs: &Operand) -> Option<bool> {
        let lhs_signed = self.operand_signedness(lhs);
        let rhs_signed = self.operand_signedness(rhs);

        match (lhs_signed, rhs_signed) {
            (Some(l), Some(r)) if l == r => Some(l),
            (Some(s), None) | (None, Some(s)) => Some(s),
            (Some(l), Some(r)) => {
                trace!(lhs_signed = l, rhs_signed = r, "mixed signedness conflict — falling back");
                None
            }
            _ => None, // non-enum: (Option, Option) tuple exhaustion
        }
    }
}

// --- Free functions for static/associated signedness helpers ---

/// Get signedness of a type (#666).
/// Recurses through pointer types (Ref, RawPtr) and pointer-wrapper ADTs
/// (Box, Unique, NonNull) to find the underlying integer type.
/// Delegates to `ty_signedness_shallow` from `shared.rs` for leaf types.
/// Part of #2944: shared core extraction.
pub(in crate::codegen_ay::chc) fn ty_signedness(ty: rustc_public::ty::Ty) -> Option<bool> {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Ref(_, ref inner, _) | RigidTy::RawPtr(ref inner, _)) => {
            ty_signedness(*inner)
        }
        TyKind::RigidTy(RigidTy::Adt(def, ref args)) => {
            let name = def.name();
            if is_pointer_wrapper_adt(&name)
                && let Some(GenericArgKind::Type(inner_ty)) = args.0.first()
            {
                return ty_signedness(*inner_ty);
            }
            // Fixes #3262: enum ADTs check repr type for signedness.
            // `#[repr(i8)]`, `#[repr(i16)]`, etc. use signed discriminants
            // (e.g., Ordering: Less=-1, Equal=0, Greater=1). Default enums
            // without explicit signed repr use unsigned discriminants
            // (sequential 0..N-1 in CHC encoding, Part of #3248).
            if def.kind() == AdtKind::Enum {
                let is_signed_repr = matches!(
                    def.repr().int,
                    Some(IntegerType::Fixed { is_signed: true, .. })
                        | Some(IntegerType::Pointer { is_signed: true })
                );
                return Some(is_signed_repr);
            }
            // Part of #3041: struct ADTs — fieldless structs (ZSTs) have no data,
            // so signedness is irrelevant. Defaulting to unsigned prevents spurious
            // signedness_fallback counts in enum_field_coerce and comparison paths.
            // Single-field structs (newtype wrappers) inherit the inner field's
            // signedness. Use `ty_with_args` so generic wrappers like
            // `NonZero<i32>` see the concrete `i32`, not the raw `T`.
            if def.kind() == AdtKind::Struct {
                if let Some(variant) = def.variants().first() {
                    let fields = variant.fields();
                    if fields.is_empty() {
                        return Some(false); // ZST — no data to compare
                    }
                    if fields.len() == 1 {
                        if let Some(inner) = ty_signedness(fields[0].ty_with_args(args)) {
                            return Some(inner);
                        }
                    }
                    // Part of #3690: multi-field structs have no inherent sign
                    // semantics when encoded as BV. Default to unsigned.
                    return Some(false);
                }
            }
            ty_signedness_shallow(ty)
        }
        // Part of #3690: arrays inherit element signedness.
        TyKind::RigidTy(RigidTy::Array(ref elem_ty, _)) => ty_signedness(*elem_ty),
        // Part of #3806: slices inherit element signedness (analogous to arrays).
        TyKind::RigidTy(RigidTy::Slice(ref elem_ty)) => ty_signedness(*elem_ty),
        // Part of #3248: empty tuple () has no data — signedness is irrelevant.
        TyKind::RigidTy(RigidTy::Tuple(ref elements)) if elements.is_empty() => Some(false),
        TyKind::RigidTy(RigidTy::Tuple(ref elements)) if !elements.is_empty() => {
            ty_signedness(elements[0])
        }
        _ => ty_signedness_shallow(ty), // external enum: TyKind
    }
}

/// Get signedness of a type for cast operations (#2082).
/// Does NOT recurse into pointer types — pointers are unsigned addresses.
pub(in crate::codegen_ay::chc) fn ty_signedness_for_cast(ty: rustc_public::ty::Ty) -> Option<bool> {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Ref(_, _, _) | RigidTy::RawPtr(_, _)) => Some(false),
        TyKind::RigidTy(RigidTy::Adt(def, _args)) => {
            let name = def.name();
            if is_pointer_wrapper_adt(&name) {
                return Some(false);
            }
            // Part of #3262: enum ADTs with signed repr need signed extension
            // in width-changing casts (e.g., Ordering::Less as i32 must
            // sign-extend 0xFF → 0xFFFFFFFF, not zero-extend → 0x000000FF).
            if def.kind() == AdtKind::Enum {
                let is_signed_repr = matches!(
                    def.repr().int,
                    Some(IntegerType::Fixed { is_signed: true, .. })
                        | Some(IntegerType::Pointer { is_signed: true })
                );
                return Some(is_signed_repr);
            }
            ty_signedness_shallow(ty)
        }
        _ => ty_signedness_shallow(ty), // external enum: TyKind
    }
}

/// Infer signedness for a binary operation in inline translation contexts.
///
/// Replicates the three-level inference from the main codegen path
/// (`codegen_stmt_rvalue.rs:56-97`) for use in virtual inline, closure inline,
/// and quantifier closure paths:
///
/// 1. **Shift ops** (Shl, Shr, etc.): LHS-only signedness — the shift amount
///    often has a different type in MIR (e.g., `u32 << i32`).
/// 2. **Non-shift ops**: check both operands, resolve conflicts (one known +
///    one unknown → use known; both known but disagree → None).
/// 3. **Div/Rem with unknown signedness**: fall back to destination local's MIR
///    type, which preserves integer type identity in Rust MIR.
///
/// Part of #3246: ensures inline paths use the same inference as the main path.
pub(in crate::codegen_ay::chc) fn infer_inline_binop_signedness(
    op: BinOp,
    lhs: &Operand,
    rhs: &Operand,
    locals: &[LocalDecl],
    dest_local: Option<usize>,
) -> Option<bool> {
    // Part of #4030: raw pointer comparisons are unsigned (addresses).
    // Mirrors operand_is_raw_pointer_like in codegen_stmt_rvalue_binop.rs.
    let is_raw_ptr_like = |operand: &Operand| -> bool {
        fn ty_is_raw_pointer_like(ty: rustc_public::ty::Ty) -> bool {
            match ty.kind() {
                TyKind::RigidTy(RigidTy::RawPtr(..)) => true,
                TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => ty_is_raw_pointer_like(inner),
                _ => false,
            }
        }
        operand.ty(locals).ok().is_some_and(ty_is_raw_pointer_like)
    };
    if is_raw_ptr_like(lhs) && is_raw_ptr_like(rhs) {
        return Some(false);
    }

    // Part of #4030: use full ty_signedness (with Ref/RawPtr/ADT recursion)
    // instead of ty_signedness_shallow. The shallow variant returns None for
    // Ref/RawPtr types, causing spurious signedness_fallback increments that
    // demote valid PROOFs. The main codegen path (codegen_stmt_rvalue_binop.rs)
    // uses the full ty_signedness via operand_signedness(); the inline path
    // must match to avoid encoding divergence.
    let operand_signed =
        |operand: &Operand| -> Option<bool> { operand.ty(locals).ok().and_then(ty_signedness) };

    // 1. Shift ops: only the value operand's (LHS) signedness matters.
    let inferred =
        if matches!(op, BinOp::Shl | BinOp::ShlUnchecked | BinOp::Shr | BinOp::ShrUnchecked) {
            operand_signed(lhs)
        } else {
            // 2. Non-shift ops: check both operands.
            let lhs_signed = operand_signed(lhs);
            let rhs_signed = operand_signed(rhs);
            match (lhs_signed, rhs_signed) {
                (Some(l), Some(r)) if l == r => Some(l),
                (Some(s), None) | (None, Some(s)) => Some(s),
                (Some(_), Some(_)) => None, // mixed-signedness conflict
                (None, None) => None,
            }
        };

    // 3. Unknown signedness: try destination local's MIR type (Part of #3099).
    // In Rust MIR, arithmetic ops preserve the operand integer type in the
    // destination.
    //
    // Part of #3264 / #3253: skip destination fallback for comparison ops.
    // Their destination is `bool`, and ty_signedness_shallow(bool)
    // returns Some(false) (unsigned), NOT None. For ordered comparisons
    // this is a soundness bug (bvult vs bvslt); for Eq/Ne it causes wrong
    // width coercion (zero-extend vs sign-extend) on mixed-width operands.
    let is_comparison = matches!(
        op,
        BinOp::Lt | BinOp::Le | BinOp::Ge | BinOp::Gt | BinOp::Cmp | BinOp::Eq | BinOp::Ne
    );
    if inferred.is_none() && !is_comparison {
        if let Some(dest_signed) = dest_local
            .and_then(|idx| locals.get(idx))
            .and_then(|local_decl| ty_signedness(local_decl.ty))
        {
            return Some(dest_signed);
        }
    }

    inferred
}
