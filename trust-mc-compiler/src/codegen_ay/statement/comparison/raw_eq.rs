// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Comparison fragment: raw_eq and ZST helpers.
// Converted from include!() to module for #2306.

use crate::codegen_ay::types::{POINTER_WIDTH, bool_sort};
use ay_bindings::Expr;
use rustc_public::mir::{BasicBlockIdx, Operand, Place};
use rustc_public::ty::{RigidTy, TyKind};
use tracing::{debug, warn};

use super::super::{IntoOption, StatementCodegen};

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Codegen raw_eq intrinsic - byte-wise equality comparison.
    ///
    /// Used by std library for array equality comparison (core::array::equality).
    /// Signature: `raw_eq<T>(a: &T, b: &T) -> bool`
    ///
    /// For ZST (zero-sized types) and zero-length arrays, always returns true
    /// since there are no bytes to compare.
    /// For non-ZST, uses SMT equality on the underlying values.
    ///
    /// Part of #408: ZST array verification.
    ///
    /// REQUIRES: args.len() >= 2
    /// ENSURES: destination gets boolean result of byte-wise equality
    pub(in crate::codegen_ay::statement) fn codegen_raw_eq(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.len() < 2 {
            return None;
        }

        // raw_eq takes &T references, get the underlying values
        let lhs_resolved = self.get_value_through_ref_source(&args[0]);
        let rhs_resolved = self.get_value_through_ref_source(&args[1]);
        let lhs_source = lhs_resolved.as_ref().map(|(_, source)| *source);
        let rhs_source = rhs_resolved.as_ref().map(|(_, source)| *source);
        let lhs = lhs_resolved.map(|(expr, _)| expr);
        let rhs = rhs_resolved.map(|(expr, _)| expr);

        debug!(
            "codegen_raw_eq: lhs={:?}, rhs={:?}",
            lhs.as_ref().map(ay_bindings::Expr::sort),
            rhs.as_ref().map(ay_bindings::Expr::sort)
        );

        // Check if this is a ZST comparison by examining the type
        // ZST cases: zero-length arrays, unit type arrays, or unit type itself
        let is_zst = self.is_raw_eq_zst(&args[0]);

        // Did the dereference actually happen? (#409)
        //
        // Address-vs-value: this was a deref-identity guess — "the result is
        // pointer-width, so we got the pointer, not the value" — and it is wrong
        // in both directions. `&[u64; 1]` / `&usize` dereference to a
        // legitimately 64-bit VALUE and were demoted here for no reason, while an
        // array modeled through typed memory can hand back its base ADDRESS from
        // a path the width cannot see.
        //
        // `get_value_through_ref` now REPORTS which lane produced the result, so
        // for three of its four lanes the question is answered by the producer
        // instead of re-derived here:
        //
        //   * `Value`      — the pointee's own SSA value. The deref happened; the
        //                    64-bit `&usize` case is no longer demoted.
        //   * `Reference`  — the fallback returned the reference's own pointer.
        //                    The deref did NOT happen, whatever width it is.
        //   * `Unreported` — `codegen_place` on `*place`, whose typed-memory
        //                    array lane may return a base address without saying
        //                    so. THIS lane keeps the old width test verbatim: it
        //                    is the residual guess, and it is confined to the one
        //                    producer that still cannot report (queue waves 6/12,
        //                    `docs/addr-vs-value-conversion-queue.md`).
        //
        // The `either_is_array_ref` premise below is unchanged, so no operand
        // shape is newly demoted outside the array-reference case this check has
        // always been about.
        let deref_failed = match (&lhs, &rhs) {
            (Some(l), Some(r)) => {
                use crate::codegen_ay::statement::codegen_place_value::RefValueSource;
                let returned_the_reference = lhs_source == Some(RefValueSource::Reference)
                    || rhs_source == Some(RefValueSource::Reference);
                let lane_cannot_report = lhs_source == Some(RefValueSource::Unreported)
                    || rhs_source == Some(RefValueSource::Unreported);
                let residual_width_guess = lane_cannot_report
                    && l.sort().is_bitvec()
                    && l.sort().bitvec_width() == Some(POINTER_WIDTH)
                    && r.sort().is_bitvec();
                let got_pointer_not_value = returned_the_reference || residual_width_guess;
                // Helper: check if operand is a reference/pointer to array
                let is_array_ref_or_ptr = |operand: &Operand| -> bool {
                    match operand {
                        Operand::Copy(place) | Operand::Move(place) => {
                            place.ty(self.body.locals()).into_option().is_some_and(|ty| {
                                match ty.kind() {
                                    // Handle references: &[T; N] or &mut [T; N]
                                    TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => {
                                        matches!(inner.kind(), TyKind::RigidTy(RigidTy::Array(..)))
                                    }
                                    // Handle raw pointers: *const [T; N] or *mut [T; N]
                                    TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => {
                                        matches!(inner.kind(), TyKind::RigidTy(RigidTy::Array(..)))
                                    }
                                    _ => false, // external enum: TyKind
                                }
                            })
                        }
                        Operand::Constant(_) => false,
                    }
                };
                // Check both operands - either being an array ref indicates deref failure
                let either_is_array_ref =
                    is_array_ref_or_ptr(&args[0]) || is_array_ref_or_ptr(&args[1]);
                got_pointer_not_value && either_is_array_ref
            }
            _ => false, // non-enum: tuple (Option, Option) — covers None variants
        };

        let eq_result = if is_zst {
            // ZST comparison always returns true - no bytes to compare
            debug!("codegen_raw_eq: ZST detected, returning true");
            Expr::bool_const(true)
        } else if deref_failed {
            // Failed to dereference array references - emit unsupported and use symbolic result (#409)
            warn!("codegen_raw_eq: failed to dereference array references, using symbolic result");
            self.ctx.unsupported_with_fallback(
                "raw_eq array dereference",
                "Cannot dereference array references for raw_eq comparison",
            );
            let sym_name = self.ctx.fresh_name("ay_raw_eq_unresolved");

            self.ctx.declare_var(&sym_name, bool_sort())
        } else if let (Some(lhs_expr), Some(rhs_expr)) = (lhs, rhs) {
            // #703: Check for sort mismatch before comparison
            // #1043: Allow Int/BitVec mixed comparisons (BigInt types)
            if lhs_expr.sort() != rhs_expr.sort() {
                let both_bitvec = lhs_expr.sort().is_bitvec() && rhs_expr.sort().is_bitvec();
                let int_bitvec_mix = (lhs_expr.sort().is_int() || rhs_expr.sort().is_int())
                    && (lhs_expr.sort().is_int() || lhs_expr.sort().is_bitvec())
                    && (rhs_expr.sort().is_int() || rhs_expr.sort().is_bitvec());
                if both_bitvec {
                    // Both bitvecs - coerce widths.
                    // raw_eq compares raw byte representations (bit patterns),
                    // so signedness is irrelevant — always zero-extend.
                    // Part of #2773: was incorrectly using operand_signedness.
                    let (lhs_coerced, rhs_coerced) =
                        Self::coerce_to_match_widths_typed(lhs_expr, rhs_expr, false);
                    lhs_coerced.eq(rhs_coerced)
                } else if int_bitvec_mix {
                    // Int/BitVec mix - convert to Int.
                    // raw_eq compares raw byte representations — always use
                    // unsigned bv2int so MSB=1 maps to the positive bit-pattern
                    // value, not a negative integer.
                    // Part of #2773: was incorrectly using signed bv2int for
                    // signed types, causing e.g. i8 0xFF to become -1 instead
                    // of 255, breaking comparison with Int 255.
                    let lhs_int =
                        if lhs_expr.sort().is_int() { lhs_expr } else { lhs_expr.bv2int() };
                    let rhs_int =
                        if rhs_expr.sort().is_int() { rhs_expr } else { rhs_expr.bv2int() };
                    lhs_int.eq(rhs_int)
                } else {
                    warn!(
                        lhs_sort = ?lhs_expr.sort(),
                        rhs_sort = ?rhs_expr.sort(),
                        "codegen_raw_eq: sort mismatch, using symbolic result"
                    );
                    let sym_name = self.ctx.fresh_name("ay_raw_eq_sort_mismatch");
                    self.ctx.declare_var(&sym_name, bool_sort())
                }
            } else if lhs_expr.sort().is_bitvec() && rhs_expr.sort().is_bitvec() {
                // Non-ZST same-sort bitvecs: use SMT equality.
                // raw_eq compares bit patterns — always zero-extend.
                // Part of #2773.
                let (lhs_coerced, rhs_coerced) =
                    Self::coerce_to_match_widths_typed(lhs_expr, rhs_expr, false);
                lhs_coerced.eq(rhs_coerced)
            } else {
                // For arrays, datatypes, etc. - direct equality (sorts match)
                lhs_expr.eq(rhs_expr)
            }
        } else {
            // Couldn't resolve values - return symbolic bool (conservative)
            debug!("codegen_raw_eq: couldn't resolve values, using symbolic bool");
            let sym_name = self.ctx.fresh_name("ay_raw_eq_result");
            let symbolic_result = self.ctx.declare_var(&sym_name, bool_sort());
            self.bind_ssa_result(destination, symbolic_result);
            return target;
        };

        self.bind_ssa_result(destination, eq_result);

        target
    }

    /// Check if a raw_eq operand refers to a ZST (zero-sized type).
    ///
    /// Returns true for:
    /// - Zero-length arrays `[T; 0]`
    /// - Arrays of unit type `[(); N]`
    /// - Unit type `()`
    pub(in crate::codegen_ay::statement) fn is_raw_eq_zst(&self, operand: &Operand) -> bool {
        let ty = match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                place.ty(self.body.locals()).into_option()
            }
            Operand::Constant(c) => Some(c.ty()),
        };

        let Some(ty) = ty else { return false };

        // Dereference if this is a reference type (raw_eq takes references)
        let inner_ty = match ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) => pointee,
            TyKind::RigidTy(RigidTy::RawPtr(pointee, _)) => pointee,
            _ => ty, // external enum: TyKind
        };

        match inner_ty.kind() {
            // Zero-length array: [T; 0]
            TyKind::RigidTy(RigidTy::Array(elem, len)) => {
                if let Some(n) = len.eval_target_usize().into_option()
                    && n == 0
                {
                    return true;
                }
                // Check if element type is ZST (e.g., [(); 10])
                Self::is_zst_type(elem)
            }
            // Unit type ()
            TyKind::RigidTy(RigidTy::Tuple(tys)) if tys.is_empty() => true,
            _ => false, // external enum: TyKind
        }
    }

    /// Check if a type is a zero-sized type (ZST).
    ///
    /// Currently handles:
    /// - Unit type `()`
    /// - Zero-length arrays `[T; 0]`
    /// - Arrays of ZST elements `[(); N]`
    /// - Fieldless structs like `struct Marker;`
    /// - Never type `!`
    ///
    /// Note: This still does NOT handle general all-ZST structs or PhantomData-only
    /// wrappers; it only handles the fieldless-struct case needed by current BMC
    /// coroutine regressions.
    pub(in crate::codegen_ay::statement) fn is_zst_type(ty: rustc_public::ty::Ty) -> bool {
        match ty.kind() {
            // Unit type ()
            TyKind::RigidTy(RigidTy::Tuple(tys)) if tys.is_empty() => true,
            // Zero-length array [T; 0] or array of ZST elements [(); N]
            TyKind::RigidTy(RigidTy::Array(elem_ty, len)) => {
                // Zero-length array is ZST
                if len.eval_target_usize().into_option() == Some(0) {
                    return true;
                }
                // Array of ZST elements is also ZST
                Self::is_zst_type(elem_ty)
            }
            // Never type ! (also ZST but uninhabited)
            TyKind::RigidTy(RigidTy::Never) => true,
            // Fieldless structs like `struct Marker;`
            TyKind::RigidTy(RigidTy::Adt(def, _))
                if def.kind() == rustc_public::ty::AdtKind::Struct
                    && def
                        .variants()
                        .first()
                        .is_some_and(|variant| variant.fields().is_empty()) =>
            {
                true
            }
            _ => false, // external enum: TyKind
        }
    }

    /// Clone::clone for primitives (Part of #1240, #502). Identity copy.
    pub(in crate::codegen_ay::statement) fn codegen_primitive_clone(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.is_empty() {
            return None;
        }
        let value = self.get_value_through_ref(&args[0])?;
        debug!("codegen_primitive_clone: value.sort={:?}", value.sort());
        self.assign_value_to_place(destination, value);
        target
    }
}
