// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Checked binary ops, unary ops, and cast operations.
//!
//! Extracted from codegen_stmt_arithmetic.rs per #2246 to bring it below 500 lines.
//! PtrMetadata Expr resolution moved to `codegen_stmt_ptr_metadata.rs` per #3619 Phase 2.
//! Pure MIR/type trace helpers moved to `codegen_stmt_ptr_metadata_mir_trace.rs` per #3619 Phase 1.
//!
//! Contains:
//! - translate_checked_binop: checked arithmetic with overflow detection
//! - translate_checked_binop_flat: flat (non-tuple) checked arithmetic (#2214)
//! - translate_unop: unary Not/Neg operations
//! - translate_cast: type cast with sign/zero extension (#673)

use std::collections::HashSet;

use ay_bindings::{Expr, Sort, SortInner};
use rustc_public::mir::{BinOp, Operand, UnOp};
use rustc_public::ty::{RigidTy, TyKind};
use tracing::{debug, trace, warn};

use crate::codegen_ay::shared::signedness_fallback_for_cast_or_coerce;
use crate::codegen_ay::types::{POINTER_WIDTH, int_ty_to_bitvec_width, uint_ty_to_bitvec_width};

use super::ChcCtx;
use super::codegen_expr_signedness::ExprSignedness;
use super::codegen_types::CodegenTypes;
use crate::codegen_ay::names::struct_sort;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Core checked binary op: computes (result, overflow) for Add/Sub/Mul/Div/Rem/Shl/Shr.
    ///
    /// Shared by `translate_checked_binop` (tuple output) and
    /// `translate_checked_binop_flat` (flat pair output).
    ///
    /// `is_signed` controls signed vs unsigned overflow semantics (#666).
    /// `int_bv_width`: BV width for Int-to-BV conversions (Part of #3043).
    /// `int_lift`: when true, keep Int operands in Int domain for invariant
    /// synthesis (#112 Direction 2). Overflow detected via Int range checks.
    /// Note: Div/Rem/Shl/Shr fall through to BV path when int_lift is active (Part of #3463).
    fn checked_binop_result_overflow(
        op: BinOp,
        lhs: Expr,
        rhs: Expr,
        is_signed: bool,
        int_bv_width: u32,
        int_lift: bool,
    ) -> Option<(Expr, Expr)> {
        // Part of #112 Direction 2: When int_lift is enabled and both operands
        // are Int, compute in Int domain directly. This produces transition
        // rules like `i' = i + 1` instead of `i' = bv2int(bvadd(int2bv(i), 1))`,
        // enabling PDR to synthesize linear invariants over Int operations.
        if int_lift && (lhs.sort().is_int() || rhs.sort().is_int()) {
            // Part of #3180: Use signed bv2int for signed types to preserve
            // negative value semantics in the Int domain.
            let lhs = if lhs.sort().is_bitvec() {
                if is_signed { lhs.bv2int_signed() } else { lhs.bv2int() }
            } else {
                lhs
            };
            let rhs = if rhs.sort().is_bitvec() {
                if is_signed { rhs.bv2int_signed() } else { rhs.bv2int() }
            } else {
                rhs
            };
            let result = match op {
                BinOp::Add | BinOp::AddUnchecked => lhs.int_add(rhs),
                BinOp::Sub | BinOp::SubUnchecked => lhs.int_sub(rhs),
                BinOp::Mul | BinOp::MulUnchecked => lhs.int_mul(rhs),
                _ => return None,
            };
            // Overflow: result outside BV range.
            // Unsigned: overflow iff result < 0 || result >= 2^w.
            // Signed: overflow iff result < -2^(w-1) || result >= 2^(w-1).
            // Part of #112: Use BigInt to avoid Rust i128 overflow at width=128.
            // `1i128 << 127` wraps to i128::MIN, producing a tautological overflow
            // check that flags ALL i128 checked ops as overflowing (P1:1301).
            let overflow = if is_signed {
                let half = Expr::int_const(num_bigint::BigInt::from(1u128) << (int_bv_width - 1));
                let neg_half =
                    Expr::int_const(-(num_bigint::BigInt::from(1u128) << (int_bv_width - 1)));
                result.clone().int_lt(neg_half).or(result.clone().int_ge(half))
            } else {
                let upper = Expr::int_const(num_bigint::BigInt::from(1u128) << int_bv_width);
                result.clone().int_lt(Expr::int_const(0i128)).or(result.clone().int_ge(upper))
            };
            return Some((result, overflow));
        }

        // Part of #2875, #3043: Coerce Int-lifted operands to BV at MIR-derived width.
        // Checked ops need BV semantics for overflow detection. The result will be
        // coerced back to Int at the assignment boundary by coerce_assignment_rhs_to_sort.
        let (lhs, rhs) = if lhs.sort().is_int() || rhs.sort().is_int() {
            let lhs = if lhs.sort().is_int() { lhs.int2bv(int_bv_width) } else { lhs };
            let rhs = if rhs.sort().is_int() { rhs.int2bv(int_bv_width) } else { rhs };
            (lhs, rhs)
        } else {
            (lhs, rhs)
        };
        // Part of #3889: Both operands must be BV for arithmetic. The inline
        // walker can resolve an operand to an Array sort (e.g., TableauRow's
        // coefficient array) instead of a scalar element — bail out to sound
        // fallback rather than panicking in bvmul/bvadd/etc.
        if !lhs.sort().is_bitvec() || !rhs.sort().is_bitvec() {
            return None;
        }
        let (lhs, rhs) = Self::coerce_arithmetic_operands(lhs, rhs, is_signed);
        let bv_width = lhs.sort().bitvec_width()?;

        if !is_signed
            && matches!(op, BinOp::Add | BinOp::AddUnchecked)
            && bv_width <= 64
            && let (Some(lhs_const), Some(rhs_const)) =
                (Self::try_extract_concrete_usize(&lhs), Self::try_extract_concrete_usize(&rhs))
        {
            let mask = if bv_width == 64 { u64::MAX as u128 } else { (1u128 << bv_width) - 1 };
            let sum = lhs_const as u128 + rhs_const as u128;
            return Some((
                Expr::bitvec_const((sum & mask) as i128, bv_width),
                Expr::bool_const(sum > mask),
            ));
        }

        // Compute the result (wrapping arithmetic).
        // Clone lhs/rhs: originals needed for overflow detection below.
        let result = match op {
            BinOp::Add | BinOp::AddUnchecked => lhs.clone().bvadd(rhs.clone()),
            BinOp::Sub | BinOp::SubUnchecked => lhs.clone().bvsub(rhs.clone()),
            BinOp::Mul | BinOp::MulUnchecked => lhs.clone().bvmul(rhs.clone()),
            BinOp::Div if is_signed => lhs.clone().bvsdiv(rhs.clone()),
            BinOp::Div => lhs.clone().bvudiv(rhs.clone()),
            BinOp::Rem if is_signed => lhs.clone().bvsrem(rhs.clone()),
            BinOp::Rem => lhs.clone().bvurem(rhs.clone()),
            BinOp::Shl => lhs.clone().bvshl(rhs.clone()),
            BinOp::Shr if is_signed => lhs.clone().bvashr(rhs.clone()),
            BinOp::Shr => lhs.clone().bvlshr(rhs.clone()),
            _ => return None, // external enum: BinOp
        };

        // Compute overflow flag based on signedness (#666)
        // Part of #3463: Div/Rem/Shl/Shr overflow conditions for checked_* methods.
        let overflow = match op {
            // Div/Rem: overflow if rhs == 0, or (signed) lhs == T_MIN && rhs == -1.
            BinOp::Div | BinOp::Rem => {
                let zero = Expr::bitvec_const(0u64, bv_width);
                let rhs_zero = rhs.clone().eq(zero);
                if is_signed {
                    let t_min = Expr::bitvec_const(1u128 << (bv_width - 1), bv_width);
                    let neg_one = Expr::bitvec_const(!0u128 >> (128 - bv_width), bv_width);
                    let signed_overflow = lhs.eq(t_min).and(rhs.eq(neg_one));
                    rhs_zero.or(signed_overflow)
                } else {
                    rhs_zero
                }
            }
            // Shl/Shr: overflow if rhs >= bit_width.
            BinOp::Shl | BinOp::Shr => {
                let width_const = Expr::bitvec_const(bv_width as u64, bv_width);
                rhs.bvuge(width_const)
            }
            _ if is_signed => {
                let msb_idx = bv_width - 1;
                // Clone lhs/rhs/result: originals may be needed in Mul arm / return.
                let lhs_sign = lhs.clone().extract(msb_idx, msb_idx);
                let rhs_sign = rhs.clone().extract(msb_idx, msb_idx);
                let result_sign = result.clone().extract(msb_idx, msb_idx);
                match op {
                    BinOp::Add | BinOp::AddUnchecked => {
                        // lhs_sign cloned: needed by result_differs on next line.
                        let same_sign = lhs_sign.clone().eq(rhs_sign);
                        let result_differs = result_sign.eq(lhs_sign).not();
                        same_sign.and(result_differs)
                    }
                    BinOp::Sub | BinOp::SubUnchecked => {
                        // lhs_sign cloned: needed by result_differs on next line.
                        let diff_sign = lhs_sign.clone().eq(rhs_sign).not();
                        let result_differs = result_sign.eq(lhs_sign).not();
                        diff_sign.and(result_differs)
                    }
                    BinOp::Mul | BinOp::MulUnchecked => lhs.bvmul_no_overflow_signed(rhs).not(),
                    _ => unreachable!("guarded by earlier match"), // external enum: BinOp (guarded subset)
                }
            }
            _ => {
                match op {
                    BinOp::Add | BinOp::AddUnchecked => result.clone().bvult(lhs),
                    BinOp::Sub | BinOp::SubUnchecked => lhs.bvult(rhs),
                    BinOp::Mul | BinOp::MulUnchecked => lhs.bvmul_no_overflow_unsigned(rhs).not(),
                    _ => unreachable!("guarded by earlier match"), // external enum: BinOp (guarded subset)
                }
            }
        };

        Some((result, overflow))
    }

    /// Translates a checked binary operation to a AY tuple expression (result, overflow).
    ///
    /// CheckedBinaryOp returns a tuple (T, bool) where the bool indicates overflow.
    /// This is critical for CHC encoding - without proper tuple encoding, the overflow
    /// check passes unconstrained, leading to spurious errors (#657).
    ///
    /// The `is_signed` parameter determines whether to use signed or unsigned overflow
    /// detection semantics (#666).
    pub(in crate::codegen_ay::chc) fn translate_checked_binop(
        &self,
        op: BinOp,
        lhs: Expr,
        rhs: Expr,
        is_signed: bool,
        int_bv_width: u32,
    ) -> Option<Expr> {
        let (result, overflow) = Self::checked_binop_result_overflow(
            op,
            lhs,
            rhs,
            is_signed,
            int_bv_width,
            self.int_lift,
        )?;
        // Part of #112: When int_lift produces Int result, use Int sort for the
        // tuple field. Otherwise use the original BV sort with detected width.
        let result_sort = if result.sort().is_int() {
            Sort::int()
        } else {
            let width = result.sort().bitvec_width()?;
            Sort::bitvec(width)
        };

        // Re: #1958: Use shared tuple_sort_name for consistent naming
        let fields: Vec<(&str, Sort)> = vec![("fld_0", result_sort), ("fld_1", Sort::bool())];
        let sort_name = Self::tuple_sort_name(&fields);
        let tuple_sort = struct_sort(&sort_name, fields);

        // Return tuple constructor with unique name (#948)
        let cons_name = crate::codegen_ay::names::resolve_ctor_name(&tuple_sort, &sort_name);
        Some(Expr::datatype_constructor(sort_name, cons_name, vec![result, overflow], tuple_sort))
    }

    /// Translates a checked binary operation to separate (result, overflow) expressions.
    /// Used when the destination local is flattened (Part of #2214).
    /// Returns `(result_bv, overflow_bool)` without constructing a Datatype.
    pub(in crate::codegen_ay::chc) fn translate_checked_binop_flat(
        &self,
        op: BinOp,
        lhs: Expr,
        rhs: Expr,
        is_signed: bool,
        int_bv_width: u32,
    ) -> Option<(Expr, Expr)> {
        Self::checked_binop_result_overflow(op, lhs, rhs, is_signed, int_bv_width, self.int_lift)
    }

    /// Translates a unary operation to a AY expression.
    ///
    /// `int_bv_width`: BV width for Int-to-BV round-trip on Int-lifted locals (Part of #3043).
    /// `is_signed`: Whether the operand type is signed (Part of #3055).
    pub(in crate::codegen_ay::chc) fn translate_unop(
        &self,
        op: UnOp,
        expr: Expr,
        int_bv_width: u32,
        is_signed: bool,
    ) -> Option<Expr> {
        Some(match op {
            UnOp::Not => {
                if expr.sort().is_bool() {
                    expr.not()
                } else if expr.sort().is_bitvec() {
                    expr.bvnot()
                } else if expr.sort().is_int() {
                    // Part of #2875, #3043: Int-lifted locals — NOT at MIR-derived width.
                    // Part of #3055: use unsigned bv2int for unsigned types.
                    let bv_result = expr.int2bv(int_bv_width).bvnot();
                    if is_signed { bv_result.bv2int_signed() } else { bv_result.bv2int() }
                } else {
                    return None;
                }
            }
            UnOp::Neg => {
                if expr.sort().is_int() {
                    expr.int_neg()
                } else if expr.sort().is_bitvec() {
                    expr.bvneg()
                } else {
                    return None;
                }
            }
            // Guard: codegen_stmt_rvalue.rs dispatches PtrMetadata to translate_ptr_metadata
            // before reaching translate_unop — this arm is structurally unreachable.
            // Part of #3124: graceful fallback instead of panic for catch_unwind safety.
            UnOp::PtrMetadata => {
                warn!("PtrMetadata reached translate_unop unexpectedly");
                return None;
            }
        })
    }

    /// Translates a cast operation to a AY expression (#673).
    ///
    /// Handles bitvector casts with proper sign/zero extension:
    /// - Extension (smaller to larger): sign-extend for signed, zero-extend for unsigned
    /// - Truncation (larger to smaller): extract low bits
    /// - Same width: pass through
    pub(in crate::codegen_ay::chc) fn translate_cast(
        &mut self,
        operand: &Operand,
        target_ty: rustc_public::ty::Ty,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        let expr = self.translate_operand_with_modified(operand, modified_locals)?;
        let src_sort = expr.sort().clone();

        // Get target width from type.
        // Keep explicit primitive/ref arms first, then reuse translate_ty for
        // pointer-wrapper ADTs (e.g., Box/NonNull -> bv64).
        let target_width = match target_ty.kind() {
            TyKind::RigidTy(RigidTy::Int(int_ty)) => Some(int_ty_to_bitvec_width(int_ty)),
            TyKind::RigidTy(RigidTy::Uint(uint_ty)) => Some(uint_ty_to_bitvec_width(uint_ty)),
            TyKind::RigidTy(RigidTy::Bool) => None, // Handled separately via bool-specific path
            TyKind::RigidTy(RigidTy::Char) => Some(32), // Unicode scalar (32-bit)
            // Part of #4030: derive Ref/RawPtr cast widths from translate_ty so
            // DST pointers (`*const [T]`, `&str`, `*const dyn Trait`) keep their
            // wide BV128 encoding instead of being truncated through BV64.
            TyKind::RigidTy(RigidTy::RawPtr(_, _) | RigidTy::Ref(_, _, _)) => {
                Self::translate_ty(target_ty)
                    .and_then(|sort| sort.bitvec_width())
                    .or(Some(POINTER_WIDTH))
            }
            TyKind::RigidTy(RigidTy::FnDef(_, _) | RigidTy::FnPtr(_)) => Some(POINTER_WIDTH),
            other => {
                let inferred_width =
                    Self::translate_ty(target_ty).and_then(|sort| sort.bitvec_width());
                if inferred_width.is_some() {
                    trace!(
                        ?other,
                        ?inferred_width,
                        "CHC: translate_cast - inferred target bit width from translate_ty"
                    );
                } else {
                    trace!(?other, "CHC: translate_cast - no bit width for cast target type");
                }
                inferred_width
            }
        };

        match (src_sort.inner(), target_width) {
            // Bool to bitvector
            (SortInner::Bool, Some(width)) => {
                let bv1 = Expr::ite(expr, Expr::bitvec_const(1, 1), Expr::bitvec_const(0, 1));
                if width == 1 { Some(bv1) } else { Some(bv1.zero_extend(width - 1)) }
            }
            // Bitvector to bool (#685)
            // Use explicit Bool check instead of weak ty_signedness check
            (SortInner::BitVec(src_bv), None)
                if matches!(target_ty.kind(), TyKind::RigidTy(RigidTy::Bool)) =>
            {
                // Target is bool - check if non-zero
                Some(expr.ne(Expr::bitvec_const(0, src_bv.width)))
            }
            // Bitvector to bitvector
            (SortInner::BitVec(src_bv), Some(dst_width)) => {
                if src_bv.width == dst_width {
                    // Same width: pass through
                    Some(expr)
                } else if src_bv.width < dst_width {
                    // Extension: sign-extend for signed, zero-extend for unsigned
                    let extra_bits = dst_width - src_bv.width;
                    let src_signed =
                        self.operand_signedness_for_cast(operand).unwrap_or_else(|| {
                            signedness_fallback_for_cast_or_coerce("translate_cast_extension")
                        });
                    Some(if src_signed {
                        expr.sign_extend(extra_bits)
                    } else {
                        expr.zero_extend(extra_bits)
                    })
                } else {
                    // Truncation: extract low bits
                    Some(expr.extract(dst_width - 1, 0))
                }
            }
            // Int sort (unbounded) to bitvector — use SMT-LIB int2bv.
            // Part of #2007: Previously passed through Int sort unchanged, causing
            // downstream bvadd panics when the leaked Int-sort expression was used
            // in bitvector arithmetic contexts.
            (SortInner::Int, Some(width)) => Some(expr.int2bv(width)),
            // Unsupported sort/width combinations — try sort coercion before falling back.
            // Explicit arms so new SortInner variants trigger a compiler error.
            // Part of #3099: coerce_assignment_rhs_to_sort handles identity, single-field
            // Datatype unwrapping, BV width mismatch, Bool↔BV, and Int↔BV coercions.
            // If coercion succeeds, no fallback is recorded (eliminates false demotions).
            (SortInner::Bool, None)
            | (SortInner::BitVec(_), None)
            | (SortInner::Int, None)
            | (SortInner::Real, _)
            | (SortInner::Array(_), _)
            | (SortInner::Datatype(_), _)
            | (SortInner::String, _)
            | (SortInner::FloatingPoint(_, _), _)
            | (SortInner::Uninterpreted(_), _)
            | (SortInner::RegLan, _) => self.try_cast_coercion_or_fallback(expr, target_ty),
            (_, _) => self.try_cast_coercion_or_fallback(expr, target_ty),
        }
    }

    /// Attempt sort coercion before recording a fallback for unsupported casts.
    ///
    /// Part of #3099: eliminates false demotions by handling casts that
    /// `coerce_assignment_rhs_to_sort` can resolve (identity, single-field
    /// Datatype unwrapping, BV width mismatch, Bool↔BV, Int↔BV).
    ///
    /// Falls back to `record_fallback()` + pass-through when coercion fails.
    fn try_cast_coercion_or_fallback(
        &mut self,
        expr: Expr,
        target_ty: rustc_public::ty::Ty,
    ) -> Option<Expr> {
        if let Some(target_sort) = Self::translate_ty(target_ty) {
            if let Some(coerced) =
                Self::coerce_assignment_rhs_to_sort(expr.clone(), &target_sort, None)
            {
                debug!(
                    src_sort = ?expr.sort(),
                    ?target_sort,
                    "translate_cast: coerced via coerce_assignment_rhs_to_sort (no fallback)"
                );
                return Some(coerced);
            }
        }
        self.record_fallback();
        warn!(src_sort = ?expr.sort(), ?target_ty, "translate_cast: unsupported cast, passing through");
        Some(expr)
    }
}
