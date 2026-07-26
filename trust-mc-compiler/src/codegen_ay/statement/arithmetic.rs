// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Arithmetic operations with overflow handling for AY codegen.
//!
//! This module implements wrapping, unchecked, and checked arithmetic operations
//! used by Rust intrinsics like `wrapping_add`, `checked_mul`, etc.
//!
//! Saturating, overflowing, and exact_div operations are in `arithmetic_overflow.rs`.
//! Atomic intrinsics are in `arithmetic_atomic.rs`.
//! Overflow/safety checks are in `arithmetic_checks.rs`.

use ay_bindings::{Expr, Sort};
use rustc_public::mir::{BasicBlockIdx, BinOp, Operand, Place};
use tracing::warn;

use crate::codegen_ay::types::bv8_sort;

use super::StatementCodegen;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    pub(super) fn ensure_bitvec_compat(
        &self,
        op: BinOp,
        lhs: &Expr,
        rhs: &Expr,
        context: &'static str,
    ) -> bool {
        let lhs_sort = lhs.sort();
        let rhs_sort = rhs.sort();
        if !lhs_sort.is_bitvec() || !rhs_sort.is_bitvec() {
            warn!(
                op = ?op,
                lhs = ?lhs_sort,
                rhs = ?rhs_sort,
                context,
                "Skipping arithmetic intrinsic for non-bitvec sorts"
            );
            return false;
        }
        // Shifts allow different-width operands (e.g., u64 << u32).
        // Part of #3477: all shift intrinsics take u32 shift amount regardless of value type.
        if !matches!(op, BinOp::Shl | BinOp::Shr | BinOp::ShlUnchecked | BinOp::ShrUnchecked)
            && lhs_sort != rhs_sort
        {
            warn!(
                op = ?op,
                lhs = ?lhs_sort,
                rhs = ?rhs_sort,
                context,
                "Skipping arithmetic intrinsic for mismatched sorts"
            );
            return false;
        }
        true
    }

    /// Apply an arithmetic binary operation with full signedness and shift-wrapping support.
    ///
    /// Extends `apply_wrapping_binop` to handle Div/Rem/Shl/Shr:
    /// - Div/Rem: uses signed (bvsdiv/bvsrem) or unsigned (bvudiv/bvurem) per `is_signed`.
    /// - Shl/Shr: coerces shift amount to value width. If `mask_shift`, masks shift amount
    ///   by `(bit_width - 1)` for wrapping semantics (e.g., `wrapping_shl`).
    /// - Shr: uses bvashr (signed) or bvlshr (unsigned) per `is_signed`.
    ///
    /// Float callers intercept before reaching this helper (Part of #3693):
    /// `rvalue.rs` routes float BinOp through AY FP theory (bv_to_fp → fp.add/sub/mul/div → fp_to_ieee_bv).
    /// The BV arithmetic arms below are only reached for integer types.
    ///
    /// Part of #3477: BMC encoding parity with CHC arithmetic dispatch.
    pub(super) fn apply_arith_op(
        op: BinOp,
        lhs: &Expr,
        rhs: &Expr,
        is_signed: bool,
        mask_shift: bool,
    ) -> Option<Expr> {
        match op {
            BinOp::Add | BinOp::AddUnchecked => Some(lhs.clone().bvadd(rhs.clone())),
            BinOp::Sub | BinOp::SubUnchecked => Some(lhs.clone().bvsub(rhs.clone())),
            BinOp::Mul | BinOp::MulUnchecked => Some(lhs.clone().bvmul(rhs.clone())),
            BinOp::Div => {
                if is_signed {
                    Some(lhs.clone().bvsdiv(rhs.clone()))
                } else {
                    Some(lhs.clone().bvudiv(rhs.clone()))
                }
            }
            BinOp::Rem => {
                if is_signed {
                    Some(lhs.clone().bvsrem(rhs.clone()))
                } else {
                    Some(lhs.clone().bvurem(rhs.clone()))
                }
            }
            BinOp::Shl | BinOp::ShlUnchecked => {
                let target_width = lhs.sort().bitvec_width()?;
                let shift = if mask_shift {
                    // Wrapping shift: mask shift amount by (width - 1) before coercion
                    let rhs_width = rhs.sort().bitvec_width()?;
                    let mask = Expr::bitvec_const(target_width as u128 - 1, rhs_width);
                    Self::coerce_to_width_typed(rhs.clone().bvand(mask), target_width, false)
                } else {
                    Self::coerce_to_width_typed(rhs.clone(), target_width, false)
                };
                Some(lhs.clone().bvshl(shift))
            }
            BinOp::Shr | BinOp::ShrUnchecked => {
                let target_width = lhs.sort().bitvec_width()?;
                let shift = if mask_shift {
                    let rhs_width = rhs.sort().bitvec_width()?;
                    let mask = Expr::bitvec_const(target_width as u128 - 1, rhs_width);
                    Self::coerce_to_width_typed(rhs.clone().bvand(mask), target_width, false)
                } else {
                    Self::coerce_to_width_typed(rhs.clone(), target_width, false)
                };
                if is_signed {
                    Some(lhs.clone().bvashr(shift))
                } else {
                    Some(lhs.clone().bvlshr(shift))
                }
            }
            _ => None, // external enum: BinOp
        }
    }

    /// Codegen wrapping arithmetic - wraps on overflow.
    ///
    /// For Add/Sub/Mul: sign-agnostic at bitvector level.
    /// For Div/Rem: panics on div-by-zero; signed MIN/-1 wraps to MIN.
    /// For Shl/Shr: masks shift amount by (bit_width - 1) for wrapping semantics.
    ///
    /// Part of #3477: Extended from Add/Sub/Mul to include Div/Rem/Shl/Shr.
    ///
    /// REQUIRES: args.len() >= 2
    /// ENSURES: destination gets result, overflow wraps silently
    pub(super) fn codegen_wrapping_arith(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
        op: BinOp,
    ) -> Option<BasicBlockIdx> {
        if args.len() < 2 {
            return None;
        }

        let lhs_expr = self.codegen_operand(&args[0])?;
        let rhs_expr = self.codegen_operand(&args[1])?;
        if !self.ensure_bitvec_compat(op, &lhs_expr, &rhs_expr, "wrapping") {
            return None;
        }

        // Determine signedness for sign-dependent ops (Div/Rem/Shr)
        let is_signed = if matches!(op, BinOp::Div | BinOp::Rem | BinOp::Shr) {
            self.is_signed_integer_op(&args[0], &args[1]).unwrap_or_else(|| {
                crate::codegen_ay::shared::signedness_fallback_for_arithmetic(
                    "codegen_wrapping_arith",
                )
            })
        } else {
            false // Add/Sub/Mul/Shl: signedness irrelevant at BV level
        };

        // Wrapping div/rem still panics on division by zero (Rust semantics)
        if matches!(op, BinOp::Div | BinOp::Rem) {
            self.emit_division_by_zero_check(&rhs_expr, "wrapping_div_by_zero");
        }

        // mask_shift=true: wrapping_shl/shr mask shift amount by (width-1)
        let result = Self::apply_arith_op(op, &lhs_expr, &rhs_expr, is_signed, true)?;

        self.bind_ssa_result(destination, result);
        target
    }

    /// Codegen unchecked arithmetic - performs operation AND asserts no overflow.
    ///
    /// Unchecked ops have UB on overflow, so the verifier must detect overflows.
    /// This is the key difference from wrapping ops which silently wrap.
    ///
    /// Part of #3477: Extended from Add/Sub/Mul to include Div/Rem/Shl/Shr.
    /// - Div/Rem: asserts no div-by-zero and no signed overflow (MIN/-1).
    /// - Shl/Shr: asserts shift distance < bit width.
    ///
    /// REQUIRES: args.len() >= 2
    /// ENSURES: destination gets result, overflow records violation
    pub(super) fn codegen_unchecked_arith(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
        op: BinOp,
    ) -> Option<BasicBlockIdx> {
        if args.len() < 2 {
            return None;
        }

        let lhs_expr = self.codegen_operand(&args[0])?;
        let rhs_expr = self.codegen_operand(&args[1])?;
        if !self.ensure_bitvec_compat(op, &lhs_expr, &rhs_expr, "unchecked") {
            return None;
        }

        // Determine signedness from operand types
        let is_signed = self.is_signed_integer_op(&args[0], &args[1]).unwrap_or_else(|| {
            crate::codegen_ay::shared::signedness_fallback_for_arithmetic("codegen_unchecked_arith")
        });

        // Perform the operation (no shift masking — unchecked shifts assert valid distance)
        let result = Self::apply_arith_op(op, &lhs_expr, &rhs_expr, is_signed, false)?;

        // Emit safety checks specific to the operation
        if matches!(op, BinOp::Div | BinOp::Rem) {
            // Division by zero is UB
            self.emit_division_by_zero_check(&rhs_expr, "unchecked_div_by_zero");
        }
        if matches!(op, BinOp::Shl | BinOp::Shr) {
            // Shift distance >= bit width is UB
            self.emit_shift_distance_check(&lhs_expr, &rhs_expr, Some(false));
        }
        // Emit overflow check (handles Add/Sub/Mul overflow + signed Div/Rem MIN/-1)
        self.emit_overflow_check(op, &lhs_expr, &rhs_expr, is_signed);

        // Store the result
        self.bind_ssa_result(destination, result);
        target
    }

    /// Codegen checked arithmetic - returns `Option<T>`.
    ///
    /// Encodes result as `Option<T>` with discriminant semantics:
    /// - field .0 = discriminant (8-bit): 0=None (overflow), 1=Some (success)
    /// - field .1 = result value (same width as input operands)
    ///
    /// Note: The discriminant semantics differ from overflowing_arith where the
    /// overflow flag uses bool semantics (0=false/no overflow, 1=true/overflow).
    ///
    /// Part of #3477: Extended from Add/Sub/Mul to include Div/Rem/Shl/Shr.
    /// - checked_div/rem returns None on div-by-zero or (signed: MIN/-1).
    /// - checked_shl/shr returns None when shift >= bit_width.
    ///
    /// REQUIRES: args.len() >= 2
    /// ENSURES: destination.0 is 0 if overflow occurred, 1 otherwise
    /// ENSURES: destination.1 is the wrapping arithmetic result
    pub(super) fn codegen_checked_arith(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
        op: BinOp,
    ) -> Option<BasicBlockIdx> {
        if args.len() < 2 {
            return None;
        }

        let lhs_expr = self.codegen_operand(&args[0])?;
        let rhs_expr = self.codegen_operand(&args[1])?;
        if !self.ensure_bitvec_compat(op, &lhs_expr, &rhs_expr, "checked") {
            return None;
        }

        // Determine signedness from operand types (#267)
        let is_signed = self.is_signed_integer_op(&args[0], &args[1]).unwrap_or_else(|| {
            crate::codegen_ay::shared::signedness_fallback_for_arithmetic("codegen_checked_arith")
        });

        // Compute the result (no shift masking — checked returns None instead of wrapping)
        let result = Self::apply_arith_op(op, &lhs_expr, &rhs_expr, is_signed, false)?;

        // Compute "overflows" expression for the Option discriminant.
        // For checked_div/rem: overflow means div-by-zero OR (signed: MIN/-1).
        // For checked_shl/shr: overflow means shift >= bit_width.
        // For Add/Sub/Mul: use standard overflow_check.
        let overflows = if matches!(op, BinOp::Div | BinOp::Rem) {
            // checked_div returns None when b==0 or (signed: a==MIN && b==-1)
            let rhs_width = rhs_expr
                .sort()
                .bitvec_width()
                .expect("invariant: checked arithmetic operands are bitvec-compatible");
            let zero = Expr::bitvec_const(0u128, rhs_width);
            let div_by_zero = rhs_expr.clone().eq(zero);

            if is_signed {
                let lhs_width = lhs_expr
                    .sort()
                    .bitvec_width()
                    .expect("invariant: checked arithmetic operands are bitvec-compatible");
                let int_min = Expr::bitvec_const(1u128 << (lhs_width - 1), lhs_width);
                let neg_one = Expr::bitvec_const(!0u128 >> (128 - rhs_width), rhs_width);
                let signed_overflow = lhs_expr.eq(int_min).and(rhs_expr.eq(neg_one));
                div_by_zero.or(signed_overflow)
            } else {
                div_by_zero
            }
        } else if matches!(op, BinOp::Shl | BinOp::Shr) {
            // checked_shl/shr returns None when shift amount >= bit_width
            let value_width = lhs_expr
                .sort()
                .bitvec_width()
                .expect("invariant: checked arithmetic operands are bitvec-compatible");
            let shift_width = rhs_expr
                .sort()
                .bitvec_width()
                .expect("invariant: checked arithmetic operands are bitvec-compatible");
            let compare_width = std::cmp::max(value_width, shift_width);
            let rhs_coerced = Self::coerce_to_width_typed(rhs_expr, compare_width, false);
            let width_const = Expr::bitvec_const(value_width as u128, compare_width);
            // overflow = shift >= width (i.e., NOT(shift < width))
            rhs_coerced.bvult(width_const).not()
        } else {
            // Add/Sub/Mul: use overflow_check
            match self.overflow_check(op, &lhs_expr, &rhs_expr, is_signed) {
                Some((no_overflow, _)) => no_overflow.not(),
                None => {
                    warn!(op = ?op, "checked arithmetic: no overflow check for op; treating as no-overflow");
                    Expr::bool_const(false)
                }
            }
        };

        // Create Option<T>: discriminant 0=None, 1=Some
        let result_sort = result.sort();
        let Some(result_bits) = result_sort.bitvec_width() else {
            warn!(
                op = ?op,
                sort = ?result_sort,
                "checked arithmetic produced non-bitvec result; skipping intrinsic"
            );
            return None;
        };
        let discrim = Expr::ite(overflows, Expr::bitvec_const(0, 8), Expr::bitvec_const(1, 8));

        let base_name = self.ssa_base_name(destination);

        // Store discriminant (field 0)
        let discrim_name = crate::codegen_ay::names::discrim_name(&base_name);
        let discrim_ssa = self.ssa_name_from_base(&discrim_name, true);
        let discrim_var = self.ctx.declare_var(&discrim_ssa, bv8_sort());
        self.assert_ssa_def(discrim_var.clone(), discrim, &discrim_name);
        self.env_update(discrim_name, discrim_var);

        // Store value (field 1)
        let value_name = crate::codegen_ay::names::payload_name(&base_name);
        let value_ssa = self.ssa_name_from_base(&value_name, true);
        let value_var = self.ctx.declare_var(&value_ssa, Sort::bitvec(result_bits));
        self.assert_ssa_def(value_var.clone(), result, &value_name);
        self.env_update(value_name, value_var);

        target
    }
}

// Saturating/overflowing/exact_div methods moved to arithmetic_overflow.rs per #4206.
