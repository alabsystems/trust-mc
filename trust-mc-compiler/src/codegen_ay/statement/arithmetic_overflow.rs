// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Saturating, overflowing, and exact division arithmetic codegen.
//!
//! Extracted from `arithmetic.rs` — Part of #4206.

use ay_bindings::{Expr, Sort};
use rustc_public::mir::{BasicBlockIdx, BinOp, Operand, Place};
use tracing::{debug, warn};

use crate::codegen_ay::types::bv8_sort;

use super::StatementCodegen;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Codegen saturating arithmetic - clamps to MIN/MAX on overflow (#273).
    ///
    /// For addition: if overflow upward → MAX, if underflow → MIN
    /// For subtraction: if underflow → MIN, if overflow upward → MAX
    /// For multiplication: clamp to MAX on overflow, MIN on underflow
    /// For division: signed MIN/-1 → MAX (only overflow case); panics on div-by-zero.
    ///
    /// Part of #3477: Extended to handle Div. Shl/Shr have no standard Rust
    /// saturating variants and return None (fall through to generic dispatch).
    ///
    /// REQUIRES: args.len() >= 2
    /// ENSURES: destination gets result clamped to [MIN, MAX] range
    pub(super) fn codegen_saturating_arith(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
        op: BinOp,
    ) -> Option<BasicBlockIdx> {
        if args.len() < 2 {
            return None;
        }

        // Shl/Shr: no standard Rust saturating variants, fall through to generic dispatch
        if matches!(op, BinOp::Shl | BinOp::Shr) {
            debug!(op = ?op, "saturating variant not supported for shifts; falling through");
            return None;
        }

        let lhs_expr = self.codegen_operand(&args[0])?;
        let rhs_expr = self.codegen_operand(&args[1])?;
        if !self.ensure_bitvec_compat(op, &lhs_expr, &rhs_expr, "saturating") {
            return None;
        }

        let is_signed = self.is_signed_integer_op(&args[0], &args[1]).unwrap_or_else(|| {
            crate::codegen_ay::shared::signedness_fallback_for_arithmetic(
                "codegen_saturating_arith",
            )
        });
        let lhs_sort = lhs_expr.sort();
        let Some(width) = lhs_sort.bitvec_width() else {
            warn!(
                op = ?op,
                sort = ?lhs_sort,
                "saturating arithmetic expected bitvec lhs sort; skipping intrinsic"
            );
            return None;
        };

        // Saturating div/rem still panics on division by zero (Rust semantics)
        if matches!(op, BinOp::Div | BinOp::Rem) {
            self.emit_division_by_zero_check(&rhs_expr, "saturating_div_by_zero");
        }

        // Compute the wrapping result
        let result = Self::apply_arith_op(op, &lhs_expr, &rhs_expr, is_signed, false)?;

        // Get MIN and MAX values
        let (min_val, max_val) = if is_signed {
            // Signed: MIN = -2^(width-1), MAX = 2^(width-1) - 1
            let int_min = Expr::bitvec_const(1u128 << (width - 1), width);
            let int_max = Expr::bitvec_const((1u128 << (width - 1)) - 1, width);
            (int_min, int_max)
        } else {
            // Unsigned: MIN = 0, MAX = 2^width - 1
            let uint_min = Expr::bitvec_const(0u128, width);
            let uint_max = Expr::bitvec_const(!0u128 >> (128 - width), width);
            (uint_min, uint_max)
        };

        // Detect overflow/underflow direction
        // For saturating, we need to know which direction we overflowed to pick MIN or MAX
        let saturated_result = if let Some((no_overflow, _)) =
            self.overflow_check(op, &lhs_expr, &rhs_expr, is_signed)
        {
            let overflows = no_overflow.not();

            // Determine saturation direction (MAX or MIN) based on operation and signedness.
            // Unsigned: add overflows to MAX, sub underflows to MIN, mul overflows to MAX.
            // Signed: direction depends on operand signs (see individual cases below).
            let clamp_value = match (op, is_signed) {
                (BinOp::Add, true) => {
                    // Signed add overflow only occurs when both operands have the same sign.
                    // If lhs >= 0, both are positive, overflow → MAX.
                    // If lhs < 0, both are negative, underflow → MIN.
                    let zero = Expr::bitvec_const(0u128, width);
                    let lhs_positive = lhs_expr.clone().bvsge(zero);
                    Expr::ite(lhs_positive, max_val, min_val)
                }
                (BinOp::Add, false) => {
                    // Unsigned add: overflow always goes to MAX
                    max_val
                }
                (BinOp::Sub, true) => {
                    // Signed sub: positive - negative overflows to MAX, negative - positive to MIN
                    let zero = Expr::bitvec_const(0u128, width);
                    let lhs_positive = lhs_expr.clone().bvsge(zero.clone());
                    let rhs_negative = rhs_expr.clone().bvsge(zero).not();
                    // If lhs >= 0 and rhs < 0, overflow to MAX
                    // If lhs < 0 and rhs > 0, underflow to MIN
                    Expr::ite(lhs_positive.and(rhs_negative), max_val, min_val)
                }
                (BinOp::Sub, false) => {
                    // Unsigned sub: underflow always goes to MIN (0)
                    min_val
                }
                (BinOp::Mul, true) => {
                    // Signed mul: sign(a)*sign(b) determines direction
                    let zero = Expr::bitvec_const(0u128, width);
                    let same_sign =
                        lhs_expr.clone().bvsge(zero.clone()).eq(rhs_expr.clone().bvsge(zero));
                    Expr::ite(same_sign, max_val, min_val)
                }
                (BinOp::Mul, false) => {
                    // Unsigned mul: overflow always goes to MAX
                    max_val
                }
                // Part of #3477: signed Div: MIN/-1 saturates to MAX
                (BinOp::Div, true) | (BinOp::Rem, true) => max_val,
                // Unsigned div/rem cannot overflow (div-by-zero is separate assertion)
                (BinOp::Div, false) | (BinOp::Rem, false) => {
                    // Should not reach here since overflow_check returns None for unsigned div
                    max_val
                }
                _ => {
                    warn!(op = ?op, "saturating arithmetic: unexpected op; using wrapping result");
                    return Some({
                        self.bind_ssa_result(destination, result);
                        target?
                    });
                }
            };

            // ite(overflows, clamp_value, result)
            Expr::ite(overflows, clamp_value, result)
        } else {
            // No overflow check available, just use result
            result
        };

        // Store the result
        self.bind_ssa_result(destination, saturated_result);
        target
    }

    /// Codegen overflowing arithmetic - returns (T, bool) tuple (#273).
    ///
    /// Encodes result as (T, bool) tuple with field layout:
    /// - field .0 = result value (same width as input operands, wrapping)
    /// - field .1 = overflow flag (8-bit): 0=no overflow, 1=overflow
    ///
    /// Note: This differs from checked_arith where discriminant comes first.
    ///
    /// Part of #3477: Extended from Add/Sub/Mul to include Div/Rem/Shl/Shr.
    /// - overflowing_div/rem: panics on div-by-zero; overflow = signed MIN/-1.
    ///   Result wraps (MIN for div, 0 for rem).
    /// - overflowing_shl/shr: result = shift by (amount % width), overflow = (amount >= width).
    ///
    /// REQUIRES: args.len() >= 2
    /// ENSURES: destination.0 is the wrapping arithmetic result
    /// ENSURES: destination.1 is 1 if overflow occurred, 0 otherwise
    pub(super) fn codegen_overflowing_arith(
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
        if !self.ensure_bitvec_compat(op, &lhs_expr, &rhs_expr, "overflowing") {
            return None;
        }

        let is_signed = self.is_signed_integer_op(&args[0], &args[1]).unwrap_or_else(|| {
            crate::codegen_ay::shared::signedness_fallback_for_arithmetic(
                "codegen_overflowing_arith",
            )
        });

        // Overflowing div/rem still panics on division by zero (Rust semantics)
        if matches!(op, BinOp::Div | BinOp::Rem) {
            self.emit_division_by_zero_check(&rhs_expr, "overflowing_div_by_zero");
        }

        // Compute the wrapping result
        // For shl/shr: mask_shift=true (overflowing_shl shifts by amount % width)
        // For div/rem: BV division naturally wraps at bitvector level
        let mask_shift = matches!(op, BinOp::Shl | BinOp::Shr);
        let result = Self::apply_arith_op(op, &lhs_expr, &rhs_expr, is_signed, mask_shift)?;

        // Get overflow flag
        let overflowed = if matches!(op, BinOp::Shl | BinOp::Shr) {
            // overflowing_shl/shr: overflow = (shift_amount >= bit_width)
            let value_width = lhs_expr
                .sort()
                .bitvec_width()
                .expect("invariant: overflowing arithmetic operands are bitvec-compatible");
            let shift_width = rhs_expr
                .sort()
                .bitvec_width()
                .expect("invariant: overflowing arithmetic operands are bitvec-compatible");
            let compare_width = std::cmp::max(value_width, shift_width);
            let rhs_coerced = Self::coerce_to_width_typed(rhs_expr, compare_width, false);
            let width_const = Expr::bitvec_const(value_width as u128, compare_width);
            // overflow = NOT(shift < width) = shift >= width
            rhs_coerced.bvult(width_const).not()
        } else {
            match self.overflow_check(op, &lhs_expr, &rhs_expr, is_signed) {
                Some((no_overflow, _)) => no_overflow.not(),
                None => {
                    // Unsigned div/rem: no computational overflow possible
                    Expr::bool_const(false)
                }
            }
        };

        // Create (T, bool) tuple stored as fields .0 and .1
        let result_sort = result.sort();
        let Some(result_bits) = result_sort.bitvec_width() else {
            warn!(
                op = ?op,
                sort = ?result_sort,
                "overflowing arithmetic produced non-bitvec result; skipping intrinsic"
            );
            return None;
        };
        let base_name = self.ssa_base_name(destination);

        // Store result (field 0)
        let result_name = crate::codegen_ay::names::discrim_name(&base_name);
        let result_ssa = self.ssa_name_from_base(&result_name, true);
        let result_var = self.ctx.declare_var(&result_ssa, Sort::bitvec(result_bits));
        self.assert_ssa_def(result_var.clone(), result, &result_name);
        self.env_update(result_name, result_var);

        // Store overflow flag (field 1) - bool stored as 8-bit discriminant
        let overflow_name = crate::codegen_ay::names::payload_name(&base_name);
        let overflow_ssa = self.ssa_name_from_base(&overflow_name, true);
        let overflow_var = self.ctx.declare_var(&overflow_ssa, bv8_sort());
        let overflow_byte =
            Expr::ite(overflowed, Expr::bitvec_const(1, 8), Expr::bitvec_const(0, 8));
        self.assert_ssa_def(overflow_var.clone(), overflow_byte, &overflow_name);
        self.env_update(overflow_name, overflow_var);

        target
    }

    /// Codegen `overflowing_add_signed(self: usize, rhs: isize) -> (usize, bool)` (Part of #3375).
    ///
    /// `ptr.offset()` is inlined by rustc into `overflowing_add_signed` rather than
    /// being lowered to `BinOp::Offset`. The semantics are:
    /// - result = self.wrapping_add(rhs as usize)  (bitvec add, signedness irrelevant)
    /// - overflow = (result < self) XOR (rhs < 0)  (unsigned carry adjusted for sign)
    ///
    /// Destination is a `(usize, bool)` tuple:
    /// - field .0 = wrapping result
    /// - field .1 = overflow flag (8-bit): 0=no overflow, 1=overflow
    pub(super) fn codegen_overflowing_add_signed(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.len() < 2 {
            return None;
        }

        let lhs_expr = self.codegen_operand(&args[0])?;
        let rhs_expr = self.codegen_operand(&args[1])?;

        let lhs_sort = lhs_expr.sort();
        let rhs_sort = rhs_expr.sort();
        if !lhs_sort.is_bitvec() || !rhs_sort.is_bitvec() {
            warn!(
                lhs = ?lhs_sort,
                rhs = ?rhs_sort,
                "overflowing_add_signed: non-bitvec operands; skipping"
            );
            return None;
        }

        // Coerce to same width. LHS (self) is unsigned, RHS (rhs) is signed.
        let target_width = lhs_sort.bitvec_width()?.max(rhs_sort.bitvec_width()?);
        let lhs = Self::coerce_to_width_typed(lhs_expr, target_width, false);
        let rhs = Self::coerce_to_width_typed(rhs_expr, target_width, true);

        // result = self.wrapping_add(rhs as usize)  [BV add, sign irrelevant]
        let result = lhs.clone().bvadd(rhs.clone());

        // unsigned_carry = result < self  [unsigned comparison]
        let unsigned_carry = result.clone().bvult(lhs);
        // rhs_negative = rhs < 0  [signed comparison]
        let zero = Expr::bitvec_const(0u128, target_width);
        let rhs_negative = rhs.bvslt(zero);
        // overflow = unsigned_carry XOR rhs_negative = !(carry == negative)
        let overflowed = unsigned_carry.eq(rhs_negative).not();

        // Store as (T, bool) tuple: field .0 = result, field .1 = overflow flag
        let result_sort = result.sort();
        let Some(result_bits) = result_sort.bitvec_width() else {
            warn!(
                sort = ?result_sort,
                "overflowing_add_signed produced non-bitvec result; skipping"
            );
            return None;
        };
        let base_name = self.ssa_base_name(destination);

        // Store result (field 0)
        let result_name = crate::codegen_ay::names::discrim_name(&base_name);
        let result_ssa = self.ssa_name_from_base(&result_name, true);
        let result_var = self.ctx.declare_var(&result_ssa, Sort::bitvec(result_bits));
        self.assert_ssa_def(result_var.clone(), result, &result_name);
        self.env_update(result_name, result_var);

        // Store overflow flag (field 1) — bool stored as 8-bit discriminant
        let overflow_name = crate::codegen_ay::names::payload_name(&base_name);
        let overflow_ssa = self.ssa_name_from_base(&overflow_name, true);
        let overflow_var = self.ctx.declare_var(&overflow_ssa, bv8_sort());
        let overflow_byte =
            Expr::ite(overflowed, Expr::bitvec_const(1, 8), Expr::bitvec_const(0, 8));
        self.assert_ssa_def(overflow_var.clone(), overflow_byte, &overflow_name);
        self.env_update(overflow_name, overflow_var);

        target
    }

    /// Codegen `exact_div(a, b)` — division with 3 UB conditions (#3177).
    ///
    /// UB 1: `b == 0` (division by zero)
    /// UB 2: `a % b != 0` (not exact, guarded by b != 0)
    /// UB 3: `a == T::MIN && b == -1` (signed overflow, signed types only)
    ///
    /// Result: `a / b` (signed or unsigned per operand type).
    pub(super) fn codegen_exact_div(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.len() < 2 {
            return None;
        }

        let lhs_expr = self.codegen_operand(&args[0])?;
        let rhs_expr = self.codegen_operand(&args[1])?;

        let lhs_sort = lhs_expr.sort();
        let rhs_sort = rhs_expr.sort();
        if !lhs_sort.is_bitvec() || !rhs_sort.is_bitvec() {
            warn!(
                lhs = ?lhs_sort,
                rhs = ?rhs_sort,
                "exact_div: non-bitvec operands; skipping"
            );
            return None;
        }

        let is_signed = self.is_signed_integer_op(&args[0], &args[1]).unwrap_or_else(|| {
            crate::codegen_ay::shared::signedness_fallback_for_arithmetic("codegen_exact_div")
        });

        // Coerce widths if mismatched
        let (lhs, rhs) = Self::coerce_to_match_widths_typed(lhs_expr, rhs_expr, is_signed);
        let width = lhs.sort().bitvec_width().expect("coerced bitvec must have width");

        let zero = Expr::bitvec_const(0u128, width);

        // UB 1: division by zero
        self.record_violation_guarded(rhs.clone().eq(zero.clone()), "exact_div_zero");

        // UB 2: not exact (a % b != 0), guarded by b != 0 to avoid div-by-zero in smt
        let b_nonzero = rhs.clone().eq(zero.clone()).not();
        let remainder = if is_signed {
            lhs.clone().bvsrem(rhs.clone())
        } else {
            lhs.clone().bvurem(rhs.clone())
        };
        let not_exact = b_nonzero.and(remainder.eq(zero).not());
        self.record_violation_guarded(not_exact, "exact_div_not_exact");

        // UB 3: signed overflow (a == T::MIN && b == -1)
        if is_signed {
            let t_min = Expr::bitvec_const(1u128 << (width - 1), width);
            let neg_one = Expr::bitvec_const(!0u128 >> (128 - width), width);
            let overflow = lhs.clone().eq(t_min).and(rhs.clone().eq(neg_one));
            self.record_violation_guarded(overflow, "exact_div_overflow");
        }

        // Result
        let result = if is_signed { lhs.bvsdiv(rhs) } else { lhs.bvudiv(rhs) };

        debug!(width, is_signed, "AY codegen: exact_div encoded");
        self.bind_ssa_result(destination, result);
        target
    }
}
