// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Overflow, division-by-zero, shift distance, and offset safety checks.
//!
//! Extracted from `arithmetic.rs` — these functions emit verification conditions
//! for operations that can exhibit undefined behavior (overflow, division by zero,
//! excessive shifts, pointer offset wrap-around).

use ay_bindings::Expr;
use rustc_public::mir::BinOp;
use tracing::{debug, warn};

use super::StatementCodegen;
use crate::codegen_ay::types::POINTER_WIDTH;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Emit overflow check assertions for checked binary operations.
    ///
    /// For verification, we assert that arithmetic operations do NOT overflow.
    /// This models Rust's checked arithmetic semantics where overflow causes panic.
    ///
    /// REQUIRES: lhs.sort().is_bitvec() && rhs.sort().is_bitvec()
    /// ENSURES: If op can overflow, adds violation assertion to VC
    /// ENSURES: No-op for operations that cannot overflow
    pub(super) fn emit_overflow_check(
        &mut self,
        op: BinOp,
        lhs: &Expr,
        rhs: &Expr,
        is_signed: bool,
    ) {
        if let Some((no_overflow_expr, label)) = self.overflow_check(op, lhs, rhs, is_signed) {
            // Overflow is a property violation: add `¬no_overflow` as a reachable counterexample.
            self.record_violation_guarded(no_overflow_expr.not(), label);
        }
    }

    /// Emit division-by-zero check for division and remainder operations.
    ///
    /// Division and remainder by zero is undefined behavior in Rust.
    /// This function emits a verification condition that the divisor is non-zero.
    ///
    /// REQUIRES: divisor.sort().is_bitvec()
    /// ENSURES: Adds violation assertion (divisor == 0) to VC
    pub(super) fn emit_division_by_zero_check(&mut self, divisor: &Expr, label: &str) {
        let Some(width) = divisor.sort().bitvec_width() else {
            return;
        };
        let zero = Expr::bitvec_const(0u128, width);
        let is_zero = divisor.clone().eq(zero);
        self.record_violation_guarded(is_zero, label);
    }

    /// Emit shift distance check for unchecked shift operations.
    ///
    /// Unchecked shifts have undefined behavior when:
    /// - Shift distance >= bit width of value (excessive shift)
    /// - Shift distance < 0 (negative shift, only for signed shift amounts)
    ///
    /// REQUIRES: value.sort().is_bitvec() && distance.sort().is_bitvec()
    /// ENSURES: Adds violation assertion for excessive shift distance
    /// ENSURES: If distance_signed=Some(true), also checks for negative distance
    pub(super) fn emit_shift_distance_check(
        &mut self,
        value: &Expr,
        distance: &Expr,
        distance_signed: Option<bool>,
    ) {
        let Some(value_width) = value.sort().bitvec_width() else {
            return;
        };
        let Some(distance_width) = distance.sort().bitvec_width() else {
            return;
        };

        // Check: distance < value_width (excessive shift check)
        // We compare in the wider of the two widths to avoid truncation losing high bits.
        // E.g., if value is u8 and distance is u32 with value 256, we need to detect 256 >= 8.
        let compare_width = std::cmp::max(value_width, distance_width);
        let distance_coerced = Self::coerce_to_width_typed(distance.clone(), compare_width, false);
        let width_const = Expr::bitvec_const(value_width as u128, compare_width);
        let valid_distance = distance_coerced.bvult(width_const);
        self.record_violation_guarded(valid_distance.not(), "shift_distance_check");

        if distance_signed == Some(true) {
            let distance_signed =
                Self::coerce_to_width_typed(distance.clone(), compare_width, true);
            let zero = Expr::bitvec_const(0u128, compare_width);
            let negative_distance = distance_signed.bvslt(zero);
            self.record_violation_guarded(negative_distance, "shift_distance_check_negative");
        }
    }

    /// Emit overflow check for pointer offset operations.
    ///
    /// BinOp::Offset computes `ptr.offset(count)` where count is in units of the
    /// pointee type (not bytes). This function checks:
    /// 1. Offset value overflow: count doesn't exceed isize bounds
    /// 2. Byte offset overflow: `count * size_of::<T>()` doesn't overflow isize
    /// 3. Result overflow: ptr + count * size doesn't wrap around address space
    ///
    /// REQUIRES: ptr.sort().is_bitvec() (pointer represented as bitvector)
    /// REQUIRES: count.sort().is_bitvec() (count represented as bitvector)
    /// ENSURES: Adds offset_value_overflow violation if count exceeds isize bounds
    /// ENSURES: If pointee_size > 1, adds offset_bytes_overflow violation
    /// ENSURES: Adds offset_result_overflow violation for pointer wraparound
    /// ENSURES: No-op for ZST (pointee_size == 0) beyond value bounds check
    pub(super) fn emit_offset_overflow_check(
        &mut self,
        ptr: &Expr,
        count: &Expr,
        pointee_size: usize,
    ) {
        let Some(ptr_width) = ptr.sort().bitvec_width() else {
            return;
        };
        let Some(_count_width) = count.sort().bitvec_width() else {
            return;
        };

        debug!(
            "emit_offset_overflow_check: ptr_width={}, pointee_size={}",
            ptr_width, pointee_size
        );

        // Use pointer width for all comparisons (typically 64-bit).
        // isize::MAX on 64-bit is 2^63 - 1.
        let isize_max = Expr::bitvec_const((1i128 << (ptr_width - 1)) - 1, ptr_width);
        let isize_min = Expr::bitvec_const(-(1i128 << (ptr_width - 1)), ptr_width);
        let zero = Expr::bitvec_const(0u128, ptr_width);

        // Sign-extend count to pointer width for signed comparison.
        let count_extended = Self::coerce_to_width_typed(count.clone(), ptr_width, true);

        // Check 1: Offset value within isize bounds.
        // Violation if count > isize::MAX or count < isize::MIN.
        debug!("  emitting offset_value_overflow check");
        let count_too_large = count_extended.clone().bvsgt(isize_max);
        let count_too_small = count_extended.clone().bvslt(isize_min);
        let offset_value_overflow = count_too_large.or(count_too_small);
        self.record_violation_guarded(offset_value_overflow, "offset_value_overflow");

        if self.ctx.config.extra_pointer_checks && ptr_width == POINTER_WIDTH {
            let is_valid = self.ctx.heap_is_allocated(ptr.clone(), None);
            self.record_violation_guarded(is_valid.not(), "pointer_invalid");
        }

        // For ZST (size 0), no byte offset happens, so no further overflow possible.
        if pointee_size == 0 {
            debug!("  skipping byte/result checks for ZST (pointee_size=0)");
            return;
        }

        // Compute byte offset: count * size_of::<T>()
        let (byte_offset, check_mul_overflow) = if pointee_size > 1 {
            let size_expr = Expr::bitvec_const(pointee_size as u128, ptr_width);
            let offset = count_extended.clone().bvmul(size_expr.clone());
            // Check for signed multiplication overflow: result / size != count
            debug!("  emitting offset_bytes_overflow check (size={})", pointee_size);
            let div_back = offset.clone().bvsdiv(size_expr);
            let mul_overflow = div_back.ne(count_extended.clone());
            self.record_violation_guarded(mul_overflow, "offset_bytes_overflow");
            (offset, true)
        } else {
            // size == 1: byte offset equals count, no multiplication needed
            (count_extended.clone(), false)
        };

        // Check 3: Result pointer overflow (ptr + byte_offset).
        // For signed offset, we need to check both directions.
        debug!("  emitting offset_result_overflow check (mul_checked={})", check_mul_overflow);
        let result_ptr = ptr.clone().bvadd(byte_offset);

        // If offset is positive and result < ptr, we wrapped forward.
        let positive_offset = count_extended.clone().bvsge(zero.clone());
        let wrapped_forward = positive_offset.and(result_ptr.clone().bvult(ptr.clone()));

        // If offset is negative and result > ptr, we wrapped backward.
        let negative_offset = count_extended.bvslt(zero);
        let wrapped_backward = negative_offset.and(result_ptr.bvugt(ptr.clone()));

        let ptr_overflow = wrapped_forward.or(wrapped_backward);
        self.record_violation_guarded(ptr_overflow, "offset_result_overflow");
    }

    /// Generate overflow check expression for binary operations.
    ///
    /// Returns an expression that is true when the operation does NOT overflow,
    /// along with a label for the check. Used by `emit_overflow_check` to record
    /// violations when overflow would occur.
    ///
    /// REQUIRES: lhs.sort().is_bitvec() && rhs.sort().is_bitvec() (widths may differ; coerced internally)
    /// ENSURES: On Some((expr, label)), expr is true iff op(lhs, rhs) does not overflow
    /// ENSURES: On None, op is not an overflow-checkable operation (bitwise, comparison, etc.)
    pub(super) fn overflow_check(
        &self,
        op: BinOp,
        lhs: &Expr,
        rhs: &Expr,
        is_signed: bool,
    ) -> Option<(Expr, &'static str)> {
        // Coerce operands to the same width before overflow check.
        // The ay_bindings overflow methods require same-width bitvectors.
        let (lhs, rhs) = Self::coerce_to_match_widths_typed(lhs.clone(), rhs.clone(), is_signed);

        match (op, is_signed) {
            // Unchecked operations use the same overflow checks as regular operations.
            // They emit assertions that overflow does not occur (UB if it does).
            (BinOp::Add | BinOp::AddUnchecked, true) => {
                Some((lhs.bvadd_no_overflow_signed(rhs), "overflow_check_add"))
            }
            (BinOp::Add | BinOp::AddUnchecked, false) => {
                Some((lhs.bvadd_no_overflow_unsigned(rhs), "overflow_check_add"))
            }
            (BinOp::Sub | BinOp::SubUnchecked, true) => {
                Some((lhs.bvsub_no_overflow_signed(rhs), "overflow_check_sub"))
            }
            (BinOp::Sub | BinOp::SubUnchecked, false) => {
                Some((lhs.bvsub_no_underflow_unsigned(rhs), "overflow_check_sub"))
            }
            (BinOp::Mul | BinOp::MulUnchecked, true) => {
                Some((lhs.bvmul_no_overflow_signed(rhs), "overflow_check_mul"))
            }
            (BinOp::Mul | BinOp::MulUnchecked, false) => {
                Some((lhs.bvmul_no_overflow_unsigned(rhs), "overflow_check_mul"))
            }
            // Signed division/remainder overflows when: lhs == INT_MIN && rhs == -1
            // Because |INT_MIN| > INT_MAX (e.g., -(-128i8) = 128 but i8::MAX = 127)
            (BinOp::Div, true) | (BinOp::Rem, true) => {
                let Some(width) = lhs.sort().bitvec_width() else {
                    warn!(
                        op = ?op,
                        lhs_sort = ?lhs.sort(),
                        rhs_sort = ?rhs.sort(),
                        "overflow_check signed Div/Rem requires bitvec operands after coercion"
                    );
                    return None;
                };
                // INT_MIN for width w: 0x80...00 (1 followed by w-1 zeros)
                let int_min = Expr::bitvec_const(1u128 << (width - 1), width);
                // -1 for width w: all ones (use !0 to avoid shift overflow for i128)
                let neg_one = Expr::bitvec_const(!0u128, width);

                // no_overflow = !(lhs == INT_MIN && rhs == -1) = (lhs != INT_MIN) || (rhs != -1)
                let lhs_not_min = lhs.eq(int_min).not();
                let rhs_not_neg_one = rhs.eq(neg_one).not();
                let no_overflow = lhs_not_min.or(rhs_not_neg_one);

                Some((no_overflow, "overflow_check_div"))
            }
            // Unsigned division cannot overflow (division by zero handled separately).
            // Shift, comparison, and bitwise operations don't overflow.
            _ => None, // non-enum: tuple (BinOp, bool)
        }
    }

    /// Emit negation overflow check for unary Neg.
    ///
    /// Emit overflow check for negation (called from codegen_rvalue for UnOp::Neg).
    ///
    /// Signed negation can overflow when negating INT_MIN (e.g., -(-128i8) overflows).
    ///
    /// REQUIRES: operand.sort().is_bitvec()
    /// ENSURES: Adds violation assertion for INT_MIN negation overflow
    pub(super) fn emit_neg_overflow_check(&mut self, operand: &Expr) {
        // Assert: -operand does not overflow (only fails for INT_MIN)
        let no_overflow = operand.clone().bvneg_no_overflow();
        self.record_violation_guarded(no_overflow.not(), "overflow_check_neg");
    }
}
