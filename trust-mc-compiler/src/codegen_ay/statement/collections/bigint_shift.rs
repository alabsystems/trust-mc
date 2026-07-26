// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! BigInt shift and bitwise operations for AY codegen.
//!
//! Extracted from `bigint.rs`. Handles:
//! - Shift operations: Shl, Shr, ShlAssign, ShrAssign
//! - Bitwise operations: BitAnd, BitOr, BitXor
//!
//! Part of #742: BigInt bit operations.
//! Part of #933: BigUint non-negativity constraints.

use crate::codegen_ay::stubs::StubKind;
use ay_bindings::Expr;
use rustc_public::mir::{BasicBlockIdx, Operand, Place};
use tracing::warn;

use super::super::StatementCodegen;
use crate::codegen_ay::types::int_sort;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Emit left-shift constraints and return the result expression.
    ///
    /// Models `lhs << rhs` with:
    /// - Negative shift violation guard
    /// - Zero-shift identity: rhs == 0 ⟹ result == lhs
    /// - Growth: lhs > 0 ∧ rhs > 0 ⟹ result > lhs
    /// - Negative shrink: lhs < 0 ∧ rhs > 0 ⟹ result < lhs
    #[must_use]
    fn emit_shl_constraints(
        &mut self,
        lhs: Expr,
        rhs: Expr,
        result_prefix: &str,
        violation_label: &str,
        is_biguint: bool,
    ) -> Expr {
        // Assert shift amount is non-negative (negative shift is UB)
        let neg_shift = rhs.clone().int_lt(Expr::int_const(0));
        self.record_violation_guarded(neg_shift, violation_label);
        // result = lhs * 2^rhs (SMT-LIB has no int pow; model with constraints)
        let result_name = self.ctx.fresh_name(result_prefix);
        let result = self.ctx.declare_var(&result_name, int_sort());
        // Constraint: if rhs == 0 then result == lhs
        let zero_shift = rhs.clone().eq(Expr::int_const(0));
        self.ctx.assert(Expr::ite(
            zero_shift,
            result.clone().eq(lhs.clone()),
            Expr::bool_const(true),
        ));
        // Constraint: if lhs > 0 and rhs > 0 then result > lhs (left shift grows)
        let lhs_pos = lhs.clone().int_gt(Expr::int_const(0));
        let rhs_pos = rhs.int_gt(Expr::int_const(0));
        let growth = result.clone().int_gt(lhs.clone());
        self.ctx.assert(Expr::ite(lhs_pos.and(rhs_pos.clone()), growth, Expr::bool_const(true)));
        // Constraint: if lhs < 0 and rhs > 0 then result < lhs (negative gets more negative)
        let lhs_neg = lhs.clone().int_lt(Expr::int_const(0));
        let shrink = result.clone().int_lt(lhs);
        self.ctx.assert(Expr::ite(lhs_neg.and(rhs_pos), shrink, Expr::bool_const(true)));
        // #933: BigUint result must be non-negative
        Self::assert_nonneg_if_biguint(self.ctx, &result, is_biguint);
        result
    }

    /// Emit right-shift constraints and return the result expression.
    ///
    /// Models `lhs >> rhs` with:
    /// - Negative shift violation guard
    /// - Zero-shift identity: rhs == 0 ⟹ result == lhs
    /// - Non-negative bounds: lhs ≥ 0 ∧ rhs > 0 ⟹ 0 ≤ result ≤ lhs
    /// - Negative bounds: lhs < 0 ∧ rhs > 0 ⟹ result < 0 ∧ result ≥ lhs
    #[must_use]
    fn emit_shr_constraints(
        &mut self,
        lhs: Expr,
        rhs: Expr,
        result_prefix: &str,
        violation_label: &str,
        is_biguint: bool,
    ) -> Expr {
        // Assert shift amount is non-negative
        let neg_shift = rhs.clone().int_lt(Expr::int_const(0));
        self.record_violation_guarded(neg_shift, violation_label);
        // Right shift: result = floor(lhs / 2^rhs) — approximation with constraints
        let result_name = self.ctx.fresh_name(result_prefix);
        let result = self.ctx.declare_var(&result_name, int_sort());
        // Constraint: if rhs == 0 then result == lhs
        let zero_shift = rhs.clone().eq(Expr::int_const(0));
        self.ctx.assert(Expr::ite(
            zero_shift,
            result.clone().eq(lhs.clone()),
            Expr::bool_const(true),
        ));
        // Constraint: if lhs >= 0 and rhs > 0 then 0 <= result <= lhs (right shift shrinks)
        let lhs_nonneg = lhs.clone().int_ge(Expr::int_const(0));
        let rhs_pos = rhs.int_gt(Expr::int_const(0));
        let nonneg_bounds =
            result.clone().int_ge(Expr::int_const(0)).and(result.clone().int_le(lhs.clone()));
        self.ctx.assert(Expr::ite(
            lhs_nonneg.clone().and(rhs_pos.clone()),
            nonneg_bounds,
            Expr::bool_const(true),
        ));
        // Constraint: if lhs < 0 and rhs > 0 then result < 0 and result >= lhs (arithmetic shift)
        let lhs_neg = lhs_nonneg.not();
        let neg_bounds = result.clone().int_lt(Expr::int_const(0)).and(result.clone().int_ge(lhs));
        self.ctx.assert(Expr::ite(lhs_neg.and(rhs_pos), neg_bounds, Expr::bool_const(true)));
        // #933: BigUint result must be non-negative
        Self::assert_nonneg_if_biguint(self.ctx, &result, is_biguint);
        result
    }

    /// Codegen BigInt shift and bitwise operations.
    ///
    /// Delegated from `codegen_bigint_stub` for shift/bitwise variants.
    pub(in super::super) fn codegen_bigint_shift_stub(
        &mut self,
        stub_kind: StubKind,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
        is_biguint: bool,
    ) -> Option<BasicBlockIdx> {
        use StubKind::{
            BigIntBitAnd, BigIntBitOr, BigIntBitXor, BigIntShl, BigIntShlAssign, BigIntShr,
            BigIntShrAssign,
        };

        match stub_kind {
            BigIntShl => {
                if args.len() < 2 {
                    return None;
                }
                let lhs = self.get_bigint_value(&args[0])?;
                let rhs = self.get_bigint_value(&args[1])?;
                let result = self.emit_shl_constraints(
                    lhs,
                    rhs,
                    "bigint_shl",
                    "bigint_shl_negative_shift",
                    is_biguint,
                );
                self.assign_value_to_place(destination, result);
                target
            }
            BigIntShr => {
                if args.len() < 2 {
                    return None;
                }
                let lhs = self.get_bigint_value(&args[0])?;
                let rhs = self.get_bigint_value(&args[1])?;
                let result = self.emit_shr_constraints(
                    lhs,
                    rhs,
                    "bigint_shr",
                    "bigint_shr_negative_shift",
                    is_biguint,
                );
                self.assign_value_to_place(destination, result);
                target
            }
            BigIntShlAssign => {
                if args.len() < 2 {
                    return None;
                }
                let lhs = self.get_bigint_value(&args[0])?;
                let rhs = self.get_bigint_value(&args[1])?;
                let result = self.emit_shl_constraints(
                    lhs,
                    rhs,
                    "bigint_shl_assign",
                    "bigint_shl_assign_negative_shift",
                    is_biguint,
                );
                self.assign_ref_target(&args[0], result)?;
                target
            }
            BigIntShrAssign => {
                if args.len() < 2 {
                    return None;
                }
                let lhs = self.get_bigint_value(&args[0])?;
                let rhs = self.get_bigint_value(&args[1])?;
                let result = self.emit_shr_constraints(
                    lhs,
                    rhs,
                    "bigint_shr_assign",
                    "bigint_shr_assign_negative_shift",
                    is_biguint,
                );
                self.assign_ref_target(&args[0], result)?;
                target
            }
            // Bitwise operations (Part of #742)
            // Note: Bitwise ops on unbounded Int don't have standard SMT semantics.
            // We model them as unconstrained (nondet) which is a sound over-approximation.
            BigIntBitAnd | BigIntBitOr | BigIntBitXor => {
                if args.len() < 2 {
                    return None;
                }
                // Validate operands are valid BigInt values (even though result is nondet)
                let _lhs = self.get_bigint_value(&args[0])?;
                let _rhs = self.get_bigint_value(&args[1])?;
                let op_name = match stub_kind {
                    BigIntBitAnd => "bitand",
                    BigIntBitOr => "bitor",
                    BigIntBitXor => "bitxor",
                    _other => {
                        // partial dispatch: StubKind
                        warn!(
                            ?_other,
                            "BigInt bitwise: unexpected stub in BitAnd|BitOr|BitXor arm"
                        );
                        return None;
                    }
                };
                warn!(
                    op = op_name,
                    "BigInt bitwise operation has no standard SMT semantics for unbounded Int; modeling as nondet"
                );
                // Create unconstrained symbolic value
                let result_name = self.ctx.fresh_name_with_suffix("bigint", op_name);
                let result = self.ctx.declare_var(&result_name, int_sort());
                // #933: BigUint bitwise result must be non-negative
                Self::assert_nonneg_if_biguint(self.ctx, &result, is_biguint);
                self.assign_value_to_place(destination, result);
                target
            }
            _other => {
                // partial dispatch: StubKind
                warn!(
                    ?stub_kind,
                    "codegen_bigint_shift_stub: unexpected stub kind — update bigint.rs routing"
                );
                None
            }
        }
    }
}
