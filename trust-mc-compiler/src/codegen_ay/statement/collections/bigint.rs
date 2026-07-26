// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! BigInt/BigUint semantic model for AY codegen.
//!
//! BigInt operations are modeled using SMT Int theory, which provides
//! arbitrary-precision arithmetic. This enables verification of code
//! using num-bigint without state explosion.
//!
//! Part of #470: BigInt verification via interception pattern.
//! Part of #933: BigUint operations enforce non-negativity constraints.
//! Part of #1354: Statement module refactoring.

use crate::codegen_ay::context::AYCtx;
use crate::codegen_ay::stubs::StubKind;
use ay_bindings::Expr;
use num_bigint::BigInt;
use rustc_public::mir::{BasicBlockIdx, Operand, Place};
use tracing::warn;

use crate::codegen_ay::types::int_sort;

use super::super::StatementCodegen;

/// Binary operation function: `(lhs, rhs) -> result`.
type BinaryIntOp = fn(Expr, Expr) -> Expr;

/// Table mapping StubKind → binary Int operation for BMC BigInt dispatch.
///
/// Covers arithmetic (Add/Sub/Mul) and comparisons (Eq/Lt/Le/Gt/Ge).
/// All share: resolve 2 args, apply op, assign to destination, assert nonneg.
/// Div/Rem excluded — they require extra zero-division checks.
const BIGINT_BINARY_OPS: &[(StubKind, BinaryIntOp)] = &[
    (StubKind::BigIntAdd, Expr::int_add),
    (StubKind::BigIntSub, Expr::int_sub),
    (StubKind::BigIntMul, Expr::int_mul),
    (StubKind::BigIntEq, Expr::eq),
    (StubKind::BigIntLt, Expr::int_lt),
    (StubKind::BigIntLe, Expr::int_le),
    (StubKind::BigIntGt, Expr::int_gt),
    (StubKind::BigIntGe, Expr::int_ge),
];

/// Table mapping compound-assign StubKind → binary Int operation.
const BIGINT_COMPOUND_ASSIGN_OPS: &[(StubKind, BinaryIntOp)] = &[
    (StubKind::BigIntAddAssign, Expr::int_add),
    (StubKind::BigIntSubAssign, Expr::int_sub),
    (StubKind::BigIntMulAssign, Expr::int_mul),
];

/// Lookup a binary operation for a StubKind in a table.
fn lookup_binary_op(table: &[(StubKind, BinaryIntOp)], stub: StubKind) -> Option<BinaryIntOp> {
    table.iter().find(|(s, _)| *s == stub).map(|(_, op)| *op)
}

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Check if a callee path refers to a specific type name as a standalone segment.
    ///
    /// This avoids false positives for wrapper types like `MyBigUintWrapper`.
    pub(in super::super) fn callee_path_contains_type(callee_path: &str, type_name: &str) -> bool {
        let mut token = String::new();
        for ch in callee_path.chars() {
            if ch.is_ascii_alphanumeric() || ch == '_' {
                token.push(ch);
            } else {
                if token == type_name {
                    return true;
                }
                token.clear();
            }
        }
        token == type_name
    }

    /// Assert that an expression is non-negative when modeling BigUint values.
    pub(in super::super) fn assert_nonneg_if_biguint(
        ctx: &mut AYCtx,
        expr: &Expr,
        is_biguint: bool,
    ) {
        if is_biguint {
            ctx.assert(expr.clone().int_ge(Expr::int_const(0)));
        }
    }

    /// Codegen BigInt operations by intercepting and replacing with AY Int operations.
    ///
    /// Part of #470: BigInt verification via interception pattern.
    /// Part of #933: BigUint operations now enforce non-negativity constraints.
    /// Binary ops use table-driven dispatch per #2268.
    pub(in crate::codegen_ay::statement) fn codegen_bigint_stub(
        &mut self,
        stub_kind: StubKind,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
        callee_path: &str,
    ) -> Option<BasicBlockIdx> {
        use StubKind::{
            BigIntAbs, BigIntAdd, BigIntAddAssign, BigIntBitAnd, BigIntBitOr, BigIntBitXor,
            BigIntClone, BigIntCmp, BigIntDiv, BigIntEq, BigIntFrom, BigIntGe, BigIntGt,
            BigIntIsNegative, BigIntIsZero, BigIntLe, BigIntLt, BigIntMul, BigIntMulAssign,
            BigIntNeg, BigIntOne, BigIntPartialCmp, BigIntRem, BigIntShl, BigIntShlAssign,
            BigIntShr, BigIntShrAssign, BigIntSub, BigIntSubAssign, BigIntZero,
        };

        // #933: Check if this is a BigUint operation - if so, we'll constrain results to >= 0
        let is_biguint = Self::callee_path_contains_type(callee_path, "BigUint");

        // Table-driven: arithmetic (Add/Sub/Mul) and comparisons (Eq/Lt/Le/Gt/Ge).
        // Pattern: resolve 2 args, apply op, assign to dest, assert nonneg.
        if let Some(op) = lookup_binary_op(BIGINT_BINARY_OPS, stub_kind) {
            if args.len() < 2 {
                return None;
            }
            let lhs = self.get_bigint_value(&args[0])?;
            let rhs = self.get_bigint_value(&args[1])?;
            let result = op(lhs, rhs);
            Self::assert_nonneg_if_biguint(self.ctx, &result, is_biguint);
            self.assign_value_to_place(destination, result);
            return target;
        }

        // Table-driven: compound assigns (AddAssign/SubAssign/MulAssign).
        // Pattern: resolve 2 args, apply op, assert nonneg, assign to ref target.
        if let Some(op) = lookup_binary_op(BIGINT_COMPOUND_ASSIGN_OPS, stub_kind) {
            if args.len() < 2 {
                return None;
            }
            let lhs = self.get_bigint_value(&args[0])?;
            let rhs = self.get_bigint_value(&args[1])?;
            let result = op(lhs, rhs);
            Self::assert_nonneg_if_biguint(self.ctx, &result, is_biguint);
            self.assign_ref_target(&args[0], result)?;
            return target;
        }

        match stub_kind {
            BigIntFrom => {
                if args.is_empty() {
                    return None;
                }
                let arg = self.codegen_operand(&args[0])?;
                let int_expr = if arg.sort().is_bitvec() {
                    let is_signed = self.operand_signedness(&args[0]).unwrap_or_else(|| {
                        warn!(
                            operand = ?args[0],
                            "BigInt::from bitvec signedness unknown, defaulting to signed"
                        );
                        true
                    });
                    self.bitvec_to_int_with_signedness(arg, is_signed)
                } else if arg.sort().is_int() {
                    arg
                } else {
                    return None;
                };
                Self::assert_nonneg_if_biguint(self.ctx, &int_expr, is_biguint);
                self.assign_value_to_place(destination, int_expr);
                target
            }
            BigIntOne => {
                self.assign_value_to_place(destination, Expr::int_const(1));
                target
            }
            BigIntZero => {
                self.assign_value_to_place(destination, Expr::int_const(0));
                target
            }
            BigIntIsZero => {
                if args.is_empty() {
                    return None;
                }
                let arg = self.get_bigint_value(&args[0])?;
                Self::assert_nonneg_if_biguint(self.ctx, &arg, is_biguint);
                self.assign_value_to_place(destination, arg.eq(Expr::int_const(0)));
                target
            }
            BigIntIsNegative => {
                if args.is_empty() {
                    return None;
                }
                let arg = self.get_bigint_value(&args[0])?;
                Self::assert_nonneg_if_biguint(self.ctx, &arg, is_biguint);
                self.assign_value_to_place(destination, arg.int_lt(Expr::int_const(0)));
                target
            }
            // Div/Rem require extra zero-division checks — not table-driven.
            BigIntDiv => {
                if args.len() < 2 {
                    return None;
                }
                let lhs = self.get_bigint_value(&args[0])?;
                let rhs = self.get_bigint_value(&args[1])?;
                let div_by_zero = rhs.clone().eq(Expr::int_const(0));
                self.record_violation_guarded(div_by_zero, "bigint_div_by_zero");
                let result = lhs.int_div(rhs);
                Self::assert_nonneg_if_biguint(self.ctx, &result, is_biguint);
                self.assign_value_to_place(destination, result);
                target
            }
            BigIntRem => {
                if args.len() < 2 {
                    return None;
                }
                let lhs = self.get_bigint_value(&args[0])?;
                let rhs = self.get_bigint_value(&args[1])?;
                let div_by_zero = rhs.clone().eq(Expr::int_const(0));
                self.record_violation_guarded(div_by_zero, "bigint_mod_by_zero");
                let result = lhs.int_mod(rhs);
                Self::assert_nonneg_if_biguint(self.ctx, &result, is_biguint);
                self.assign_value_to_place(destination, result);
                target
            }
            BigIntNeg => {
                if args.is_empty() {
                    return None;
                }
                let arg = self.get_bigint_value(&args[0])?;
                if is_biguint {
                    let operand_positive = arg.clone().int_gt(Expr::int_const(0));
                    self.record_violation_guarded(operand_positive, "biguint_neg_positive");
                }
                let result = arg.int_neg();
                Self::assert_nonneg_if_biguint(self.ctx, &result, is_biguint);
                self.assign_value_to_place(destination, result);
                target
            }
            BigIntAbs => {
                if args.is_empty() {
                    return None;
                }
                let arg = self.get_bigint_value(&args[0])?;
                let zero = Expr::int_const(0);
                let is_neg = arg.clone().int_lt(zero);
                let negated = arg.clone().int_neg();
                let abs_expr = Expr::ite(is_neg, negated, arg);
                Self::assert_nonneg_if_biguint(self.ctx, &abs_expr, is_biguint);
                self.assign_value_to_place(destination, abs_expr);
                target
            }
            BigIntCmp | BigIntPartialCmp => {
                // Ordering encoded as bitvec(8): Less=0xFF, Equal=0, Greater=1
                // Must match comparison.rs codegen_ord_cmp output sort (issue #736)
                if args.len() < 2 {
                    return None;
                }
                let lhs = self.get_bigint_value(&args[0])?;
                let rhs = self.get_bigint_value(&args[1])?;
                let cmp_result = Expr::ite(
                    lhs.clone().int_lt(rhs.clone()),
                    Expr::bitvec_const(-1i128 as u128 & 0xFF, 8),
                    Expr::ite(lhs.eq(rhs), Expr::bitvec_const(0, 8), Expr::bitvec_const(1, 8)),
                );
                self.assign_value_to_place(destination, cmp_result);
                target
            }
            BigIntClone => {
                if args.is_empty() {
                    return None;
                }
                let arg = self.get_bigint_value(&args[0])?;
                Self::assert_nonneg_if_biguint(self.ctx, &arg, is_biguint);
                self.assign_value_to_place(destination, arg);
                target
            }
            // Shift and bitwise operations delegated to bigint_shift.rs
            BigIntShl | BigIntShr | BigIntShlAssign | BigIntShrAssign | BigIntBitAnd
            | BigIntBitOr | BigIntBitXor => {
                self.codegen_bigint_shift_stub(stub_kind, args, destination, target, is_biguint)
            }
            // Table-driven ops handled above; explicit unreachable for compile-time coverage.
            BigIntAdd | BigIntSub | BigIntMul | BigIntEq | BigIntLt | BigIntLe | BigIntGt
            | BigIntGe | BigIntAddAssign | BigIntSubAssign | BigIntMulAssign => {
                unreachable!("handled by BIGINT_BINARY_OPS / BIGINT_COMPOUND_ASSIGN_OPS table")
            }
            _ => None, // internal enum: StubKind (BigInt subset partial dispatch)
        }
    }

    /// Convert a bitvector expression to an Int, using signedness to interpret the value.
    #[must_use]
    pub(in super::super) fn bitvec_to_int_with_signedness(
        &self,
        expr: Expr,
        is_signed: bool,
    ) -> Expr {
        if !expr.sort().is_bitvec() {
            return expr;
        }
        let width = expr.sort().bitvec_width().unwrap_or(0);
        if is_signed && width > 0 {
            let sign_bit = expr.clone().extract(width - 1, width - 1).eq(Expr::bitvec_const(1, 1));
            let unsigned = expr.bv2int();
            let modulus = Expr::int_const(BigInt::from(1u8) << (width as usize));
            let signed_val = unsigned.clone().int_sub(modulus);
            Expr::ite(sign_bit, signed_val, unsigned)
        } else {
            expr.bv2int()
        }
    }

    /// Get a BigInt value from an operand, handling references.
    ///
    /// If the operand cannot be resolved to an Int expression, creates an unconstrained
    /// symbolic variable as a fallback. This is an over-approximation that may hide bugs.
    #[must_use]
    pub(in super::super) fn get_bigint_value(&mut self, operand: &Operand) -> Option<Expr> {
        if let Some(expr) = self.codegen_operand(operand) {
            if expr.sort().is_int() {
                return Some(expr);
            }
            if expr.sort().is_bitvec() {
                let is_signed = self.operand_signedness(operand).unwrap_or_else(|| {
                    warn!(
                        operand = ?operand,
                        "BigInt operand bitvec signedness unknown, defaulting to signed"
                    );
                    true
                });
                return Some(self.bitvec_to_int_with_signedness(expr, is_signed));
            }
        }
        if let Some(expr) = self.get_value_through_ref(operand) {
            if expr.sort().is_int() {
                return Some(expr);
            }
            if expr.sort().is_bitvec() {
                let is_signed = self.operand_signedness(operand).unwrap_or_else(|| {
                    warn!(
                        operand = ?operand,
                        "BigInt operand ref bitvec signedness unknown, defaulting to signed"
                    );
                    true
                });
                return Some(self.bitvec_to_int_with_signedness(expr, is_signed));
            }
        }
        // Issue #739: Fallback creates unconstrained variable - emit warning for visibility
        let var_name = self.ctx.fresh_name("bigint_symbolic");
        warn!(
            operand = ?operand,
            var_name = %var_name,
            "BigInt operand could not be resolved to Int; creating unconstrained symbolic variable (over-approximation)"
        );
        Some(self.ctx.declare_var(&var_name, int_sort()))
    }

    /// Assign a value to the target of a reference operand.
    pub(in super::super) fn assign_ref_target(
        &mut self,
        operand: &Operand,
        value: Expr,
    ) -> Option<()> {
        if let Operand::Copy(place) | Operand::Move(place) = operand {
            self.assign_value_to_place(place, value);
            Some(())
        } else {
            warn!("assign_ref_target: could not determine target place");
            Some(())
        }
    }
}
