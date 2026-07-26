// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! BMC encoding handlers for `wrapping_abs`, `wrapping_neg`, `div_euclid`,
//! and `rem_euclid` (Part of #3186).
//!
//! Mirrors the CHC handlers at:
//! - `chc/call/codegen_call_cmp_string/wrapping_abs.rs`
//! - `chc/call/codegen_call_cmp_string/div_euclid.rs`
//!
//! These methods produce branching MIR bodies that the BMC path cannot inline,
//! falling through to the unsupported-construct fallback. This module intercepts
//! the calls and provides direct bitvector encoding:
//!
//! - `wrapping_abs(x)` → `ite(bvslt(x, 0), bvneg(x), x)`
//! - `wrapping_neg(x)` → `bvneg(x)`
//! - `div_euclid(a, b)` → unsigned: `bvudiv(a, b)`, signed: adjusted quotient
//! - `rem_euclid(a, b)` → unsigned: `bvurem(a, b)`, signed: adjusted remainder

use ay_bindings::Expr;
use rustc_public::mir::{BasicBlockIdx, Operand, Place};
use tracing::debug;

use crate::codegen_ay::statement::StatementCodegen;
use crate::codegen_ay::types::coerce_bitvec_width_safe;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Try to intercept `wrapping_abs`, `wrapping_neg`, `div_euclid`, or
    /// `rem_euclid` calls before they fall through to the unsupported fallback.
    ///
    /// Returns `Some(target_bb)` if handled, `None` otherwise.
    pub(in crate::codegen_ay::statement) fn try_codegen_math_unary_call(
        &mut self,
        func: &Operand,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        let callee_path = self.resolve_callee_path(func)?;
        let method = callee_path.rsplit("::").next()?;

        match method {
            "wrapping_abs" if !args.is_empty() => {
                self.codegen_wrapping_abs_bmc(&args[0], destination);
                debug!("wrapping_abs: encoded (BMC)");
                target
            }
            "wrapping_neg" if !args.is_empty() => {
                self.codegen_wrapping_neg_bmc(&args[0], destination);
                debug!("wrapping_neg: encoded (BMC)");
                target
            }
            "div_euclid" if args.len() >= 2 => {
                self.codegen_euclid_bmc(&args[0], &args[1], destination, EuclidOp::Div);
                debug!("div_euclid: encoded (BMC)");
                target
            }
            "rem_euclid" if args.len() >= 2 => {
                self.codegen_euclid_bmc(&args[0], &args[1], destination, EuclidOp::Rem);
                debug!("rem_euclid: encoded (BMC)");
                target
            }
            _ => None,
        }
    }

    /// Encode `wrapping_abs(x)` as `ite(bvslt(x, 0), bvneg(x), x)`.
    ///
    /// `wrapping_abs` is defined only on signed integer types. For the minimum
    /// value (e.g., `i8::MIN`), `wrapping_abs` wraps: `(-128i8).wrapping_abs() == -128`.
    /// Bitvector `bvneg` correctly models this two's complement wrapping.
    fn codegen_wrapping_abs_bmc(&mut self, arg: &Operand, destination: &Place) {
        let Some(x) = self.codegen_operand(arg) else {
            self.codegen_symbolic_result(destination);
            return;
        };
        if !x.sort().is_bitvec() {
            self.codegen_symbolic_result(destination);
            return;
        }
        let w = x.sort().bitvec_width().expect("invariant: is_bitvec guard");
        let zero = Expr::bitvec_const(0u128, w);
        let is_neg = x.clone().bvslt(zero);
        let negated = x.clone().bvneg();
        let result = Expr::ite(is_neg, negated, x);
        self.assign_value_to_place(destination, result);
    }

    /// Encode `wrapping_neg(x)` as `bvneg(x)`.
    fn codegen_wrapping_neg_bmc(&mut self, arg: &Operand, destination: &Place) {
        let Some(x) = self.codegen_operand(arg) else {
            self.codegen_symbolic_result(destination);
            return;
        };
        if !x.sort().is_bitvec() {
            self.codegen_symbolic_result(destination);
            return;
        }
        let result = x.bvneg();
        self.assign_value_to_place(destination, result);
    }

    /// Encode `div_euclid`/`rem_euclid` with correct Euclidean semantics.
    ///
    /// - **Unsigned**: identical to `bvudiv`/`bvurem`.
    /// - **Signed `div_euclid(a, b)`**:
    ///   `q = bvsdiv(a, b); r = bvsrem(a, b); ite(r < 0, ite(b > 0, q-1, q+1), q)`
    /// - **Signed `rem_euclid(a, b)`**:
    ///   `r = bvsrem(a, b); ite(r < 0, ite(b < 0, r-b, r+b), r)`
    fn codegen_euclid_bmc(
        &mut self,
        lhs_op: &Operand,
        rhs_op: &Operand,
        destination: &Place,
        op: EuclidOp,
    ) {
        let Some(lhs) = self.codegen_operand(lhs_op) else {
            self.codegen_symbolic_result(destination);
            return;
        };
        let Some(rhs) = self.codegen_operand(rhs_op) else {
            self.codegen_symbolic_result(destination);
            return;
        };
        if !lhs.sort().is_bitvec() || !rhs.sort().is_bitvec() {
            self.codegen_symbolic_result(destination);
            return;
        }

        // Determine signedness from operand type.
        let is_signed = self.operand_signedness(lhs_op).unwrap_or(false);

        // Coerce both operands to the wider width.
        let lhs_w = lhs.sort().bitvec_width().expect("invariant: is_bitvec guard");
        let rhs_w = rhs.sort().bitvec_width().expect("invariant: is_bitvec guard");
        let target_width = lhs_w.max(rhs_w);
        let a = coerce_bitvec_width_safe(lhs, target_width, is_signed.into());
        let b = coerce_bitvec_width_safe(rhs, target_width, is_signed.into());

        // UB: division by zero (b == 0).
        let label = match op {
            EuclidOp::Div => "div_euclid_zero",
            EuclidOp::Rem => "rem_euclid_zero",
        };
        self.emit_division_by_zero_check(&b, label);

        // UB: signed overflow (a == T::MIN && b == -1).
        if is_signed {
            let t_min = Expr::bitvec_const(1u128 << (target_width - 1), target_width);
            let neg_one = Expr::bitvec_const(!0u128 >> (128 - target_width), target_width);
            let overflow = a.clone().eq(t_min).and(b.clone().eq(neg_one));
            let overflow_label = match op {
                EuclidOp::Div => "div_euclid_overflow",
                EuclidOp::Rem => "rem_euclid_overflow",
            };
            self.record_violation_guarded(overflow, overflow_label);
        }

        let result = if !is_signed {
            // Unsigned: Euclidean == truncated.
            match op {
                EuclidOp::Div => a.bvudiv(b),
                EuclidOp::Rem => a.bvurem(b),
            }
        } else {
            let zero = Expr::bitvec_const(0u128, target_width);
            let one = Expr::bitvec_const(1u128, target_width);
            match op {
                EuclidOp::Div => {
                    // q = bvsdiv(a, b); r = bvsrem(a, b)
                    // result = ite(r < 0, ite(b > 0, q - 1, q + 1), q)
                    let q = a.clone().bvsdiv(b.clone());
                    let r = a.bvsrem(b.clone());
                    let r_neg = r.bvslt(zero);
                    let b_pos = b.bvsgt(Expr::bitvec_const(0u128, target_width));
                    let q_minus_1 = q.clone().bvsub(one.clone());
                    let q_plus_1 = q.clone().bvadd(one);
                    let adjusted = Expr::ite(b_pos, q_minus_1, q_plus_1);
                    Expr::ite(r_neg, adjusted, q)
                }
                EuclidOp::Rem => {
                    // r = bvsrem(a, b)
                    // result = ite(r < 0, ite(b < 0, r - b, r + b), r)
                    let r = a.bvsrem(b.clone());
                    let r_neg = r.clone().bvslt(zero);
                    let b_neg = b.clone().bvslt(Expr::bitvec_const(0u128, target_width));
                    let r_minus_b = r.clone().bvsub(b.clone());
                    let r_plus_b = r.clone().bvadd(b);
                    let adjusted = Expr::ite(b_neg, r_minus_b, r_plus_b);
                    Expr::ite(r_neg, adjusted, r)
                }
            }
        };

        self.assign_value_to_place(destination, result);
    }
}

/// Whether we are encoding `div_euclid` or `rem_euclid`.
#[derive(Debug, Clone, Copy)]
enum EuclidOp {
    Div,
    Rem,
}
