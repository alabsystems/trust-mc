// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Arithmetic and comparison binary operations + width coercion helpers.
//!
//! Split from codegen_stmt.rs per #2036. Checked binop, unop, PtrMetadata,
//! and cast extracted to codegen_stmt_arithmetic_ops.rs per #2246.
//!
//! Contains: translate_binop.
//!
//! Width coercion and overflow helpers extracted to
//! `codegen_stmt_arithmetic_coerce.rs` per #4130.
//!
//! Migrated from include!() to proper module.
//! Part of #2306: include!() to proper module migration.

use ay_bindings::{Expr, ExprValue, Sort};
use rustc_public::mir::BinOp;

use crate::codegen_ay::types::coerce_int_real;

use super::super::fieldless_constructor_cmp::try_fieldless_constructor_comparison;
use super::ChcCtx;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    fn unsigned_rem_pow2_mask(lhs: Expr, rhs: &Expr) -> Option<Expr> {
        let ExprValue::BitVecConst { value, width } = rhs.value() else {
            return None;
        };
        let divisor = u128::try_from(value).ok()?;
        if divisor == 0 || !divisor.is_power_of_two() {
            return None;
        }
        Some(lhs.bvand(Expr::bitvec_const(divisor - 1, *width)))
    }

    /// Translates a binary operation to a AY expression.
    ///
    /// `is_signed`: signed vs unsigned BV semantics for div/rem/shr/cmp (#666).
    /// `is_float`: when true, Div/Rem on BVs return None (float BV ops are unsound, #3668).
    /// `int_bv_width`: BV width for Int↔BV round-trips on Int-lifted locals (#3043).
    pub(in crate::codegen_ay::chc) fn translate_binop(
        &self,
        op: BinOp,
        lhs: Expr,
        rhs: Expr,
        is_signed: bool,
        int_bv_width: u32,
        is_float: bool,
    ) -> Option<Expr> {
        // Part of #2875: Coerce mixed Int/BV operands to a common domain.
        // Int-lifted locals (from Range Int-propagation) produce Int expressions,
        // but constants and non-lifted locals may still be BV. Lift BV→Int so both
        // operands are in the same domain. This must happen before the is_bv check.
        // Part of #3055: Use signed/unsigned bv2int based on operand signedness.
        let bv_to_int =
            |bv: Expr| -> Expr { if is_signed { bv.bv2int_signed() } else { bv.bv2int() } };
        let (lhs, rhs) = if lhs.sort().is_int() && rhs.sort().is_bitvec() {
            (lhs, bv_to_int(rhs))
        } else if lhs.sort().is_bitvec() && rhs.sort().is_int() {
            (bv_to_int(lhs), rhs)
        } else {
            (lhs, rhs)
        };

        // Dispatch to Int or BitVec methods based on sort
        let is_bv = lhs.sort().is_bitvec();
        let is_bool = lhs.sort().is_bool();
        if is_bv && !rhs.sort().is_bitvec() {
            return None;
        }

        // Part of #2007, #3589: Coerce BV operands to matching widths.
        // Skip shifts — they coerce via coerce_shift_amount (RHS → LHS width).
        let is_shift =
            matches!(op, BinOp::Shl | BinOp::ShlUnchecked | BinOp::Shr | BinOp::ShrUnchecked);
        let (lhs, rhs) = if is_bv && !is_shift {
            Self::coerce_arithmetic_operands(lhs, rhs, is_signed)
        } else {
            (lhs, rhs)
        };

        // Part of #3839: CHC-safe float encoding — exact constant fold for
        // concrete operands, congruent unconstrained-table application for
        // symbolic ones (sound for proofs; see float_binop_table.rs). The
        // symbolic lane carries a Kani --nan-check parity obligation emitted
        // by emit_assignment_safety_checks.
        if is_float && is_bv {
            use crate::codegen_ay::float_arithmetic::is_float_arithmetic_op;
            if is_float_arithmetic_op(op) {
                return self.float_binop_chc_term(op, lhs, rhs, int_bv_width);
            }
        }

        Some(match op {
            BinOp::Add | BinOp::AddUnchecked => {
                if is_bv {
                    lhs.bvadd(rhs)
                } else {
                    let (lhs, rhs) = coerce_int_real(lhs, rhs);
                    if lhs.sort().is_real() {
                        lhs.real_add(rhs)
                    } else if lhs.sort().is_int() {
                        lhs.int_add(rhs)
                    } else {
                        return None;
                    }
                }
            }
            BinOp::Sub | BinOp::SubUnchecked => {
                if is_bv {
                    lhs.bvsub(rhs)
                } else {
                    let (lhs, rhs) = coerce_int_real(lhs, rhs);
                    if lhs.sort().is_real() {
                        lhs.real_sub(rhs)
                    } else if lhs.sort().is_int() {
                        lhs.int_sub(rhs)
                    } else {
                        return None;
                    }
                }
            }
            BinOp::Mul | BinOp::MulUnchecked => {
                if is_bv {
                    lhs.bvmul(rhs)
                } else {
                    let (lhs, rhs) = coerce_int_real(lhs, rhs);
                    if lhs.sort().is_real() {
                        lhs.real_mul(rhs)
                    } else if lhs.sort().is_int() {
                        lhs.int_mul(rhs)
                    } else {
                        return None;
                    }
                }
            }
            BinOp::Div => {
                if is_bv {
                    if is_signed { lhs.bvsdiv(rhs) } else { lhs.bvudiv(rhs) }
                } else {
                    let (lhs, rhs) = coerce_int_real(lhs, rhs);
                    if lhs.sort().is_real() {
                        lhs.real_div(rhs)
                    } else if lhs.sort().is_int() {
                        lhs.int_div(rhs)
                    } else {
                        return None;
                    }
                }
            }
            BinOp::Rem => {
                if lhs.sort().is_int() {
                    lhs.int_mod(rhs)
                } else if is_bv {
                    if is_signed {
                        lhs.bvsrem(rhs)
                    } else if let Some(masked) = Self::unsigned_rem_pow2_mask(lhs.clone(), &rhs) {
                        masked
                    } else {
                        lhs.bvurem(rhs)
                    }
                } else {
                    return None;
                }
            }
            // Bitwise ops on bitvectors or booleans (#1889)
            // MIR uses BitAnd for both integer bitwise AND and boolean && (short-circuit)
            // Part of #1894: Add width coercion for bitvector bitwise ops
            BinOp::BitAnd => {
                if is_bv {
                    let (lhs, rhs) = Self::coerce_bitwise_operands(lhs, rhs, is_signed);
                    lhs.bvand(rhs)
                } else if is_bool {
                    lhs.and(rhs)
                } else if lhs.sort().is_int() && rhs.sort().is_int() {
                    // Part of #2875, #3043: Int-lifted locals need BV bitwise ops.
                    // Convert Int→BV at MIR-derived width, perform bitwise, convert back.
                    // Part of #3055: use unsigned bv2int for unsigned types.
                    let lhs_bv = lhs.int2bv(int_bv_width);
                    let rhs_bv = rhs.int2bv(int_bv_width);
                    bv_to_int(lhs_bv.bvand(rhs_bv))
                } else {
                    return None;
                }
            }
            BinOp::BitOr => {
                if is_bv {
                    let (lhs, rhs) = Self::coerce_bitwise_operands(lhs, rhs, is_signed);
                    lhs.bvor(rhs)
                } else if is_bool {
                    lhs.or(rhs)
                } else if lhs.sort().is_int() && rhs.sort().is_int() {
                    // Part of #2875, #3043: Int-lifted locals — BV bitwise at MIR-derived width.
                    // Part of #3055: use unsigned bv2int for unsigned types.
                    let lhs_bv = lhs.int2bv(int_bv_width);
                    let rhs_bv = rhs.int2bv(int_bv_width);
                    bv_to_int(lhs_bv.bvor(rhs_bv))
                } else {
                    return None;
                }
            }
            BinOp::BitXor => {
                if is_bv {
                    let (lhs, rhs) = Self::coerce_bitwise_operands(lhs, rhs, is_signed);
                    lhs.bvxor(rhs)
                } else if is_bool {
                    // XOR on booleans: (!lhs && rhs) || (lhs && !rhs) == not(eq)
                    lhs.eq(rhs).not()
                } else if lhs.sort().is_int() && rhs.sort().is_int() {
                    // Part of #2875, #3043: Int-lifted locals — BV bitwise at MIR-derived width.
                    // Part of #3055: use unsigned bv2int for unsigned types.
                    let lhs_bv = lhs.int2bv(int_bv_width);
                    let rhs_bv = rhs.int2bv(int_bv_width);
                    bv_to_int(lhs_bv.bvxor(rhs_bv))
                } else {
                    return None;
                }
            }
            BinOp::Shl | BinOp::ShlUnchecked => {
                if is_bv {
                    // MIR shift operations can have different-width operands (e.g., u64 << u32).
                    // SMT-LIB requires same-width operands, so coerce shift amount to value width.
                    let target_width = lhs.sort().bitvec_width()?;
                    let rhs = Self::coerce_shift_amount(rhs, target_width);
                    lhs.bvshl(rhs)
                } else if lhs.sort().is_int() {
                    // Part of #2875, #3043: Int-lifted locals — shift at MIR-derived width.
                    // Part of #3055: use unsigned bv2int for unsigned types.
                    let lhs_bv = lhs.int2bv(int_bv_width);
                    let rhs_bv = if rhs.sort().is_int() { rhs.int2bv(int_bv_width) } else { rhs };
                    let target_width = lhs_bv.sort().bitvec_width()?;
                    let rhs_bv = Self::coerce_shift_amount(rhs_bv, target_width);
                    bv_to_int(lhs_bv.bvshl(rhs_bv))
                } else {
                    return None;
                }
            }
            BinOp::Shr | BinOp::ShrUnchecked => {
                if is_bv {
                    // Coerce shift amount to value width (same as Shl).
                    let target_width = lhs.sort().bitvec_width()?;
                    let rhs = Self::coerce_shift_amount(rhs, target_width);
                    // Arithmetic shift for signed, logical shift for unsigned
                    if is_signed { lhs.bvashr(rhs) } else { lhs.bvlshr(rhs) }
                } else if lhs.sort().is_int() {
                    // Part of #2875, #3043: Int-lifted locals — shift at MIR-derived width.
                    // Part of #3055: use unsigned bv2int for unsigned types.
                    let lhs_bv = lhs.int2bv(int_bv_width);
                    let rhs_bv = if rhs.sort().is_int() { rhs.int2bv(int_bv_width) } else { rhs };
                    let target_width = lhs_bv.sort().bitvec_width()?;
                    let rhs_bv = Self::coerce_shift_amount(rhs_bv, target_width);
                    if is_signed {
                        lhs_bv.bvashr(rhs_bv).bv2int_signed()
                    } else {
                        bv_to_int(lhs_bv.bvlshr(rhs_bv))
                    }
                } else {
                    return None;
                }
            }
            // Comparison ops
            // Handle Int/Real sort mismatches by converting Int to Real (Part of #911)
            // Part of #2244: Also handle Bool↔BV and BV width mismatches that arise
            // from flattened locals where discriminant (Bool) is compared against a
            // bitvector field or operands have different BV widths.
            BinOp::Eq => {
                let (lhs, rhs) = coerce_int_real(lhs, rhs);
                let (lhs, rhs) = Self::coerce_eq_operands(lhs, rhs, is_signed);
                if let Some(result) = try_fieldless_constructor_comparison(&lhs, &rhs, true) {
                    return Some(result);
                }
                if *lhs.sort() != *rhs.sort() {
                    return None;
                }
                // Part of #3875: Full SMT array equality (∀i. select(a,i)==select(b,i))
                // is unsound for finite arrays with symbolic bases — it requires
                // uninitialized indices beyond N to match. Return None so the caller
                // falls back to sound over-approximation.
                if lhs.sort().is_array() {
                    return None;
                }
                option_like_datatype_eq(&lhs, &rhs, true).unwrap_or_else(|| lhs.eq(rhs))
            }
            BinOp::Ne => {
                let (lhs, rhs) = coerce_int_real(lhs, rhs);
                let (lhs, rhs) = Self::coerce_eq_operands(lhs, rhs, is_signed);
                if let Some(result) = try_fieldless_constructor_comparison(&lhs, &rhs, false) {
                    return Some(result);
                }
                if *lhs.sort() != *rhs.sort() {
                    return None;
                }
                // Part of #3875: Same array equality issue as BinOp::Eq — see above.
                if lhs.sort().is_array() {
                    return None;
                }
                option_like_datatype_eq(&lhs, &rhs, false).unwrap_or_else(|| lhs.eq(rhs).not())
            }
            BinOp::Lt => {
                if is_bv {
                    if is_signed { lhs.bvslt(rhs) } else { lhs.bvult(rhs) }
                } else {
                    let (lhs, rhs) = coerce_int_real(lhs, rhs);
                    if lhs.sort().is_real() {
                        lhs.real_lt(rhs)
                    } else if lhs.sort().is_int() {
                        lhs.int_lt(rhs)
                    } else {
                        return None;
                    }
                }
            }
            BinOp::Le => {
                if is_bv {
                    if is_signed { lhs.bvsle(rhs) } else { lhs.bvule(rhs) }
                } else {
                    let (lhs, rhs) = coerce_int_real(lhs, rhs);
                    if lhs.sort().is_real() {
                        lhs.real_le(rhs)
                    } else if lhs.sort().is_int() {
                        lhs.int_le(rhs)
                    } else {
                        return None;
                    }
                }
            }
            BinOp::Gt => {
                if is_bv {
                    if is_signed { lhs.bvsgt(rhs) } else { lhs.bvugt(rhs) }
                } else {
                    let (lhs, rhs) = coerce_int_real(lhs, rhs);
                    if lhs.sort().is_real() {
                        lhs.real_gt(rhs)
                    } else if lhs.sort().is_int() {
                        lhs.int_gt(rhs)
                    } else {
                        return None;
                    }
                }
            }
            BinOp::Ge => {
                if is_bv {
                    if is_signed { lhs.bvsge(rhs) } else { lhs.bvuge(rhs) }
                } else {
                    let (lhs, rhs) = coerce_int_real(lhs, rhs);
                    if lhs.sort().is_real() {
                        lhs.real_ge(rhs)
                    } else if lhs.sort().is_int() {
                        lhs.int_ge(rhs)
                    } else {
                        return None;
                    }
                }
            }
            // Fix #1898, #1905, #1229: Three-way comparison returning Ordering
            // Returns 32-bit result to match sort_inference.rs normalization.
            // Ordering is repr(i8): Less=-1, Equal=0, Greater=1.
            // In 32-bit bitvec: Less=0xFFFFFFFF (-1 in two's complement), Equal=0, Greater=1.
            // Must match SwitchInt case masking: MIR stores Less as u128::MAX, masked to
            // 0xFFFFFFFF in BV32 by codegen_rules_helpers.rs / terminator.rs.
            // Fix #4213: was 0xFF (255) which never matched SwitchInt's 0xFFFFFFFF.
            BinOp::Cmp => {
                if is_bv {
                    // Bitvector comparison - use signed or unsigned based on type
                    let lt = if is_signed {
                        lhs.clone().bvslt(rhs.clone())
                    } else {
                        lhs.clone().bvult(rhs.clone())
                    };
                    let eq = lhs.eq(rhs);
                    Expr::ite(
                        lt,
                        Expr::bitvec_const(0xFFFF_FFFFu128, 32), // Less = -1 in BV32
                        Expr::ite(eq, Expr::bitvec_const(0u128, 32), Expr::bitvec_const(1u128, 32)),
                    )
                } else {
                    // Int/Real comparison
                    let (lhs, rhs) = coerce_int_real(lhs, rhs);
                    if lhs.sort().is_int() {
                        let lt = lhs.clone().int_lt(rhs.clone());
                        let eq = lhs.eq(rhs);
                        Expr::ite(
                            lt,
                            Expr::bitvec_const(0xFFFF_FFFFu128, 32), // Less = -1 in BV32
                            Expr::ite(
                                eq,
                                Expr::bitvec_const(0u128, 32),
                                Expr::bitvec_const(1u128, 32),
                            ),
                        )
                    } else {
                        return None; // Real comparison not supported for Cmp
                    }
                }
            }
            // Unsupported ops
            BinOp::Offset => return None,
        })
    }
}

#[derive(Clone)]
enum OptionLikeView {
    None,
    Some(Expr),
    Symbolic { is_some: Expr, payload: Expr },
}

fn option_like_datatype_eq(lhs: &Expr, rhs: &Expr, is_eq: bool) -> Option<Expr> {
    if lhs.sort() != rhs.sort() || !is_option_like_sort(lhs.sort()) {
        return None;
    }
    let lhs = option_like_view(lhs)?;
    let rhs = option_like_view(rhs)?;
    let eq = option_like_view_eq(lhs, rhs);
    Some(if is_eq { eq } else { eq.not() })
}

fn is_option_like_sort(sort: &Sort) -> bool {
    let Some(dt) = sort.datatype_sort() else {
        return false;
    };
    if dt.constructors.len() != 2 {
        return false;
    }
    let mut arities = dt.constructors.iter().map(|ctor| ctor.fields.len()).collect::<Vec<_>>();
    arities.sort_unstable();
    arities == [0, 1]
}

fn option_like_view(expr: &Expr) -> Option<OptionLikeView> {
    match expr.value() {
        ExprValue::DatatypeConstructor { args, .. } if args.is_empty() => {
            Some(OptionLikeView::None)
        }
        ExprValue::DatatypeConstructor { args, .. } if args.len() == 1 => {
            Some(OptionLikeView::Some(args[0].clone()))
        }
        ExprValue::Ite { cond, then_expr, else_expr } => {
            let then_view = option_like_view(then_expr)?;
            let else_view = option_like_view(else_expr)?;
            match (then_view, else_view) {
                (OptionLikeView::Some(payload), OptionLikeView::None) => {
                    Some(OptionLikeView::Symbolic { is_some: cond.clone(), payload })
                }
                (OptionLikeView::None, OptionLikeView::Some(payload)) => {
                    Some(OptionLikeView::Symbolic { is_some: cond.clone().not(), payload })
                }
                _ => None,
            }
        }
        _ => None,
    }
}

fn option_like_view_eq(lhs: OptionLikeView, rhs: OptionLikeView) -> Expr {
    match (lhs, rhs) {
        (OptionLikeView::None, OptionLikeView::None) => Expr::bool_const(true),
        (OptionLikeView::Some(lhs), OptionLikeView::Some(rhs)) => lhs.eq(rhs),
        (OptionLikeView::None, OptionLikeView::Some(_))
        | (OptionLikeView::Some(_), OptionLikeView::None) => Expr::bool_const(false),
        (OptionLikeView::Symbolic { is_some, payload }, OptionLikeView::Some(expected))
        | (OptionLikeView::Some(expected), OptionLikeView::Symbolic { is_some, payload }) => {
            is_some.and(payload.eq(expected))
        }
        (OptionLikeView::Symbolic { is_some, .. }, OptionLikeView::None)
        | (OptionLikeView::None, OptionLikeView::Symbolic { is_some, .. }) => is_some.not(),
        (
            OptionLikeView::Symbolic { is_some: lhs_is_some, payload: lhs_payload },
            OptionLikeView::Symbolic { is_some: rhs_is_some, payload: rhs_payload },
        ) => {
            let same_discriminant = lhs_is_some.clone().eq(rhs_is_some.clone());
            let same_payload_when_some =
                lhs_is_some.and(rhs_is_some).implies(lhs_payload.eq(rhs_payload));
            same_discriminant.and(same_payload_when_some)
        }
    }
}
