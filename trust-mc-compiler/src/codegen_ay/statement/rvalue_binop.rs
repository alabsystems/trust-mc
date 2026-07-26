// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//! Binary and unary operation codegen for AY.
//!
//! Extracted from rvalue.rs — Part of #2152.
//!
//! Contains:
//! - `codegen_binop_typed`: Binary operation translation with signedness
//! - `coerce_to_int_pair`: Int/BitVec coercion for BigInt operations
//! - `codegen_unop`: Unary operation translation
//! - `build_discriminant_ite_chain`: Discriminant extraction from datatypes

use ay_bindings::{Expr, ExprValue, Sort};
use rustc_public::mir::{BinOp, UnOp};
use tracing::{debug, warn};

use super::StatementCodegen;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Coerce operands to Int sort for mixed Int/BitVec operations.
    ///
    /// When BigInt types interact with bitvector types, both operands must be
    /// promoted to Int sort for SMT-LIB compatibility. Already-Int operands
    /// are passed through; BitVec operands are converted via `bv2int()` (unsigned)
    /// or `bv2int_signed()` (signed two's complement) based on `is_signed`.
    ///
    /// Part of #2757: Use signed interpretation for signed integer operands.
    pub(super) fn coerce_to_int_pair(lhs: Expr, rhs: Expr, is_signed: bool) -> (Expr, Expr) {
        let lhs_int = if lhs.sort().is_int() {
            lhs
        } else if is_signed {
            lhs.bv2int_signed()
        } else {
            lhs.bv2int()
        };
        let rhs_int = if rhs.sort().is_int() {
            rhs
        } else if is_signed {
            rhs.bv2int_signed()
        } else {
            rhs.bv2int()
        };
        (lhs_int, rhs_int)
    }

    /// Translate a MIR binary operation into a AY expression with type-directed signedness.
    ///
    /// For operations that differ between signed/unsigned (Div, Rem, Shr, comparisons),
    /// uses `is_signed` to select the correct SMT operation.
    /// REQUIRES: `lhs`/`rhs` sorts are compatible for the selected operation.
    ///
    /// Float callers intercept before reaching this helper (Part of #3693):
    /// `rvalue.rs` routes float BinOp through AY FP theory (bv_to_fp → fp.add/sub/mul/div → fp_to_ieee_bv).
    /// ENSURES: result sort matches the operation (Bool for comparisons, BitVec otherwise).
    #[must_use]
    pub(super) fn codegen_binop_typed(
        &self,
        op: BinOp,
        lhs: Expr,
        rhs: Expr,
        is_signed: Option<bool>,
    ) -> Expr {
        let signed = is_signed.unwrap_or_else(|| {
            crate::codegen_ay::shared::signedness_fallback_for_binop(op, "codegen_binop_typed")
        });

        match op {
            BinOp::Add | BinOp::AddUnchecked => {
                // #1582: Coerce operands to matching widths for closure captured variables
                let (lhs, rhs) = Self::coerce_to_match_widths_typed(lhs, rhs, signed);
                lhs.bvadd(rhs)
            }
            BinOp::Sub | BinOp::SubUnchecked => {
                // #1582: Coerce operands to matching widths for closure captured variables
                let (lhs, rhs) = Self::coerce_to_match_widths_typed(lhs, rhs, signed);
                lhs.bvsub(rhs)
            }
            BinOp::Mul | BinOp::MulUnchecked => {
                // #1582: Coerce operands to matching widths for closure captured variables
                let (lhs, rhs) = Self::coerce_to_match_widths_typed(lhs, rhs, signed);
                lhs.bvmul(rhs)
            }
            BinOp::Div => {
                // #1582: Coerce operands to matching widths for closure captured variables
                let (lhs, rhs) = Self::coerce_to_match_widths_typed(lhs, rhs, signed);
                if signed { lhs.bvsdiv(rhs) } else { lhs.bvudiv(rhs) }
            }
            BinOp::Rem => {
                // #1582: Coerce operands to matching widths for closure captured variables
                let (lhs, rhs) = Self::coerce_to_match_widths_typed(lhs, rhs, signed);
                if signed { lhs.bvsrem(rhs) } else { lhs.bvurem(rhs) }
            }
            BinOp::BitXor => {
                if lhs.sort().is_bool() {
                    lhs.xor(rhs)
                } else {
                    let (lhs, rhs) = Self::coerce_to_match_widths_typed(lhs, rhs, signed);
                    lhs.bvxor(rhs)
                }
            }
            BinOp::BitAnd => {
                if lhs.sort().is_bool() {
                    lhs.and(rhs)
                } else {
                    let (lhs, rhs) = Self::coerce_to_match_widths_typed(lhs, rhs, signed);
                    lhs.bvand(rhs)
                }
            }
            BinOp::BitOr => {
                if lhs.sort().is_bool() {
                    lhs.or(rhs)
                } else {
                    let (lhs, rhs) = Self::coerce_to_match_widths_typed(lhs, rhs, signed);
                    lhs.bvor(rhs)
                }
            }
            BinOp::Shl | BinOp::ShlUnchecked => {
                // MIR shift operations can have different-width operands (e.g., u32 << u8).
                // SMT-LIB requires same-width operands, so coerce shift amount to value width.
                let Some(target_width) = lhs.sort().bitvec_width() else {
                    warn!(?op, lhs_sort = ?lhs.sort(), "shift: lhs not bitvec");
                    return lhs;
                };
                let rhs = Self::coerce_to_width(rhs, target_width);
                lhs.bvshl(rhs)
            }
            BinOp::Shr | BinOp::ShrUnchecked => {
                // Coerce shift amount to value width (same as Shl).
                let Some(target_width) = lhs.sort().bitvec_width() else {
                    warn!(?op, lhs_sort = ?lhs.sort(), "shift: lhs not bitvec");
                    return lhs;
                };
                let rhs = Self::coerce_to_width(rhs, target_width);
                if signed {
                    lhs.bvashr(rhs) // Arithmetic shift (preserves sign)
                } else {
                    lhs.bvlshr(rhs) // Logical shift (fills with zeros)
                }
            }
            BinOp::Eq => {
                // #1043: Handle Int/BitVec mixed comparisons (BigInt types)
                if lhs.sort().is_int() || rhs.sort().is_int() {
                    let (l, r) = Self::coerce_to_int_pair(lhs, rhs, signed);
                    l.eq(r)
                } else {
                    let (lhs, rhs) = Self::coerce_to_match_widths_typed(lhs, rhs, signed);
                    option_like_datatype_eq(&lhs, &rhs, true).unwrap_or_else(|| lhs.eq(rhs))
                }
            }
            BinOp::Ne => {
                // #1043: Handle Int/BitVec mixed comparisons (BigInt types)
                if lhs.sort().is_int() || rhs.sort().is_int() {
                    let (l, r) = Self::coerce_to_int_pair(lhs, rhs, signed);
                    l.ne(r)
                } else {
                    let (lhs, rhs) = Self::coerce_to_match_widths_typed(lhs, rhs, signed);
                    option_like_datatype_eq(&lhs, &rhs, false).unwrap_or_else(|| lhs.ne(rhs))
                }
            }
            BinOp::Lt => {
                // #756: Handle Int/BitVec mixed comparisons (BigInt types)
                if lhs.sort().is_int() || rhs.sort().is_int() {
                    let (l, r) = Self::coerce_to_int_pair(lhs, rhs, signed);
                    l.int_lt(r)
                } else {
                    let (lhs, rhs) = Self::coerce_to_match_widths_typed(lhs, rhs, signed);
                    if signed { lhs.bvslt(rhs) } else { lhs.bvult(rhs) }
                }
            }
            BinOp::Le => {
                // #756: Handle Int/BitVec mixed comparisons (BigInt types)
                if lhs.sort().is_int() || rhs.sort().is_int() {
                    let (l, r) = Self::coerce_to_int_pair(lhs, rhs, signed);
                    l.int_le(r)
                } else {
                    let (lhs, rhs) = Self::coerce_to_match_widths_typed(lhs, rhs, signed);
                    if signed { lhs.bvsle(rhs) } else { lhs.bvule(rhs) }
                }
            }
            BinOp::Ge => {
                // #756: Handle Int/BitVec mixed comparisons (BigInt types)
                if lhs.sort().is_int() || rhs.sort().is_int() {
                    let (l, r) = Self::coerce_to_int_pair(lhs, rhs, signed);
                    l.int_ge(r)
                } else {
                    let (lhs, rhs) = Self::coerce_to_match_widths_typed(lhs, rhs, signed);
                    if signed { lhs.bvsge(rhs) } else { lhs.bvuge(rhs) }
                }
            }
            BinOp::Gt => {
                // #756: Handle Int/BitVec mixed comparisons (BigInt types)
                if lhs.sort().is_int() || rhs.sort().is_int() {
                    let (l, r) = Self::coerce_to_int_pair(lhs, rhs, signed);
                    l.int_gt(r)
                } else {
                    let (lhs, rhs) = Self::coerce_to_match_widths_typed(lhs, rhs, signed);
                    if signed { lhs.bvsgt(rhs) } else { lhs.bvugt(rhs) }
                }
            }
            BinOp::Cmp => {
                // #756: Handle Int/BitVec mixed comparisons (BigInt types)
                // Fix #2771: Use 32-bit bitvecs to match sort_inference.rs unit enum encoding
                // and codegen_stmt_arithmetic.rs / comparison.rs codegen_ord_cmp.
                // Rust Ordering is repr(i8): Less=-1, Equal=0, Greater=1.
                // In 32-bit BV: Less=0xFFFFFFFF (-1 in two's complement), Equal=0, Greater=1.
                // Fix #4213: was 0xFF (255) which never matched SwitchInt's 0xFFFFFFFF.
                if lhs.sort().is_int() || rhs.sort().is_int() {
                    let (lhs_int, rhs_int) = Self::coerce_to_int_pair(lhs, rhs, signed);
                    // lhs_int used twice: int_lt and eq. Clone for first use.
                    // rhs_int used twice: int_lt and eq. Clone for first use.
                    let lt = lhs_int.clone().int_lt(rhs_int.clone());
                    Expr::ite(
                        lt,
                        Expr::bitvec_const(0xFFFF_FFFFu128, 32),
                        Expr::ite(
                            lhs_int.eq(rhs_int),
                            Expr::bitvec_const(0u128, 32),
                            Expr::bitvec_const(1u128, 32),
                        ),
                    )
                } else {
                    // Three-way comparison: use signed comparisons if signed, unsigned otherwise
                    // SMT-LIB requires same-width operands for comparison
                    let (lhs, rhs) = Self::coerce_to_match_widths_typed(lhs, rhs, signed);
                    // lhs used twice: bvslt/bvult and eq. Clone for first use.
                    // rhs used twice: bvslt/bvult and eq. Clone for first use.
                    let lt = if signed {
                        lhs.clone().bvslt(rhs.clone())
                    } else {
                        lhs.clone().bvult(rhs.clone())
                    };
                    Expr::ite(
                        lt,
                        Expr::bitvec_const(0xFFFF_FFFFu128, 32),
                        Expr::ite(
                            lhs.eq(rhs),
                            Expr::bitvec_const(0u128, 32),
                            Expr::bitvec_const(1u128, 32),
                        ),
                    )
                }
            }
            BinOp::Offset => {
                // NOTE: BinOp::Offset is normally handled specially in codegen_rvalue
                // where we have access to pointee type info for scaling. This fallback
                // should rarely be reached - log a warning for debugging if it is.
                debug!(
                    "BinOp::Offset fallback: no pointee type info, assuming byte-sized (size=1)"
                );
                lhs.bvadd(rhs)
            }
        }
    }

    /// Build an ITE chain for discriminant extraction from a datatype expression.
    ///
    /// For a datatype with N constructors, produces:
    ///   (ite (is-C0 expr) 0 (ite (is-C1 expr) 1 ... (N-1)))
    ///
    /// The last constructor serves as the else case (returns N-1).
    ///
    /// REQUIRES: constructors.len() > 0
    /// ENSURES: result is bitvec(32) with value in [0, N-1]
    ///
    /// Part of #1419: Extracted from duplicated code in codegen_rvalue_discriminant.
    pub(super) fn build_discriminant_ite_chain(
        dt_name: &str,
        constructors: &[ay_bindings::DatatypeConstructor],
        expr: &Expr,
    ) -> Expr {
        assert!(
            !constructors.is_empty(),
            "build_discriminant_ite_chain: constructors must not be empty"
        );
        let num_cons = constructors.len();
        // Start with last variant as default (else case)
        // Use 32 bits to match sort_inference.rs expectation (#1417)
        let mut result = Expr::bitvec_const(num_cons as i128 - 1, 32);
        for (i, cons) in constructors.iter().enumerate().rev() {
            if i == num_cons - 1 {
                continue; // Last variant is the else case
            }
            // expr used in loop — clone each iteration since is_constructor now takes self
            let is_cons = expr.clone().is_constructor(dt_name, &cons.name);
            let idx = Expr::bitvec_const(i as i128, 32);
            result = Expr::ite(is_cons, idx, result);
        }
        result
    }

    /// Translate a MIR unary operation into a AY expression.
    ///
    /// REQUIRES: operand.sort() is Bool (for Not) or BitVec (for Not/Neg)
    /// ENSURES: result.sort() == operand.sort() for Not/Neg
    ///
    /// NOTE: PtrMetadata is handled specially in `codegen_rvalue` before this function
    /// is called, so it's unreachable here.
    #[must_use]
    pub(super) fn codegen_unop(&self, op: UnOp, operand: Expr) -> Expr {
        match op {
            UnOp::Not => {
                // Bitwise not for integers, logical not for booleans
                if operand.sort().is_bool() { operand.not() } else { operand.bvnot() }
            }
            UnOp::Neg => operand.bvneg(),
            // PtrMetadata is handled by codegen_ptr_metadata in codegen_rvalue
            UnOp::PtrMetadata => unreachable!(
                "PtrMetadata should be handled by codegen_rvalue before calling codegen_unop"
            ),
        }
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
