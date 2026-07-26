// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! BigInt arithmetic stub implementations for CHC mode.
//!
//! Converted from include!() to proper module per #2595.
//! Binary operations use table-driven dispatch per #2268.

use super::stubs::StubKind;
use super::stubs_numeric_arg::NumericArgKind;
use super::{ChcCtx, StubTranslateArgs, chc_fresh_name, declare_pending_var, ty_signedness};
use ay_bindings::Expr;
use rustc_public::mir::Operand;
use std::collections::HashSet;
use tracing::{debug, warn};

use crate::codegen_ay::types::int_sort;

/// Binary operation function: `(lhs, rhs) -> result`.
type BinaryIntOp = fn(Expr, Expr) -> Expr;

/// Table mapping StubKind → binary Int operation for CHC BigInt dispatch.
///
/// Covers arithmetic (Add/Sub/Mul/Div/Rem), compound assignment (*Assign),
/// and comparisons (Eq/Lt/Le/Gt/Ge). All share the pattern:
///   resolve 2 args as Int, apply operation.
///
/// Sorted by discriminant for linear scan; table is small (13 entries).
const BIGINT_BINARY_OPS: &[(StubKind, BinaryIntOp)] = &[
    (StubKind::BigIntAdd, Expr::int_add),
    (StubKind::BigIntSub, Expr::int_sub),
    (StubKind::BigIntMul, Expr::int_mul),
    (StubKind::BigIntDiv, Expr::int_div),
    (StubKind::BigIntRem, Expr::int_mod),
    (StubKind::BigIntAddAssign, Expr::int_add),
    (StubKind::BigIntSubAssign, Expr::int_sub),
    (StubKind::BigIntMulAssign, Expr::int_mul),
    (StubKind::BigIntEq, Expr::eq),
    (StubKind::BigIntLt, Expr::int_lt),
    (StubKind::BigIntLe, Expr::int_le),
    (StubKind::BigIntGt, Expr::int_gt),
    (StubKind::BigIntGe, Expr::int_ge),
];

/// Lookup a binary operation for a StubKind.
fn bigint_binary_op(stub: StubKind) -> Option<BinaryIntOp> {
    BIGINT_BINARY_OPS.iter().find(|(s, _)| *s == stub).map(|(_, op)| *op)
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// D3 table-driven dispatch (Part of #2304).
    pub(in crate::codegen_ay::chc) fn translate_bigint_call(
        &mut self,
        stub: StubKind,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        // Binary operations use a fn-pointer table (already table-driven).
        if let Some(op) = bigint_binary_op(stub) {
            if args.len() < 2 {
                return None;
            }
            let lhs = self.get_bigint_arg(&args[0], modified_locals)?;
            let rhs = self.get_bigint_arg(&args[1], modified_locals)?;
            let result = Some(op(lhs, rhs));
            debug!(?stub, args_len = args.len(), result = ?result, "translate_bigint_call");
            return result;
        }

        // Remaining variants dispatched via stub_dispatch! macro.
        let ctx = StubTranslateArgs { args, modified_locals, dest_local: None };
        stub_dispatch!(self, stub, &ctx, "translate_bigint_call",
            StubKind::BigIntFrom       => translate_bigint_from,
            StubKind::BigIntOne        => translate_bigint_one,
            StubKind::BigIntZero       => translate_bigint_zero,
            StubKind::BigIntIsZero     => translate_bigint_is_zero,
            StubKind::BigIntIsNegative => translate_bigint_is_negative,
            StubKind::BigIntNeg        => translate_bigint_neg,
            StubKind::BigIntAbs        => translate_bigint_abs,
            StubKind::BigIntCmp
            | StubKind::BigIntPartialCmp => translate_bigint_cmp,
            StubKind::BigIntClone      => translate_bigint_clone,
            StubKind::BigIntShl
            | StubKind::BigIntShlAssign => translate_bigint_shl,
            StubKind::BigIntShr
            | StubKind::BigIntShrAssign => translate_bigint_shr,
            StubKind::BigIntBitAnd
            | StubKind::BigIntBitOr
            | StubKind::BigIntBitXor   => translate_bigint_bitwise,
        )
    }

    // ===== BigInt handlers (D3 table-driven, Part of #2304) =====

    /// BigInt::from(primitive) — result is Int sort.
    /// Part of #911: uses bv2int instead of unconstrained variable.
    fn translate_bigint_from(&mut self, ctx: &StubTranslateArgs<'_>) -> Option<Expr> {
        if ctx.args.is_empty() {
            return None;
        }
        if let Some(arg_expr) =
            self.translate_operand_with_modified(&ctx.args[0], ctx.modified_locals)
        {
            if arg_expr.sort().is_bitvec() {
                let is_signed = if let Ok(arg_ty) = ctx.args[0].ty(self.body.locals()) {
                    ty_signedness(arg_ty).unwrap_or_else(|| {
                        warn!(arg = ?ctx.args[0], "Cannot determine signedness for BigInt::from, defaulting to signed");
                        true
                    })
                } else {
                    warn!(arg = ?ctx.args[0], "Cannot determine arg type for BigInt::from, defaulting to signed");
                    true
                };
                if is_signed { Some(arg_expr.bv2int_signed()) } else { Some(arg_expr.bv2int()) }
            } else if arg_expr.sort().is_int() {
                Some(arg_expr)
            } else {
                // Part of #3447: Record that BigInt::from arg has unsupported sort.
                self.record_sound_fallback_reason("bigint_from_unsupported_sort");
                Some(declare_pending_var(chc_fresh_name("bigint_from"), int_sort()))
            }
        } else {
            // Part of #3447: Record that BigInt::from arg translation failed.
            self.record_sound_fallback_reason("bigint_from_arg_unresolved");
            Some(declare_pending_var(chc_fresh_name("bigint_from"), int_sort()))
        }
    }

    fn translate_bigint_one(&mut self, _ctx: &StubTranslateArgs<'_>) -> Option<Expr> {
        Some(Expr::int_const(1))
    }

    fn translate_bigint_zero(&mut self, _ctx: &StubTranslateArgs<'_>) -> Option<Expr> {
        Some(Expr::int_const(0))
    }

    fn translate_bigint_is_zero(&mut self, ctx: &StubTranslateArgs<'_>) -> Option<Expr> {
        let arg = self.get_bigint_arg(ctx.args.first()?, ctx.modified_locals)?;
        Some(arg.eq(Expr::int_const(0)))
    }

    fn translate_bigint_is_negative(&mut self, ctx: &StubTranslateArgs<'_>) -> Option<Expr> {
        let arg = self.get_bigint_arg(ctx.args.first()?, ctx.modified_locals)?;
        Some(arg.int_lt(Expr::int_const(0)))
    }

    fn translate_bigint_neg(&mut self, ctx: &StubTranslateArgs<'_>) -> Option<Expr> {
        let arg = self.get_bigint_arg(ctx.args.first()?, ctx.modified_locals)?;
        Some(arg.int_neg())
    }

    fn translate_bigint_abs(&mut self, ctx: &StubTranslateArgs<'_>) -> Option<Expr> {
        let arg = self.get_bigint_arg(ctx.args.first()?, ctx.modified_locals)?;
        let zero = Expr::int_const(0);
        Some(Expr::ite(arg.clone().int_lt(zero), arg.clone().int_neg(), arg))
    }

    /// Cmp/PartialCmp — Int-encoded Ordering (Less=-1, Equal=0, Greater=1).
    fn translate_bigint_cmp(&mut self, ctx: &StubTranslateArgs<'_>) -> Option<Expr> {
        if ctx.args.len() < 2 {
            return None;
        }
        let lhs = self.get_bigint_arg(&ctx.args[0], ctx.modified_locals)?;
        let rhs = self.get_bigint_arg(&ctx.args[1], ctx.modified_locals)?;
        let is_lt = lhs.clone().int_lt(rhs.clone());
        let is_eq = lhs.eq(rhs);
        Some(Expr::ite(
            is_lt,
            Expr::int_const(-1),
            Expr::ite(is_eq, Expr::int_const(0), Expr::int_const(1)),
        ))
    }

    fn translate_bigint_clone(&mut self, ctx: &StubTranslateArgs<'_>) -> Option<Expr> {
        self.get_bigint_arg(ctx.args.first()?, ctx.modified_locals)
    }

    /// Bit shift — LIA cannot express symbolic exponent; return unconstrained (sound).
    fn translate_bigint_shl(&mut self, _ctx: &StubTranslateArgs<'_>) -> Option<Expr> {
        // Part of #3447: LIA cannot express shifts — result is unconstrained.
        self.record_sound_fallback_reason("bigint_shl_lia_unsupported");
        Some(declare_pending_var(chc_fresh_name("bigint_shl"), int_sort()))
    }

    fn translate_bigint_shr(&mut self, _ctx: &StubTranslateArgs<'_>) -> Option<Expr> {
        // Part of #3447: LIA cannot express shifts — result is unconstrained.
        self.record_sound_fallback_reason("bigint_shr_lia_unsupported");
        Some(declare_pending_var(chc_fresh_name("bigint_shr"), int_sort()))
    }

    /// Bitwise ops on unbounded Int cannot be expressed in LIA; return unconstrained (sound).
    fn translate_bigint_bitwise(&mut self, _ctx: &StubTranslateArgs<'_>) -> Option<Expr> {
        // Part of #3447: LIA cannot express bitwise ops — result is unconstrained.
        self.record_sound_fallback_reason("bigint_bitwise_lia_unsupported");
        Some(declare_pending_var(chc_fresh_name("bigint_bitwise"), int_sort()))
    }

    /// Gets a BigInt argument as a AY Int expression.
    ///
    /// Delegates to shared `resolve_numeric_arg` (Part of #2878).
    pub(in crate::codegen_ay::chc) fn get_bigint_arg(
        &mut self,
        operand: &Operand,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        self.resolve_numeric_arg(operand, modified_locals, NumericArgKind::BigInt)
    }
}
