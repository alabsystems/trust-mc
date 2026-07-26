// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! BigRational arithmetic stub implementations for CHC mode.
//!
//! Converted from include!() to proper module per #2595.
//! Binary operations use table-driven dispatch per #2268.

use super::stubs::StubKind;
use super::stubs_numeric_arg::NumericArgKind;
use super::{ChcCtx, StubTranslateArgs};
use ay_bindings::Expr;
use rustc_public::mir::Operand;
use std::collections::HashSet;
use tracing::debug;

/// Binary operation function: `(lhs, rhs) -> result`.
type BinaryRealOp = fn(Expr, Expr) -> Expr;

/// Table mapping StubKind → binary Real operation for CHC BigRational dispatch.
///
/// Covers arithmetic (Add/Sub/Mul/Div), compound assignment (*Assign),
/// and comparisons (Eq/Lt/Le/Gt/Ge). All share the pattern:
///   resolve 2 args as Real, apply operation.
const BIGRATIONAL_BINARY_OPS: &[(StubKind, BinaryRealOp)] = &[
    (StubKind::BigRationalAdd, Expr::real_add),
    (StubKind::BigRationalSub, Expr::real_sub),
    (StubKind::BigRationalMul, Expr::real_mul),
    (StubKind::BigRationalDiv, Expr::real_div),
    (StubKind::BigRationalAddAssign, Expr::real_add),
    (StubKind::BigRationalSubAssign, Expr::real_sub),
    (StubKind::BigRationalMulAssign, Expr::real_mul),
    (StubKind::BigRationalDivAssign, Expr::real_div),
    (StubKind::BigRationalEq, Expr::eq),
    (StubKind::BigRationalLt, Expr::real_lt),
    (StubKind::BigRationalLe, Expr::real_le),
    (StubKind::BigRationalGt, Expr::real_gt),
    (StubKind::BigRationalGe, Expr::real_ge),
];

/// Lookup a binary operation for a StubKind.
fn bigrational_binary_op(stub: StubKind) -> Option<BinaryRealOp> {
    BIGRATIONAL_BINARY_OPS.iter().find(|(s, _)| *s == stub).map(|(_, op)| *op)
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// D3 table-driven dispatch (Part of #2304).
    ///
    /// BigRational is modeled using SMT Real sort (rational fragment).
    /// Part of #911: BigRational interception for CHC codegen.
    pub(in crate::codegen_ay::chc) fn translate_bigrational_call(
        &mut self,
        stub: StubKind,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        // Binary operations use a fn-pointer table (already table-driven).
        if let Some(op) = bigrational_binary_op(stub) {
            if args.len() < 2 {
                return None;
            }
            let lhs = self.get_bigrational_arg(&args[0], modified_locals)?;
            let rhs = self.get_bigrational_arg(&args[1], modified_locals)?;
            let result = Some(op(lhs, rhs));
            debug!(?stub, args_len = args.len(), result = ?result, "translate_bigrational_call");
            return result;
        }

        // Remaining variants dispatched via stub_dispatch! macro.
        let ctx = StubTranslateArgs { args, modified_locals, dest_local: None };
        stub_dispatch!(self, stub, &ctx, "translate_bigrational_call",
            StubKind::BigRationalNew   => translate_bigrational_new,
            StubKind::BigRationalFrom  => translate_bigrational_from,
            StubKind::BigRationalNeg   => translate_bigrational_neg,
            StubKind::BigRationalClone => translate_bigrational_clone,
        )
    }

    // ===== BigRational handlers (D3 table-driven, Part of #2304) =====

    /// BigRational::new(numer, denom) -> numer / denom as Real.
    fn translate_bigrational_new(&mut self, ctx: &StubTranslateArgs<'_>) -> Option<Expr> {
        if ctx.args.len() < 2 {
            return None;
        }
        let numer = self.get_bigint_arg(&ctx.args[0], ctx.modified_locals)?;
        let denom = self.get_bigint_arg(&ctx.args[1], ctx.modified_locals)?;
        let numer_real = numer.int_to_real();
        let denom_real = denom.int_to_real();
        Some(numer_real.real_div(denom_real))
    }

    /// BigRational::from(BigInt) -> BigInt / 1 as Real.
    fn translate_bigrational_from(&mut self, ctx: &StubTranslateArgs<'_>) -> Option<Expr> {
        let arg = self.get_bigint_arg(ctx.args.first()?, ctx.modified_locals)?;
        Some(arg.int_to_real())
    }

    fn translate_bigrational_neg(&mut self, ctx: &StubTranslateArgs<'_>) -> Option<Expr> {
        let arg = self.get_bigrational_arg(ctx.args.first()?, ctx.modified_locals)?;
        Some(arg.real_neg())
    }

    fn translate_bigrational_clone(&mut self, ctx: &StubTranslateArgs<'_>) -> Option<Expr> {
        self.get_bigrational_arg(ctx.args.first()?, ctx.modified_locals)
    }

    /// Gets a BigRational argument as a AY Real expression.
    ///
    /// Delegates to shared `resolve_numeric_arg` (Part of #2878).
    pub(in crate::codegen_ay::chc) fn get_bigrational_arg(
        &mut self,
        operand: &Operand,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        self.resolve_numeric_arg(operand, modified_locals, NumericArgKind::BigRational)
    }
}
