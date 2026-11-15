// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Numeric float casts for the BMC lane: `IntToFloat`, `FloatToInt` and
//! `FloatToFloat`.
//!
//! Floats are bitvector-sorted in this lane (the IEEE 754 bit pattern), so the
//! generic BV→BV arm of `codegen_cast` sign/zero-extended or truncated those
//! bits. That is `transmute` semantics, not `as` semantics, and it proved false
//! claims: `0x4080_0000u32 as f32 == 4.0`, `3.0f32 as u32 == 0x4040_0000`,
//! `300.0f32 as u8 == 0` (negative pack `int_float_casts.rs`).
//!
//! Every lowering here is pure bitvector and exact, and is the one the CHC lane
//! already uses rather than a reimplementation:
//! - `int as float`: `int_to_float_bv_pure` — round to nearest, ties to even,
//!   ±Inf on overflow. f32/f64 targets only: its exponent field is not
//!   saturated to Inf, which is wrong for f16 (`u32::MAX as f16`), so other
//!   targets fail closed.
//! - `float as int`: `build_float_to_int_saturating_expr` — truncation toward
//!   zero, saturating at the integer bounds, NaN → 0.
//! - `float as float`: `float_to_float_bv_pure` for f32↔f64 (RNE, overflow to
//!   ±Inf, underflow to subnormal/±0). A NaN input yields an unconstrained NaN,
//!   because Rust does not pin the sign or payload of a NaN a cast produces.
//!
//! AY's FP theory is deliberately not used: measured 2026-09-11, the ay CLI
//! answers `unknown` on `fp.to_ubv` and signed `to_fp` terms even with concrete
//! operands.
//!
//! Any other shape fails closed: it is recorded through
//! `unsupported_with_fallback` (which demotes the verdict) and `None` is
//! returned, so it can never fall back to bit reinterpretation.

use ay_bindings::{Expr, Sort};
use rustc_public::mir::Operand;
use rustc_public::ty::{FloatTy, RigidTy, Ty, TyKind};
use tracing::debug;

use super::{CastKind, IntoOption, StatementCodegen};
use crate::codegen_ay::chc::call::codegen_call_cmp_string::float_to_int_saturating::build_float_to_int_saturating_expr;
use crate::codegen_ay::float_arithmetic::{
    float_to_float_bv_pure, float_width_to_eb_sb, int_to_float_bv_pure,
};
use crate::codegen_ay::types::{int_ty_to_bitvec_width, uint_ty_to_bitvec_width};

/// Bit width of a primitive float type.
pub(super) fn float_ty_width(ty: Ty) -> Option<u32> {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Float(FloatTy::F16)) => Some(16),
        TyKind::RigidTy(RigidTy::Float(FloatTy::F32)) => Some(32),
        TyKind::RigidTy(RigidTy::Float(FloatTy::F64)) => Some(64),
        TyKind::RigidTy(RigidTy::Float(FloatTy::F128)) => Some(128),
        _ => None,
    }
}

/// Bit width and signedness of a primitive integer type, read from the MIR type.
pub(super) fn int_ty_width_signedness(ty: Ty) -> Option<(u32, bool)> {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Int(int_ty)) => Some((int_ty_to_bitvec_width(int_ty), true)),
        TyKind::RigidTy(RigidTy::Uint(uint_ty)) => Some((uint_ty_to_bitvec_width(uint_ty), false)),
        _ => None,
    }
}

/// IEEE 754 NaN test on a bitvector-encoded float: exponent all ones,
/// mantissa non-zero.
fn bv_float_is_nan(value: &Expr, width: u32) -> Option<Expr> {
    let (eb, sb) = float_width_to_eb_sb(width)?;
    let mant_bits = sb - 1;
    let exponent = value.clone().extract(width - 2, mant_bits);
    let mantissa = value.clone().extract(mant_bits - 1, 0);
    let exp_all_ones = exponent.eq(Expr::bitvec_const((1u64 << eb) - 1, eb));
    let mant_nonzero = mantissa.eq(Expr::bitvec_const(0u64, mant_bits)).not();
    Some(exp_all_ones.and(mant_nonzero))
}

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Entry point for `IntToFloat` / `FloatToInt` / `FloatToFloat` casts.
    ///
    /// Returns the exact converted value, or records a demoting fallback and
    /// returns `None`. It never delegates to `codegen_cast`, whose BV→BV arm is
    /// bit reinterpretation.
    pub(super) fn codegen_float_numeric_cast(
        &mut self,
        kind: &CastKind,
        operand: &Operand,
        target_ty: Ty,
    ) -> Option<Expr> {
        let src_ty = operand.ty(self.body.locals()).into_option();
        let lowered = match (kind, src_ty) {
            (CastKind::IntToFloat, Some(src_ty)) => {
                self.lower_int_to_float(operand, src_ty, target_ty)
            }
            (CastKind::FloatToInt, Some(src_ty)) => {
                self.lower_float_to_int(operand, src_ty, target_ty)
            }
            (CastKind::FloatToFloat, Some(src_ty)) => {
                self.lower_float_to_float(operand, src_ty, target_ty)
            }
            _ => None,
        };
        if lowered.is_none() {
            debug!(?kind, "numeric float cast has no exact encoding; failing closed");
            self.ctx.unsupported_with_fallback(
                "Cast",
                format!("{kind:?}: {operand:?} as {target_ty:?} (no exact float cast encoding)"),
            );
        }
        lowered
    }

    /// The operand's expression, only when it is a bitvector of exactly `width`
    /// bits — the sort every lowering below is defined on.
    fn float_cast_operand(&mut self, operand: &Operand, width: u32) -> Option<Expr> {
        let expr = self.codegen_operand(operand)?;
        if expr.sort().bitvec_width() != Some(width) {
            return None;
        }
        Some(expr)
    }

    fn lower_int_to_float(&mut self, operand: &Operand, src_ty: Ty, target_ty: Ty) -> Option<Expr> {
        let (src_width, signed) = int_ty_width_signedness(src_ty)?;
        let float_width = float_ty_width(target_ty).filter(|w| matches!(*w, 32 | 64))?;
        let src = self.float_cast_operand(operand, src_width)?;
        int_to_float_bv_pure(src, signed, float_width)
    }

    fn lower_float_to_int(&mut self, operand: &Operand, src_ty: Ty, target_ty: Ty) -> Option<Expr> {
        let float_width = float_ty_width(src_ty)?;
        let (int_width, signed) = int_ty_width_signedness(target_ty)?;
        let src = self.float_cast_operand(operand, float_width)?;
        build_float_to_int_saturating_expr(&src, int_width, signed)
    }

    fn lower_float_to_float(
        &mut self,
        operand: &Operand,
        src_ty: Ty,
        target_ty: Ty,
    ) -> Option<Expr> {
        let src_width = float_ty_width(src_ty)?;
        let target_width = float_ty_width(target_ty)?;
        let src = self.float_cast_operand(operand, src_width)?;
        if src_width == target_width {
            // Same-type `as` is a no-op, NaN payload included.
            return Some(src);
        }
        if !matches!((src_width, target_width), (32, 64) | (64, 32)) {
            return None;
        }
        let converted = float_to_float_bv_pure(src.clone(), src_width, target_width)?;
        let src_is_nan = bv_float_is_nan(&src, src_width)?;
        let name = self.ctx.fresh_name("float_cast_nan");
        let nan = self.ctx.declare_var(&name, Sort::bitvec(target_width));
        let nan_is_nan = bv_float_is_nan(&nan, target_width)?;
        // Unconditional, like the solver-auxiliary definitions in `codegen_cast`:
        // it only says `nan` is some NaN, which is always satisfiable, so it
        // cannot make any path vacuous.
        self.ctx.assert(nan_is_nan);
        Some(Expr::ite(src_is_nan, nan, converted))
    }
}
