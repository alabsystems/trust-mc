// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Integer `pow`/`wrapping_pow` BMC encoding handler (Part of #3294).
//!
//! Mirrors the CHC handler at `chc/call/codegen_call_cmp_string/pow.rs`.
//! Integer pow/wrapping_pow use exponentiation-by-squaring loops in MIR
//! that are not inlined by the BMC statement path, falling through to the
//! unsupported-construct fallback. This module intercepts pow calls and
//! provides direct encoding:
//! - Both constants → evaluate `base.wrapping_pow(exp)` at codegen time
//! - Constant base 2 → `bvshl(1, exp)` (power of two = left shift)
//! - Otherwise → sound over-approximation (symbolic result)

use ay_bindings::Expr;
use rustc_public::mir::{BasicBlockIdx, Operand, Place};
use rustc_public::ty::{ConstantKind, RigidTy, TyConstKind, TyKind};
use tracing::debug;

use crate::codegen_ay::statement::StatementCodegen;
use crate::codegen_ay::types::{SignExtension, coerce_bitvec_width_safe, ty_to_bv_width};

use super::super::IntoOption;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Try to intercept integer `pow`/`wrapping_pow` calls before they fall
    /// through to the unsupported-construct fallback.
    ///
    /// Returns `Some(target_bb)` if the call was handled, `None` otherwise.
    pub(in crate::codegen_ay::statement) fn try_codegen_pow_call(
        &mut self,
        func: &Operand,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        let callee_path = self.resolve_callee_path(func)?;
        if !is_pow_method(&callee_path) || args.len() < 2 {
            return None;
        }

        // Determine the result bitvec width from the base type.
        let base_ty = args[0].ty(self.body.locals()).into_option()?;
        let result_width = ty_to_bv_width(base_ty).unwrap_or(0);
        if result_width == 0 {
            debug!("pow: cannot determine result width for {:?}", base_ty.kind());
            self.codegen_symbolic_result(destination);
            return target;
        }

        // Extract constant values from MIR operands.
        let base_const = try_extract_const_u128(&args[0]);
        let exp_const = try_extract_const_u128(&args[1]);

        // Case 1: Both base and exponent are constants — evaluate at codegen time.
        if let (Some(base), Some(exp)) = (base_const, exp_const) {
            if let Ok(exp_u32) = u32::try_from(exp) {
                let result_val = base.wrapping_pow(exp_u32);
                let result_expr = Expr::bitvec_const(result_val as i128, result_width);
                self.assign_value_to_place(destination, result_expr);
                debug!(
                    base,
                    exp,
                    result = result_val,
                    width = result_width,
                    "pow: constant-folded (BMC)"
                );
                return target;
            }
        }

        // Case 2: Base is constant 2 — emit bvshl(1, exp).
        // 2^n == 1 << n for bitvector arithmetic.
        if base_const == Some(2) {
            if let Some(exp_expr) = self.codegen_operand(&args[1]) {
                let one = Expr::bitvec_const(1, result_width);
                let exp_coerced =
                    coerce_bitvec_width_safe(exp_expr, result_width, SignExtension::ZeroExtend);
                let result_expr = one.bvshl(exp_coerced);
                self.assign_value_to_place(destination, result_expr);
                debug!("pow: base-2 → bvshl(1, exp) (BMC)");
                return target;
            }
        }

        // Fallback: non-constant base or cannot resolve — sound over-approximation.
        debug!("pow: fallback to symbolic (BMC)");
        self.codegen_symbolic_result(destination);
        target
    }
}

/// Check if a callee path string ends with `::pow` or `::wrapping_pow`.
fn is_pow_method(path: &str) -> bool {
    matches!(path.rsplit("::").next(), Some("pow" | "wrapping_pow"))
}

/// Try to extract a constant unsigned integer value from a MIR operand.
///
/// Returns `Some(value)` if the operand is `Operand::Constant` with an integer
/// allocation. Returns `None` for non-constant operands or non-integer types.
fn try_extract_const_u128(operand: &Operand) -> Option<u128> {
    let const_op = match operand {
        Operand::Constant(c) => c,
        Operand::Copy(_) | Operand::Move(_) => return None,
    };
    let mir_const = &const_op.const_;

    let extract_from_alloc =
        |alloc: &rustc_public::ty::Allocation, ty: rustc_public::ty::Ty| -> Option<u128> {
            match ty.kind() {
                TyKind::RigidTy(RigidTy::Uint(_)) => alloc.read_uint().ok(),
                TyKind::RigidTy(RigidTy::Int(_)) => {
                    let v = alloc.read_int().ok()?;
                    u128::try_from(v).ok()
                }
                _ => None,
            }
        };

    let ty = mir_const.ty();
    match mir_const.kind() {
        ConstantKind::Allocated(alloc) => extract_from_alloc(alloc, ty),
        ConstantKind::Ty(ty_const) => match ty_const.kind() {
            TyConstKind::Value(value_ty, alloc) => extract_from_alloc(alloc, *value_ty),
            _ => None,
        },
        _ => None,
    }
}
