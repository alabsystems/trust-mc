// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Float-to-int range checking codegen for Kani verification.
//!
//! Handles `kani::float::float_to_int_in_range::<Float, Int>(value) -> bool`.
//! Part of #3840: concrete fast path for constant float operands.
//! Split from kani.rs per 500-line file limit.

use ay_bindings::Expr;
use rustc_public::mir::{Operand, Place};
use rustc_public::ty::{GenericArgKind, GenericArgs, RigidTy, TyKind};
use tracing::debug;

use super::StatementCodegen;
use super::cast_float::{float_ty_width, int_ty_width_signedness};
use crate::codegen_ay::float_range_check::{eval_float_in_int_range, float_to_int_in_range_expr};
use crate::codegen_ay::types::{bool_sort, int_ty_to_bitvec_width, uint_ty_to_bitvec_width};

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Try to evaluate `float_to_int_in_range::<Float, Int>(value)` at codegen time.
    ///
    /// Part of #3840: Concrete fast path for constant float operands.
    /// Returns `Some(bool)` when the operand is a concrete float literal and the
    /// target integer width is exactly representable by the source float format
    /// (f32 <= 24 bits, f64 <= 53 bits). Returns `None` otherwise.
    fn try_eval_float_to_int_in_range_const(
        &mut self,
        float_ty: rustc_public::ty::Ty,
        int_ty: rustc_public::ty::Ty,
        operand: &Operand,
    ) -> Option<bool> {
        // Extract the concrete float value based on source type.
        let (value_f64, mantissa_bits): (f64, u32) = match float_ty.kind() {
            TyKind::RigidTy(RigidTy::Float(rustc_public::ty::FloatTy::F32)) => {
                let bits = self.try_extract_f32_const(operand)?;
                (f32::from_bits(bits) as f64, 24)
            }
            TyKind::RigidTy(RigidTy::Float(rustc_public::ty::FloatTy::F64)) => {
                let bits = self.try_extract_f64_const(operand)?;
                (f64::from_bits(bits), 53)
            }
            _ => return None,
        };

        // Determine target integer width and signedness.
        let (width, signed) = match int_ty.kind() {
            TyKind::RigidTy(RigidTy::Int(it)) => (int_ty_to_bitvec_width(it), true),
            TyKind::RigidTy(RigidTy::Uint(ut)) => (uint_ty_to_bitvec_width(ut), false),
            _ => return None,
        };

        eval_float_in_int_range(value_f64, mantissa_bits, width, signed)
    }

    /// Codegen kani::float::float_to_int_in_range<Float, Int>(value) -> bool
    ///
    /// Part of #1369: Converted from hook to intrinsic.
    /// Part of #3840: Concrete fast path for constant float operands.
    /// Returns true if the float value after truncation fits within the target
    /// integer type's range [Int::MIN, Int::MAX].
    pub(super) fn codegen_float_to_int_in_range(
        &mut self,
        fn_args: &GenericArgs,
        args: &[Operand],
        destination: &Place,
    ) {
        let base_name = self.ssa_base_name(destination);
        let _ssa_name = self.ssa_name_from_base(&base_name, true);

        // Extract Float and Int types from generic args
        let (float_ty, int_ty) =
            if let (Some(GenericArgKind::Type(float_ty)), Some(GenericArgKind::Type(int_ty))) =
                (fn_args.0.first(), fn_args.0.get(1))
            {
                (*float_ty, *int_ty)
            } else {
                debug!("codegen_float_to_int_in_range: couldn't extract generic types");
                let name = self.ctx.fresh_name("ay_float_in_range");
                let expr = self.ctx.declare_var(&name, bool_sort());
                self.ctx.bmc_sound_havoc("float_to_int_in_range_no_generics");
                self.ctx.record_unreplayable_playback_value(
                    expr.clone(),
                    self.current_path_condition.clone(),
                );
                // A free boolean explores both answers, so a proof over it holds;
                // a counterexample may read the wrong answer and must not be
                // certified Genuine.
                self.ctx.bmc_sound_havoc("float_to_int_in_range_fresh_bool");
                self.env_update(base_name, expr);
                return;
            };

        // Part of #3840: Try concrete evaluation first.
        if let Some(operand) = args.first() {
            if let Some(result) =
                self.try_eval_float_to_int_in_range_const(float_ty, int_ty, operand)
            {
                debug!(
                    "codegen_float_to_int_in_range: {:?} -> {:?}, concrete result = {}",
                    float_ty, int_ty, result
                );
                self.env_update(base_name, Expr::bool_const(result));
                return;
            }
        }

        // Non-literal operand: encode the predicate exactly. Before this, any
        // operand that was not a MIR literal (`let f: f32 = 5.6; ...(f)`) got a
        // free boolean, which failed true claims about the intrinsic.
        if let Some(operand) = args.first()
            && let Some(float_width) = float_ty_width(float_ty)
            && let Some((int_width, int_signed)) = int_ty_width_signedness(int_ty)
            && let Some(value) = self.codegen_operand(operand)
            && value.sort().bitvec_width() == Some(float_width)
            && let Some(result) = float_to_int_in_range_expr(&value, int_width, int_signed)
        {
            debug!(
                "codegen_float_to_int_in_range: {:?} -> {:?}, exact bitvector predicate",
                float_ty, int_ty
            );
            self.env_update(base_name, result);
            return;
        }

        // Fallback when the operand does not codegen to a float bitvector:
        // fresh symbolic boolean. That over-approximation keeps a proof valid
        // but can manufacture a counterexample, so it taints the certificate
        // (SAT only; an UNSAT result stays a clean proof).
        let name = self.ctx.fresh_name("ay_float_in_range");
        let result = self.ctx.declare_var(&name, bool_sort());
        self.ctx.bmc_sound_havoc("float_to_int_in_range");
        self.ctx.record_unreplayable_playback_value(
            result.clone(),
            self.current_path_condition.clone(),
        );
        self.ctx.bmc_sound_havoc("float_to_int_in_range_fresh_bool");

        debug!(
            "codegen_float_to_int_in_range: {:?} -> {:?}, symbolic bool fallback",
            float_ty, int_ty
        );

        self.env_update(base_name, result);
    }
}
