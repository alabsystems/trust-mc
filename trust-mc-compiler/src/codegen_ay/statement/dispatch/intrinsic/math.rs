// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Math intrinsic dispatch: fast-math, f32 math, f64 math.

use rustc_public::mir::{BasicBlockIdx, Operand, Place};
use rustc_public::ty::{RigidTy, TyKind};
use tracing::debug;

use crate::codegen_ay::chc::call::codegen_call_cmp_string::float_to_int_saturating::{
    build_float_to_int_saturating_expr, build_float_to_int_ub_components,
};
use crate::codegen_ay::statement::StatementCodegen;
use crate::codegen_ay::types::{int_ty_to_bitvec_width, uint_ty_to_bitvec_width};

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// `float_to_int_unchecked::<Float, Int>(value) -> Int`.
    ///
    /// UB unless the source is finite AND its truncation toward zero fits the
    /// target integer. rustc reports those as two DIFFERENT diagnostics, and so
    /// does this: collapsing them would name the wrong cause for a NaN.
    ///
    /// Previously unmodelled in this lane, so every call fell through to the
    /// unsupported-call path. That was fail-closed (the harness demoted) but it
    /// meant the intrinsic's own obligation was never checked — the corpus
    /// tests for it could not do better than INCONCLUSIVE.
    ///
    /// The predicates come from `build_float_to_int_ub_components`, shared with
    /// the CHC lane rather than reimplemented: the bit-level float reasoning is
    /// subtle (the `INT_MIN` boundary especially) and is soundness-relevant in
    /// both lanes, so it must not be allowed to diverge.
    fn codegen_float_to_int_unchecked(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        let value = self.codegen_operand(args.first()?)?;

        // The target integer type is the destination's, and its signedness is
        // read from the MIR type rather than guessed from the width.
        let dest_ty = destination.ty(self.body.locals()).ok()?;
        let (target_width, is_signed) = match dest_ty.kind() {
            TyKind::RigidTy(RigidTy::Int(int_ty)) => (int_ty_to_bitvec_width(int_ty), true),
            TyKind::RigidTy(RigidTy::Uint(uint_ty)) => (uint_ty_to_bitvec_width(uint_ty), false),
            _ => return None,
        };

        let (non_finite, out_of_range) =
            build_float_to_int_ub_components(&value, target_width, is_signed)?;

        self.record_violation_guarded_with_message(
            non_finite,
            "float_to_int_unchecked_non_finite",
            Some("float_to_int_unchecked: attempt to convert a non-finite value to an integer".into()),
        );
        self.record_violation_guarded_with_message(
            out_of_range,
            "float_to_int_unchecked_out_of_range",
            Some(
                "float_to_int_unchecked: attempt to convert a value out of range of the target integer"
                    .into(),
            ),
        );

        // On every non-UB input the saturating conversion agrees with the
        // truncation `float_to_int_unchecked` performs, so it is exact wherever
        // the program is defined — and where it is not, the obligations above
        // have already fired.
        let result = build_float_to_int_saturating_expr(&value, target_width, is_signed)?;
        self.assign_value_to_place(destination, result);
        target
    }

    /// Math intrinsics: fast-math, f32 math, f64 math.
    pub(in crate::codegen_ay::statement) fn dispatch_math(
        &mut self,
        fn_name: &str,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        // `float_to_int_unchecked` must come before the generic f32/f64 math
        // families, whose `contains` patterns would otherwise swallow it.
        if fn_name.contains("float_to_int_unchecked") {
            debug!("AY codegen: handling float_to_int_unchecked");
            return self.codegen_float_to_int_unchecked(args, destination, target);
        }
        // Fast-math intrinsics
        if fn_name.contains("fadd_fast")
            || fn_name.contains("fsub_fast")
            || fn_name.contains("fmul_fast")
            || fn_name.contains("fdiv_fast")
        {
            debug!("AY codegen: handling fast-math intrinsic: {}", fn_name);
            return self.codegen_fast_math_intrinsic(fn_name, args, destination, target);
        }
        // f32 math intrinsics (Part of #1362, #1365)
        if is_f32_math_intrinsic(fn_name) {
            debug!("AY codegen: handling f32 math intrinsic: {}", fn_name);
            return self.codegen_math_intrinsic_f32(fn_name, args, destination, target);
        }
        // f64 math intrinsics
        if is_f64_math_intrinsic(fn_name) {
            debug!("AY codegen: handling f64 math intrinsic: {}", fn_name);
            return self.codegen_math_intrinsic_f64(fn_name, args, destination, target);
        }
        None
    }
}

/// Check if fn_name is an f32 math intrinsic.
pub(super) fn is_f32_math_intrinsic(fn_name: &str) -> bool {
    const F32_SUFFIXES: &[&str] = &[
        "sqrtf32",
        "sinf32",
        "cosf32",
        "expf32",
        "logf32",
        "exp2f32",
        "log2f32",
        "log10f32",
        "powf32",
        "powif32",
        "fabsf32",
        "copysignf32",
        "floorf32",
        "ceilf32",
        "truncf32",
        "roundf32",
        "round_ties_even_f32",
        "fmaf32",
        "minnumf32",
        "maxnumf32",
    ];
    F32_SUFFIXES.iter().any(|suffix| fn_name.ends_with(suffix))
}

/// Check if fn_name is an f64 math intrinsic.
pub(super) fn is_f64_math_intrinsic(fn_name: &str) -> bool {
    const F64_SUFFIXES: &[&str] = &[
        "sqrtf64",
        "sinf64",
        "cosf64",
        "expf64",
        "logf64",
        "exp2f64",
        "log2f64",
        "log10f64",
        "powf64",
        "powif64",
        "fabsf64",
        "copysignf64",
        "floorf64",
        "ceilf64",
        "truncf64",
        "roundf64",
        "round_ties_even_f64",
        "fmaf64",
        "minnumf64",
        "maxnumf64",
    ];
    F64_SUFFIXES.iter().any(|suffix| fn_name.ends_with(suffix))
}
