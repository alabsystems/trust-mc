// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Math intrinsic dispatch: fast-math, f32 math, f64 math.

use rustc_public::mir::{BasicBlockIdx, Operand, Place};
use tracing::debug;

use crate::codegen_ay::statement::StatementCodegen;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Math intrinsics: fast-math, f32 math, f64 math.
    pub(in crate::codegen_ay::statement) fn dispatch_math(
        &mut self,
        fn_name: &str,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
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
