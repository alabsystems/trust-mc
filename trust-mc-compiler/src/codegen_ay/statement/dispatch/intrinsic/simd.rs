// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! SIMD intrinsic dispatch: bitwise, arithmetic, comparison, reduce, shuffle, cast, extract/insert.

use rustc_public::mir::{BasicBlockIdx, Operand, Place};
use tracing::debug;

use super::matches_simd_intrinsic;
use crate::codegen_ay::statement::StatementCodegen;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// SIMD intrinsics: bitwise, arithmetic, comparison, reduce, shuffle, cast, extract/insert.
    pub(in crate::codegen_ay::statement) fn dispatch_simd(
        &mut self,
        fn_name: &str,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        // Quick check: all SIMD intrinsics contain "simd"
        if !fn_name.contains("simd") {
            return None;
        }
        // Bitwise
        if matches_simd_intrinsic(fn_name, "simd_and") {
            debug!("AY codegen: handling simd_and");
            return self.codegen_simd_and(args, destination, target);
        }
        if matches_simd_intrinsic(fn_name, "simd_or") {
            debug!("AY codegen: handling simd_or");
            return self.codegen_simd_or(args, destination, target);
        }
        if matches_simd_intrinsic(fn_name, "simd_xor") {
            debug!("AY codegen: handling simd_xor");
            return self.codegen_simd_xor(args, destination, target);
        }
        if matches_simd_intrinsic(fn_name, "simd_shl") {
            debug!("AY codegen: handling simd_shl");
            return self.codegen_simd_shl(args, destination, target);
        }
        if matches_simd_intrinsic(fn_name, "simd_shr") {
            debug!("AY codegen: handling simd_shr");
            return self.codegen_simd_shr(args, destination, target);
        }
        // Arithmetic (Part of #1478)
        if matches_simd_intrinsic(fn_name, "simd_add") {
            debug!("AY codegen: handling simd_add");
            return self.codegen_simd_add(args, destination, target);
        }
        if matches_simd_intrinsic(fn_name, "simd_sub") {
            debug!("AY codegen: handling simd_sub");
            return self.codegen_simd_sub(args, destination, target);
        }
        if matches_simd_intrinsic(fn_name, "simd_mul") {
            debug!("AY codegen: handling simd_mul");
            return self.codegen_simd_mul(args, destination, target);
        }
        if matches_simd_intrinsic(fn_name, "simd_div") {
            debug!("AY codegen: handling simd_div");
            return self.codegen_simd_div(args, destination, target);
        }
        if matches_simd_intrinsic(fn_name, "simd_rem") {
            debug!("AY codegen: handling simd_rem");
            return self.codegen_simd_rem(args, destination, target);
        }
        // Comparison (Part of #1478)
        if matches_simd_intrinsic(fn_name, "simd_eq") {
            debug!("AY codegen: handling simd_eq");
            return self.codegen_simd_eq(args, destination, target);
        }
        if matches_simd_intrinsic(fn_name, "simd_ne") {
            debug!("AY codegen: handling simd_ne");
            return self.codegen_simd_ne(args, destination, target);
        }
        if matches_simd_intrinsic(fn_name, "simd_lt") {
            debug!("AY codegen: handling simd_lt");
            return self.codegen_simd_lt(args, destination, target);
        }
        if matches_simd_intrinsic(fn_name, "simd_le") {
            debug!("AY codegen: handling simd_le");
            return self.codegen_simd_le(args, destination, target);
        }
        if matches_simd_intrinsic(fn_name, "simd_gt") {
            debug!("AY codegen: handling simd_gt");
            return self.codegen_simd_gt(args, destination, target);
        }
        if matches_simd_intrinsic(fn_name, "simd_ge") {
            debug!("AY codegen: handling simd_ge");
            return self.codegen_simd_ge(args, destination, target);
        }
        // Reduce operations (Part of #1478)
        // Note: simd_reduce_* uses contains() since reduce names are unambiguous
        if fn_name.contains("simd_reduce_add") {
            debug!("AY codegen: handling simd_reduce_add");
            return self.codegen_simd_reduce_add(args, destination, target);
        }
        if fn_name.contains("simd_reduce_mul") {
            debug!("AY codegen: handling simd_reduce_mul");
            return self.codegen_simd_reduce_mul(args, destination, target);
        }
        if fn_name.contains("simd_reduce_and") {
            debug!("AY codegen: handling simd_reduce_and");
            return self.codegen_simd_reduce_and(args, destination, target);
        }
        if fn_name.contains("simd_reduce_or") {
            debug!("AY codegen: handling simd_reduce_or");
            return self.codegen_simd_reduce_or(args, destination, target);
        }
        if fn_name.contains("simd_reduce_xor") {
            debug!("AY codegen: handling simd_reduce_xor");
            return self.codegen_simd_reduce_xor(args, destination, target);
        }
        if fn_name.contains("simd_reduce_min") {
            debug!("AY codegen: handling simd_reduce_min");
            return self.codegen_simd_reduce_min(args, destination, target);
        }
        if fn_name.contains("simd_reduce_max") {
            debug!("AY codegen: handling simd_reduce_max");
            return self.codegen_simd_reduce_max(args, destination, target);
        }
        if fn_name.contains("simd_reduce_all") {
            debug!("AY codegen: handling simd_reduce_all");
            return self.codegen_simd_reduce_all(args, destination, target);
        }
        if fn_name.contains("simd_reduce_any") {
            debug!("AY codegen: handling simd_reduce_any");
            return self.codegen_simd_reduce_any(args, destination, target);
        }
        // Shuffle (Part of #1478)
        if fn_name.contains("simd_shuffle") {
            debug!("AY codegen: handling simd_shuffle");
            return self.codegen_simd_shuffle(args, destination, target);
        }
        // Cast (Part of #1478)
        if matches_simd_intrinsic(fn_name, "simd_cast") {
            debug!("AY codegen: handling simd_cast");
            return self.codegen_simd_cast(args, destination, target);
        }
        // Extract/insert (Part of #1501)
        if matches_simd_intrinsic(fn_name, "simd_extract") {
            debug!("AY codegen: handling simd_extract");
            return self.codegen_simd_extract(args, destination, target);
        }
        if matches_simd_intrinsic(fn_name, "simd_insert") {
            debug!("AY codegen: handling simd_insert");
            return self.codegen_simd_insert(args, destination, target);
        }
        // Negation
        if matches_simd_intrinsic(fn_name, "simd_neg") {
            debug!("AY codegen: handling simd_neg");
            return self.codegen_simd_neg(args, destination, target);
        }
        // Select (element-wise mask select)
        if matches_simd_intrinsic(fn_name, "simd_select") {
            debug!("AY codegen: handling simd_select");
            return self.codegen_simd_select(args, destination, target);
        }
        None
    }
}
