// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! No-op intrinsic dispatch: forget, black_box, likely/unlikely, is_val_statically_known.

use ay_bindings::Expr;
use rustc_public::mir::{BasicBlockIdx, Operand, Place};
use tracing::debug;

use crate::codegen_ay::statement::StatementCodegen;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// No-op intrinsics: forget, black_box, likely/unlikely, is_val_statically_known.
    pub(in crate::codegen_ay::statement) fn dispatch_noop(
        &mut self,
        fn_name: &str,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if fn_name.contains("forget") {
            debug!("AY codegen: handling forget (no-op)");
            return target;
        }
        if fn_name.contains("black_box") {
            debug!("AY codegen: handling black_box (identity)");
            return self.codegen_identity_intrinsic(args, destination, target);
        }
        if fn_name.contains("likely") || fn_name.contains("unlikely") {
            debug!("AY codegen: handling likely/unlikely (identity)");
            return self.codegen_identity_intrinsic(args, destination, target);
        }
        if fn_name.contains("is_val_statically_known") {
            debug!("AY codegen: handling is_val_statically_known (return false)");
            // Always return false - symbolic values are not statically known
            self.bind_ssa_result(destination, Expr::bool_const(false));
            return target;
        }
        // Part of #3477: assert_zero_valid / assert_mem_uninitialized_valid /
        // assert_inhabited are compile-time type validity checks. The UB
        // violation (when rustc proves the type is invalid for the requirement)
        // is recorded upstream in `maybe_emit_assert_validity_violation`, where
        // the resolved intrinsic Instance carries the generic type argument.
        // Here we only supply the no-op control flow (the intrinsic returns ()).
        if fn_name.contains("assert_zero_valid")
            || fn_name.contains("assert_mem_uninitialized_valid")
            || fn_name.contains("assert_inhabited")
        {
            debug!("AY codegen: handling assert validity check (no-op)");
            return target;
        }
        None
    }
}
