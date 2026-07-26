// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Result method dispatch: is_ok, is_err, unwrap, expect, unwrap_or, unwrap_or_else.

use rustc_public::mir::{BasicBlockIdx, Operand, Place};
use tracing::debug;

use super::extract_method_name;
use crate::codegen_ay::statement::StatementCodegen;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Result predicate methods: is_ok, is_err, unwrap, expect, unwrap_or, unwrap_or_else.
    pub(in crate::codegen_ay::statement) fn dispatch_result(
        &mut self,
        fn_name: &str,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if !fn_name.contains("Result") {
            return None;
        }
        let method = extract_method_name(fn_name)?;

        match method {
            "unwrap_or_else" => {
                debug!("AY codegen: handling Result::unwrap_or_else");
                self.codegen_result_unwrap_or_else(args, destination, target)
            }
            "unwrap_or" => {
                debug!("AY codegen: handling Result::unwrap_or");
                self.codegen_result_unwrap_or(args, destination, target)
            }
            "is_ok" => {
                debug!("AY codegen: handling Result::is_ok");
                self.codegen_result_is_ok(args, destination, target)
            }
            "is_err" => {
                debug!("AY codegen: handling Result::is_err");
                self.codegen_result_is_err(args, destination, target)
            }
            "expect" => {
                debug!("AY codegen: handling Result::expect - delegating to unwrap");
                self.codegen_result_unwrap(args, destination, target)
            }
            "unwrap" => {
                debug!("AY codegen: handling Result::unwrap");
                self.codegen_result_unwrap(args, destination, target)
            }
            _ => None, // non-enum: &str
        }
    }
}
