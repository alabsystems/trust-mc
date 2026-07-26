// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Option method dispatch: is_none, is_some, unwrap, unwrap_or, unwrap_or_else, expect.

use rustc_public::mir::{BasicBlockIdx, Operand, Place};
use tracing::debug;

use super::extract_method_name;
use crate::codegen_ay::statement::StatementCodegen;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Option methods: is_none, is_some, unwrap.
    pub(in crate::codegen_ay::statement) fn dispatch_option(
        &mut self,
        fn_name: &str,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if !fn_name.contains("Option") {
            return None;
        }
        let method = extract_method_name(fn_name)?;

        match method {
            "is_none" => {
                debug!("AY codegen: handling Option::is_none");
                self.codegen_option_is_none(args, destination, target)
            }
            "is_some" => {
                debug!("AY codegen: handling Option::is_some");
                self.codegen_option_is_some(args, destination, target)
            }
            "unwrap_or_else" => {
                debug!("AY codegen: handling Option::unwrap_or_else");
                self.codegen_option_unwrap_or_else(args, destination, target)
            }
            "unwrap_or" => {
                debug!("AY codegen: handling Option::unwrap_or");
                self.codegen_option_unwrap_or(args, destination, target)
            }
            "expect" => {
                debug!("AY codegen: handling Option::expect - delegating to unwrap");
                self.codegen_option_unwrap(args, destination, target)
            }
            "unwrap" => {
                debug!("AY codegen: handling Option::unwrap");
                self.codegen_option_unwrap(args, destination, target)
            }
            _ => None, // non-enum: &str
        }
    }
}
