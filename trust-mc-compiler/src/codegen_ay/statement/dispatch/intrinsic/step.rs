// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Step trait dispatch: forward_unchecked, backward_unchecked for iterators.

use rustc_public::mir::{BasicBlockIdx, Operand, Place};
use tracing::debug;

use super::extract_method_name;
use crate::codegen_ay::statement::StatementCodegen;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Step::forward_unchecked / backward_unchecked for iterators.
    pub(in crate::codegen_ay::statement) fn dispatch_step(
        &mut self,
        fn_name: &str,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if !fn_name.contains("Step") {
            return None;
        }
        let method = extract_method_name(fn_name)?;

        match method {
            "forward_unchecked" => {
                debug!("AY codegen: handling Step::forward_unchecked (value + step)");
                self.codegen_step_unchecked(args, destination, target, true)
            }
            "backward_unchecked" => {
                debug!("AY codegen: handling Step::backward_unchecked (value - step)");
                self.codegen_step_unchecked(args, destination, target, false)
            }
            _ => None, // non-enum: &str
        }
    }
}
