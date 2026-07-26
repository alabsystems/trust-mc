// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! PartialOrd trait comparison dispatch: lt, le, gt, ge.

use rustc_public::mir::{BasicBlockIdx, Operand, Place};
use tracing::debug;

use super::extract_method_name;
use crate::codegen_ay::statement::StatementCodegen;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// PartialOrd trait comparison dispatching for lt, le, gt, ge.
    pub(in crate::codegen_ay::statement) fn dispatch_partial_ord(
        &mut self,
        fn_name: &str,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if !fn_name.contains("PartialOrd") {
            return None;
        }
        let method = extract_method_name(fn_name)?;

        match method {
            "lt" => {
                debug!("AY codegen: handling PartialOrd::lt (less-than comparison)");
                self.codegen_partial_ord_cmp(args, destination, target, "lt")
            }
            "le" => {
                debug!("AY codegen: handling PartialOrd::le (less-or-equal comparison)");
                self.codegen_partial_ord_cmp(args, destination, target, "le")
            }
            "gt" => {
                debug!("AY codegen: handling PartialOrd::gt (greater-than comparison)");
                self.codegen_partial_ord_cmp(args, destination, target, "gt")
            }
            "ge" => {
                debug!("AY codegen: handling PartialOrd::ge (greater-or-equal comparison)");
                self.codegen_partial_ord_cmp(args, destination, target, "ge")
            }
            _ => None, // non-enum: &str
        }
    }
}
