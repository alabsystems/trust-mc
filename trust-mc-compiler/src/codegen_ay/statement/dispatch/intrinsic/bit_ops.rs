// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Bit manipulation dispatch: rotate, funnel shift, ctlz, cttz, ctpop, bswap, bitreverse.

use rustc_public::mir::{BasicBlockIdx, Operand, Place};
use tracing::debug;

use super::extract_method_name;
use crate::codegen_ay::statement::StatementCodegen;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Bit manipulation: rotate, funnel shift, ctlz, cttz, ctpop, bswap, bitreverse.
    pub(in crate::codegen_ay::statement) fn dispatch_bit_ops(
        &mut self,
        fn_name: &str,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        let method = extract_method_name(fn_name)?;

        if method == "rotate_left" {
            debug!("AY codegen: handling rotate_left");
            return self.codegen_rotate(args, destination, target, true);
        }
        if method == "rotate_right" {
            debug!("AY codegen: handling rotate_right");
            return self.codegen_rotate(args, destination, target, false);
        }
        if method == "unchecked_funnel_shl" {
            debug!("AY codegen: handling unchecked_funnel_shl");
            return self.codegen_funnel_shift(args, destination, target, true);
        }
        if method == "unchecked_funnel_shr" {
            debug!("AY codegen: handling unchecked_funnel_shr");
            return self.codegen_funnel_shift(args, destination, target, false);
        }
        // ctlz/cttz: nonzero variants are detected within the handler
        if method.starts_with("ctlz") {
            let is_nonzero_variant = method.contains("nonzero");
            debug!("AY codegen: handling ctlz (nonzero={})", is_nonzero_variant);
            return self.codegen_ctlz(args, destination, target, is_nonzero_variant);
        }
        if method.starts_with("cttz") {
            let is_nonzero_variant = method.contains("nonzero");
            debug!("AY codegen: handling cttz (nonzero={})", is_nonzero_variant);
            return self.codegen_cttz(args, destination, target, is_nonzero_variant);
        }
        if method == "ctpop" {
            debug!("AY codegen: handling ctpop (population count)");
            return self.codegen_ctpop(args, destination, target);
        }
        if method == "bswap" {
            debug!("AY codegen: handling bswap (byte swap)");
            return self.codegen_bswap(args, destination, target);
        }
        if method == "bitreverse" {
            debug!("AY codegen: handling bitreverse");
            return self.codegen_bitreverse(args, destination, target);
        }
        None
    }
}
