// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! raw_eq and comparison trait dispatch: Ord::cmp, PartialEq::eq/ne, SpecArrayEq.

use ay_bindings::Expr;
use rustc_public::mir::{BasicBlockIdx, Operand, Place};
use tracing::debug;

use super::extract_method_name;
use crate::codegen_ay::statement::StatementCodegen;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// raw_eq and comparison trait intrinsics: Ord::cmp, PartialEq::eq/ne, SpecArrayEq.
    pub(in crate::codegen_ay::statement) fn dispatch_raw_eq_and_cmp(
        &mut self,
        fn_name: &str,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        let method = extract_method_name(fn_name);
        // raw_eq intrinsic - byte-wise equality comparison (#408)
        if fn_name.contains("raw_eq") {
            debug!("AY codegen: handling raw_eq intrinsic");
            return self.codegen_raw_eq(args, destination, target);
        }
        // Ord::cmp / Ord::{min,max,clamp}
        if fn_name.contains("cmp::Ord") {
            match method {
                Some("cmp") => {
                    debug!("AY codegen: handling Ord::cmp method");
                    return self.codegen_ord_cmp(args, destination, target);
                }
                Some("min") => {
                    debug!("AY codegen: handling Ord::min method");
                    return self.codegen_ord_minmax(args, destination, target, true);
                }
                Some("max") => {
                    debug!("AY codegen: handling Ord::max method");
                    return self.codegen_ord_minmax(args, destination, target, false);
                }
                Some("clamp") => {
                    debug!("AY codegen: handling Ord::clamp method");
                    return self.codegen_ord_clamp(args, destination, target);
                }
                _ => {}
            }
        }
        // PartialEq::eq
        if fn_name.contains("PartialEq") && method == Some("eq") {
            debug!("AY codegen: handling PartialEq::eq method");
            return self.codegen_partial_eq(args, destination, target);
        }
        // PartialEq::ne
        if fn_name.contains("PartialEq") && method == Some("ne") {
            debug!("AY codegen: handling PartialEq::ne method");
            return self.codegen_partial_ne(args, destination, target);
        }
        // SpecArrayEq::spec_eq for ZST arrays (#408)
        if fn_name.contains("SpecArrayEq") && method == Some("spec_eq") {
            debug!("AY codegen: handling SpecArrayEq::spec_eq for potential ZST array");
            let is_zst_0 = !args.is_empty() && self.is_raw_eq_zst(&args[0]);
            let is_zst_1 = args.len() >= 2 && self.is_raw_eq_zst(&args[1]);
            debug!("SpecArrayEq::spec_eq: is_zst_0={}, is_zst_1={}", is_zst_0, is_zst_1);
            if is_zst_0 && is_zst_1 {
                debug!("codegen SpecArrayEq::spec_eq: ZST arrays detected, returning true");
                self.bind_ssa_result(destination, Expr::bool_const(true));
                return target;
            }
            // For non-ZST arrays, fall through to default handling
        }
        // Part of #3470: ptr_guaranteed_cmp intrinsic — returns 1u8 if equal, 0u8 otherwise.
        if method == Some("ptr_guaranteed_cmp") {
            debug!("AY codegen: handling ptr_guaranteed_cmp intrinsic");
            if args.len() >= 2 {
                if let (Some(a), Some(b)) =
                    (self.codegen_operand(&args[0]), self.codegen_operand(&args[1]))
                {
                    let one = Expr::bitvec_const(1u128, 8);
                    let zero = Expr::bitvec_const(0u128, 8);
                    let result = Expr::ite(a.eq(b), one, zero);
                    self.bind_ssa_result(destination, result);
                    return target;
                }
            }
        }
        None
    }
}
