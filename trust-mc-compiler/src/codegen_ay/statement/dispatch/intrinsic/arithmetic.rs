// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Arithmetic intrinsic dispatch: wrapping, unchecked, checked, saturating, overflowing.

use rustc_public::mir::{BasicBlockIdx, BinOp, Operand, Place};
use tracing::debug;

use crate::codegen_ay::statement::StatementCodegen;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Arithmetic intrinsics: wrapping, unchecked, checked, saturating, overflowing.
    pub(in crate::codegen_ay::statement) fn dispatch_arithmetic(
        &mut self,
        fn_name: &str,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        // Wrapping arithmetic - just perform the operation (wraps naturally in bitvector)
        if let Some(op) = match_arithmetic_variant(fn_name, "wrapping_") {
            debug!("AY codegen: handling wrapping_{:?}", op);
            return self.codegen_wrapping_arith(args, destination, target, op);
        }
        // Unchecked arithmetic - same as wrapping BUT asserts no overflow (overflow is UB)
        if let Some(op) = match_arithmetic_variant(fn_name, "unchecked_") {
            debug!("AY codegen: handling unchecked_{:?}", op);
            return self.codegen_unchecked_arith(args, destination, target, op);
        }
        // Checked arithmetic - returns Option<T>
        if let Some(op) = match_arithmetic_variant(fn_name, "checked_") {
            debug!("AY codegen: handling checked_{:?}", op);
            return self.codegen_checked_arith(args, destination, target, op);
        }
        // Saturating arithmetic - clamp result to MIN/MAX on overflow (#273)
        if let Some(op) = match_arithmetic_variant(fn_name, "saturating_") {
            debug!("AY codegen: handling saturating_{:?}", op);
            return self.codegen_saturating_arith(args, destination, target, op);
        }
        // overflowing_add_signed: mixed-signedness add for ptr.offset() (Part of #3375)
        // Must be checked BEFORE the generic overflowing_ prefix match, because
        // "overflowing_add_signed" contains "overflowing_" but "add_signed" doesn't
        // match the "add"/"sub"/"mul" suffix variants.
        if fn_name.contains("overflowing_add_signed") {
            debug!("AY codegen: handling overflowing_add_signed");
            return self.codegen_overflowing_add_signed(args, destination, target);
        }
        // Overflowing arithmetic - returns (result, bool) tuple (#273)
        if let Some(op) = match_arithmetic_variant(fn_name, "overflowing_") {
            debug!("AY codegen: handling overflowing_{:?}", op);
            return self.codegen_overflowing_arith(args, destination, target, op);
        }
        // Raw compiler intrinsics use `{op}_with_overflow` names and return the
        // same `(result, bool)` tuple as `overflowing_{op}` methods.
        if let Some(op) = match_with_overflow_intrinsic(fn_name) {
            debug!("AY codegen: handling {:?}_with_overflow", op);
            return self.codegen_overflowing_arith(args, destination, target, op);
        }
        // exact_div intrinsic: a / b with UB if b==0, a%b!=0, or signed overflow (#3177)
        if fn_name == "exact_div" || fn_name.ends_with("::exact_div") {
            debug!("AY codegen: handling exact_div");
            return self.codegen_exact_div(args, destination, target);
        }
        None
    }
}

/// Match arithmetic variant prefix (e.g., "wrapping_add" -> Add, "checked_shl" -> Shl).
/// Returns the BinOp if fn_name contains `{prefix}{op}` where op is
/// add/sub/mul/div/rem/shl/shr.
///
/// Part of #3477: Extended from add/sub/mul to include div/rem/shl/shr.
/// Avoids per-call String allocations by scanning for prefix then checking suffix.
pub(super) fn match_arithmetic_variant(fn_name: &str, prefix: &str) -> Option<BinOp> {
    // Find the prefix in fn_name, then check what follows it
    let mut start = 0;
    while let Some(pos) = fn_name[start..].find(prefix) {
        let abs_pos = start + pos;
        let after = &fn_name[abs_pos + prefix.len()..];
        // Check the suffix after the prefix. We need exact suffix match
        // (not just starts_with) to avoid "add" matching "add_assign".
        // Since fn_name can be a full path like "core::num::wrapping_add",
        // the suffix may be followed by "::" or end of string.
        if after == "add" || after.starts_with("add::") {
            return Some(BinOp::Add);
        }
        if after == "sub" || after.starts_with("sub::") {
            return Some(BinOp::Sub);
        }
        if after == "mul" || after.starts_with("mul::") {
            return Some(BinOp::Mul);
        }
        // Part of #3477: div/rem/shl/shr parity with CHC encoding.
        if after == "div" || after.starts_with("div::") {
            return Some(BinOp::Div);
        }
        if after == "rem" || after.starts_with("rem::") {
            return Some(BinOp::Rem);
        }
        if after == "shl" || after.starts_with("shl::") {
            return Some(BinOp::Shl);
        }
        if after == "shr" || after.starts_with("shr::") {
            return Some(BinOp::Shr);
        }
        start = abs_pos + 1;
    }
    None
}

pub(super) fn match_with_overflow_intrinsic(fn_name: &str) -> Option<BinOp> {
    match fn_name.rsplit("::").next() {
        Some("add_with_overflow") => Some(BinOp::Add),
        Some("sub_with_overflow") => Some(BinOp::Sub),
        Some("mul_with_overflow") => Some(BinOp::Mul),
        _ => None,
    }
}
