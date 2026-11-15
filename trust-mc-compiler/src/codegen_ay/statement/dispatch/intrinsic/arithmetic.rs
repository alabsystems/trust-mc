// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Arithmetic intrinsic dispatch: wrapping, unchecked, checked, saturating, overflowing.

use ay_bindings::Expr;
use rustc_public::mir::{BasicBlockIdx, BinOp, Operand, Place};
use rustc_public::ty::{RigidTy, TyKind};
use tracing::{debug, warn};

use crate::codegen_ay::statement::{IntoOption, StatementCodegen};
use crate::codegen_ay::types::POINTER_WIDTH;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Arithmetic intrinsics: wrapping, unchecked, checked, saturating, overflowing.
    pub(in crate::codegen_ay::statement) fn dispatch_arithmetic(
        &mut self,
        fn_name: &str,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        // These names are INTEGER methods. `<*const T>::wrapping_add(self, count)`
        // matches the same name, and lowering it as `ptr + count` moved the
        // pointer by `count` BYTES instead of `count * size_of::<T>()`:
        // `(&v as *const u128).wrapping_add(10)` landed 10 bytes past `v`, so
        // `offset_from` reported a misaligned distance instead of the
        // out-of-allocation pointer Kani reports
        // (tests/expected/offset-bounds-check/offset_from.rs).
        if args.first().and_then(|a| a.ty(self.body.locals()).into_option()).is_some_and(|t| {
            matches!(t.kind(), TyKind::RigidTy(RigidTy::RawPtr(..)))
        }) {
            return self.codegen_raw_ptr_wrapping_offset(fn_name, args, destination, target);
        }
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

    /// `<*T>::wrapping_add` / `wrapping_sub`: a wrapping offset by `count`
    /// ELEMENTS (`wrapping_offset`). Leaving the object is not UB here, so no
    /// obligation is emitted; a later dereference carries it. Any other
    /// arithmetic name on a raw-pointer receiver is not an integer operation
    /// and is declined.
    fn codegen_raw_ptr_wrapping_offset(
        &mut self,
        fn_name: &str,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        let op = match_arithmetic_variant(fn_name, "wrapping_")?;
        if !matches!(op, BinOp::Add | BinOp::Sub) || args.len() < 2 {
            return None;
        }
        let ptr_ty = args[0].ty(self.body.locals()).into_option();
        let Some(pointee_size) = ptr_ty.and_then(Self::pointee_size_for_offset_ty) else {
            warn!(?ptr_ty, "raw pointer {fn_name}: pointee size unknown; declining");
            return None;
        };
        let ptr = self.codegen_operand(&args[0])?;
        let count = self.codegen_operand(&args[1])?;
        let ptr = self.coerce_to_ptr_width(ptr);
        let count = Self::coerce_to_width_typed(count, POINTER_WIDTH, false);
        let bytes = count.bvmul(Expr::bitvec_const(pointee_size as u128, POINTER_WIDTH));
        let result = if matches!(op, BinOp::Add) { ptr.bvadd(bytes) } else { ptr.bvsub(bytes) };
        self.assign_value_to_place(destination, result);
        target
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
