// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! StubKind-based primitive comparison dispatch (Part of #2306).
//! String-based comparison + wrapping arithmetic: `codegen_call_cmp_string.rs`.
//!
//! Ordering computation (Ord, PartialOrd, fat-ptr): `codegen_call_cmp_ord.rs`.
//! Operand resolution (deref, raw-ptr, array recovery): `codegen_call_cmp_operand.rs`.

use std::collections::HashSet;

use ay_bindings::{Expr, ExprValue, Sort};
use rustc_public::mir::Operand;
use rustc_public::ty::{RigidTy, Ty, TyKind};

use crate::codegen_ay::stubs::StubKind;
use crate::codegen_ay::types::{SignExtension, coerce_bitvec_width_safe, ptr_sort};

use super::super::fieldless_constructor_cmp::try_fieldless_constructor_comparison;
use super::ChcCtx;
use super::chc_call_context::{ChcCallContext, DispatchCallContext};
use super::codegen_call_cmp_array_stub::compute_array_cmp_result;
use super::codegen_call_cmp_operand::{
    extract_single_ref_pointee, is_raw_ptr_cmp_arg, is_raw_ptr_cmp_arg_any_depth,
};
use super::codegen_call_cmp_string::cmp_slice_backing::{
    SliceBackingCmpResult, compute_optional_slice_backing_cmp_result,
};
use super::codegen_call_coerce::{CallCoerce, emit_sound_fallback_goto};
use super::codegen_call_kani_model_dst::is_zst_ty;
use super::codegen_call_misc::CallMisc;
use super::codegen_expr_signedness::arg_signedness_for_cmp;
use super::codegen_rules::CodegenRules;
use tracing::debug;

/// Extension trait for StubKind-based primitive comparison handlers.
pub(in crate::codegen_ay::chc) trait CallCmp {
    /// Handle primitive comparison/equality stubs routed via StubKind.
    /// Returns `true` if the call was handled, `false` to decline so fn_inline
    /// can attempt the call instead (Part of #3041).
    fn codegen_call_primitive_cmp_stub(&mut self, bb_idx: usize, cx: &ChcCallContext<'_>) -> bool;

    /// Part of #4203: Pre-inline PartialEq dispatch for flattened tuple types.
    ///
    /// When `<(T1, T2) as PartialEq>::eq` is called on flattened tuple locals,
    /// the StubKind handler declines (operand resolution returns mismatched sorts)
    /// and fn_inline fails (derived PartialEq body has flattened sort != Datatype
    /// sort mismatch). This dispatch intercepts the call before fn_inline,
    /// reconstructs both operands from flattened field state variables using
    /// `try_reconstruct_cmp_operands_from_flattened`, and emits a direct `.eq()`
    /// or `.ne()` constraint.
    ///
    /// Returns `true` if the call was handled, `false` otherwise.
    fn try_dispatch_call_flattened_partial_eq(&mut self, dcx: &DispatchCallContext<'_>) -> bool;

    /// Pre-stub dispatch for direct fixed-array `PartialEq` cases whose value
    /// semantics do not depend on payload reads.
    fn try_dispatch_call_fixed_unit_array_partial_eq(
        &mut self,
        dcx: &DispatchCallContext<'_>,
    ) -> bool;
}

impl<'tcx, 'body> CallCmp for ChcCtx<'tcx, 'body> {
    fn codegen_call_primitive_cmp_stub(&mut self, bb_idx: usize, cx: &ChcCallContext<'_>) -> bool {
        let dest_local: usize = cx.destination.local;
        if cx.args.len() < 2 {
            // Comparison needs 2 args — insufficient args is a translation failure (Part of #3123).
            #[rustfmt::skip]
            emit_sound_fallback_goto(self, cx.from_app, cx.target, cx.modified_locals, &[dest_local], cx.stmt_constraints);
            return true;
        }

        if let Some(cmp_result) = self.fixed_unit_array_cmp_result(cx) {
            self.emit_cmp_result(cx, dest_local, cmp_result);
            return true;
        }

        // Part of #3041: Full 6-tier referent resolution (const refs, arg pointees).
        let lhs = self.resolve_ref_or_const_referent(&cx.args[0], cx.modified_locals);
        let rhs = self.resolve_ref_or_const_referent(&cx.args[1], cx.modified_locals);

        let (Some(mut lhs), Some(mut rhs)) = (lhs, rhs) else {
            // Part of #3041: decline so fn_inline can try the actual method body.
            return false;
        };

        // Part of #3248: use ZST-aware signedness for comparisons to avoid
        // spurious fallback counts on empty tuples and fieldless structs.
        let is_signed = arg_signedness_for_cmp(&cx.args[0], self.body.locals());

        if self.prepare_cmp_operands(cx, dest_local, is_signed, &mut lhs, &mut rhs) {
            return true;
        }

        // Part of #4131: BV128 wide pointers decompose into (data_ptr, metadata).
        let is_raw_ptr = is_raw_ptr_cmp_arg_any_depth(&cx.args[0], self.body.locals());

        let cmp_result_opt = compute_array_cmp_result(
            cx.stub,
            &lhs,
            &rhs,
            &cx.args[0],
            self.body.locals(),
            is_signed,
        )
        .or_else(|| {
            Self::compute_cmp_result(cx.stub, lhs.clone(), rhs.clone(), is_signed, is_raw_ptr)
        });
        // Part of #4070: When referent resolution returns mismatched sorts,
        // try to reconstruct operands from flattened field state variables.
        let cmp_result_opt = cmp_result_opt.or_else(|| {
            let (rlhs, rrhs) = self.try_reconstruct_cmp_operands_from_flattened(
                &cx.args[0],
                &cx.args[1],
                &lhs,
                &rhs,
                cx.modified_locals,
            )?;
            Self::compute_cmp_result(cx.stub, rlhs, rrhs, is_signed, is_raw_ptr)
        });
        let Some(cmp_result) = cmp_result_opt else {
            debug!("primitive cmp unsupported sorts (bb{}->bb{})", bb_idx, cx.target);
            #[rustfmt::skip]
            emit_sound_fallback_goto(self, cx.from_app, cx.target, cx.modified_locals, &[dest_local], cx.stmt_constraints);
            return true;
        };

        self.emit_cmp_result(cx, dest_local, cmp_result);
        true
    }

    fn try_dispatch_call_flattened_partial_eq(&mut self, dcx: &DispatchCallContext<'_>) -> bool {
        let Some(target) = dcx.target else { return false };
        if dcx.args.len() < 2 {
            return false;
        }
        let callee_path = dcx
            .callee_path
            .clone()
            .or_else(|| self.resolve_callee_path(dcx.func))
            .or_else(|| self.resolve_fn_def_name(dcx.func));
        let Some(ref path) = callee_path else { return false };
        if !path.contains("cmp::PartialEq") {
            return false;
        }
        let is_eq = match path.rsplit("::").next() {
            Some("eq") => true,
            Some("ne") => false,
            _ => return false,
        };
        // Only fire when at least one operand involves a flattened tuple local.
        let has_flattened = self.operand_involves_flattened(&dcx.args[0])
            || self.operand_involves_flattened(&dcx.args[1]);
        if !has_flattened {
            return false;
        }
        let modified_locals = dcx.modified_locals;
        let dest_local: usize = dcx.destination.local;
        // Resolve operands — may return mismatched sorts for flattened locals.
        let lhs = self.resolve_ref_or_const_referent(&dcx.args[0], modified_locals);
        let rhs = self.resolve_ref_or_const_referent(&dcx.args[1], modified_locals);
        let (lhs_orig, rhs_orig) = match (lhs, rhs) {
            (Some(l), Some(r)) => (l, r),
            _ => {
                // Cannot resolve operands at all — try translating directly.
                let l = self.translate_operand_with_modified(&dcx.args[0], modified_locals);
                let r = self.translate_operand_with_modified(&dcx.args[1], modified_locals);
                match (l, r) {
                    (Some(l), Some(r)) => (l, r),
                    _ => return false,
                }
            }
        };
        // Try reconstruction from flattened fields.
        let (rlhs, rrhs) = if lhs_orig.sort() == rhs_orig.sort() {
            (lhs_orig, rhs_orig)
        } else if let Some((rl, rr)) = self.try_reconstruct_cmp_operands_from_flattened(
            &dcx.args[0],
            &dcx.args[1],
            &lhs_orig,
            &rhs_orig,
            modified_locals,
        ) {
            (rl, rr)
        } else {
            return false;
        };
        let cmp_result = Self::compute_partial_eq(rlhs.clone(), rrhs.clone(), false, is_eq)
            .unwrap_or_else(|| if is_eq { rlhs.eq(rrhs) } else { rlhs.ne(rrhs) });
        debug!(
            is_eq,
            path = path.as_str(),
            dest_local,
            "CHC: flattened tuple PartialEq pre-inline dispatch (Part of #4203)"
        );
        let cx = ChcCallContext {
            stub: if is_eq {
                StubKind::PrimitivePartialEqEq
            } else {
                StubKind::PrimitivePartialEqNe
            },
            args: dcx.args,
            destination: dcx.destination,
            target: *target,
            from_app: dcx.from_app,
            stmt_constraints: dcx.stmt_constraints,
            modified_locals,
        };
        self.emit_cmp_result(&cx, dest_local, cmp_result);
        true
    }

    fn try_dispatch_call_fixed_unit_array_partial_eq(
        &mut self,
        dcx: &DispatchCallContext<'_>,
    ) -> bool {
        let Some(target) = dcx.target else {
            return false;
        };
        if dcx.args.len() < 2 {
            return false;
        }
        let callee_path = dcx
            .callee_path
            .clone()
            .or_else(|| self.resolve_callee_path(dcx.func))
            .or_else(|| self.resolve_fn_def_name(dcx.func));
        let Some(ref path) = callee_path else {
            return false;
        };
        if !path.contains("cmp::PartialEq") {
            return false;
        }
        let stub = match path.rsplit("::").next() {
            Some("eq") => StubKind::PrimitivePartialEqEq,
            Some("ne") => StubKind::PrimitivePartialEqNe,
            _ => return false,
        };

        let cx = ChcCallContext {
            stub,
            args: dcx.args,
            destination: dcx.destination,
            target: *target,
            from_app: dcx.from_app,
            stmt_constraints: dcx.stmt_constraints,
            modified_locals: dcx.modified_locals,
        };
        let Some(cmp_result) = self.fixed_unit_array_cmp_result(&cx) else {
            return false;
        };

        self.emit_cmp_result(&cx, dcx.destination.local, cmp_result);
        true
    }
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Part of #4203: Check if an operand involves a flattened tuple local.
    ///
    /// Returns true if the operand references a local that is either directly
    /// flattened or is a reference to a flattened local (via ref_targets).
    fn operand_involves_flattened(&self, arg: &Operand) -> bool {
        let local = match arg {
            Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => p.local,
            _ => return false,
        };
        if self.flatten.flattened_tuple_locals.contains(&local) {
            return true;
        }
        if let Some(target) = self.ref_resolution.ref_targets.get(&local) {
            return self.flatten.flattened_tuple_locals.contains(&target.local);
        }
        false
    }

    fn prepare_cmp_operands(
        &mut self,
        cx: &ChcCallContext<'_>,
        dest_local: usize,
        is_signed: bool,
        lhs: &mut Expr,
        rhs: &mut Expr,
    ) -> bool {
        // Part of #4030: Raw pointer Ord compares addresses, not content.
        if !is_raw_ptr_cmp_arg(&cx.args[0], self.body.locals()) {
            if self.maybe_emit_slice_backing_cmp_result(cx, dest_local, is_signed) {
                return true;
            }
            // #3792: recover fixed-array operands from `&&[T; N]`.
            #[rustfmt::skip]
            self.recover_fixed_array_cmp_operands(lhs, rhs, &cx.args, cx.modified_locals);
            // #3994: ZST short-circuit.
            if self.maybe_emit_zst_cmp_result(cx, dest_local, lhs, rhs) {
                return true;
            }
            // #3270: deref pointer operands to pointee values.
            self.deref_cmp_operands_if_needed(lhs, rhs, &cx.args, cx.modified_locals);
        }
        // Part of #4030: Double-ref raw pointer case (`&&*const T`).
        self.resolve_double_ref_raw_ptr_cmp(lhs, rhs, &cx.args, cx.modified_locals);
        false
    }

    /// Emit a precise slice-backed comparison, or a fail-closed fallback when
    /// slice backing exists but cannot be compared precisely.
    fn maybe_emit_slice_backing_cmp_result(
        &mut self,
        cx: &ChcCallContext<'_>,
        dest_local: usize,
        is_signed: bool,
    ) -> bool {
        match self.try_compute_slice_cmp_result(cx, is_signed) {
            Some(SliceBackingCmpResult::Precise(cmp_result)) => {
                self.emit_cmp_result(cx, dest_local, cmp_result);
                true
            }
            Some(SliceBackingCmpResult::Unsupported) => {
                debug!(
                    fn_name = %self.fn_name,
                    "cmp_stub: slice-backed comparison unsupported; using sound fallback"
                );
                #[rustfmt::skip]
                emit_sound_fallback_goto(self, cx.from_app, cx.target, cx.modified_locals, &[dest_local], cx.stmt_constraints);
                true
            }
            None => false,
        }
    }

    /// Build lexicographic slice comparison from resolved backing arrays while
    /// preserving each operand's recovered length and logical offset.
    fn try_compute_slice_cmp_result(
        &mut self,
        cx: &ChcCallContext<'_>,
        is_signed: bool,
    ) -> Option<SliceBackingCmpResult> {
        if is_raw_ptr_cmp_arg_any_depth(&cx.args[0], self.body.locals()) {
            return None;
        }
        let lhs = self.resolve_slice_backing(&cx.args[0], cx.modified_locals);
        let rhs = self.resolve_slice_backing(&cx.args[1], cx.modified_locals);
        compute_optional_slice_backing_cmp_result(cx.stub, lhs.as_ref(), rhs.as_ref(), is_signed)
    }

    /// Fixed-array `PartialEq` for zero-length arrays and arrays of `()`.
    ///
    /// These cases are value-semantic and do not need payload reads: `[T; 0]`
    /// has no element comparisons, and `[(); N]` has only unit elements.
    fn fixed_unit_array_cmp_result(&self, cx: &ChcCallContext<'_>) -> Option<Expr> {
        let is_eq = match cx.stub {
            StubKind::PrimitivePartialEqEq => true,
            StubKind::PrimitivePartialEqNe => false,
            _ => return None,
        };

        self.fixed_unit_array_eq_expr_from_args(cx.args).map(|_| Expr::bool_const(is_eq))
    }

    pub(in crate::codegen_ay::chc) fn fixed_unit_array_eq_expr_from_args(
        &self,
        args: &[Operand],
    ) -> Option<Expr> {
        let (lhs_elem, lhs_len) = self.fixed_array_operand_elem_len(args.first()?)?;
        let (rhs_elem, rhs_len) = self.fixed_array_operand_elem_len(args.get(1)?)?;
        if lhs_len != rhs_len {
            return None;
        }

        let same_value = lhs_len == 0 || (is_unit_ty(lhs_elem) && is_unit_ty(rhs_elem));
        same_value.then(|| Expr::bool_const(true))
    }

    fn fixed_array_operand_elem_len(&self, operand: &Operand) -> Option<(Ty, u64)> {
        let ty = self.resolve_body_ty(operand.ty(self.body.locals()).ok()?);
        fixed_array_elem_len_from_ty(self.resolve_body_ty(ty))
    }

    /// PartialEq::eq / PartialEq::ne.
    pub(super) fn compute_partial_eq(
        lhs: Expr,
        rhs: Expr,
        is_signed: bool,
        is_eq: bool,
    ) -> Option<Expr> {
        if let Some(result) = try_fieldless_constructor_comparison(&lhs, &rhs, is_eq) {
            return Some(result);
        }
        if lhs.sort().is_bitvec()
            && rhs.sort().is_bitvec()
            && let Some(target_width) =
                lhs.sort().bitvec_width().zip(rhs.sort().bitvec_width()).map(|(l, r)| l.max(r))
        {
            let lhs = coerce_bitvec_width_safe(
                lhs,
                target_width,
                SignExtension::for_signedness(is_signed),
            );
            let rhs = coerce_bitvec_width_safe(
                rhs,
                target_width,
                SignExtension::for_signedness(is_signed),
            );
            Some(if is_eq { lhs.eq(rhs) } else { lhs.ne(rhs) })
        } else if (lhs.sort().is_int() && rhs.sort().is_int())
            || (lhs.sort().is_bool() && rhs.sort().is_bool())
        {
            Some(if is_eq { lhs.eq(rhs) } else { lhs.ne(rhs) })
        } else if let Some(result) = try_option_like_datatype_partial_eq(&lhs, &rhs, is_eq) {
            Some(result)
        } else if lhs.sort().datatype_name().is_some()
            && rhs.sort().datatype_name().is_some()
            && lhs.sort() == rhs.sort()
        {
            // Part of #3208: Support PartialEq on Datatype sorts (Option<T>,
            // Result<T,E>, user-defined enums with derived PartialEq). SMT
            // equality on Datatypes is structural — it compares constructors
            // and field values recursively, which matches derived PartialEq
            // semantics exactly.
            Some(if is_eq { lhs.eq(rhs) } else { lhs.ne(rhs) })
        } else if let Some(result) = Self::try_coerce_bv_datatype_eq(lhs, rhs, is_eq) {
            // Part of #4023: BV discriminant vs Datatype sort mismatch.
            // When the enum flatten layer collapses CoroutineState (or similar
            // ZST-payload enums) to a BV discriminant but the comparison constant
            // retains its full Datatype encoding, convert the Datatype to its
            // constructor-index BV and compare as BV.
            Some(result)
        } else {
            None
        }
    }

    /// Part of #4070: Reconstruct flattened tuple operands for PartialEq.
    /// Follows `ref_targets` to find referent locals and reconstructs full Datatypes
    /// from flattened field state variables when sorts are mismatched.
    fn try_reconstruct_cmp_operands_from_flattened(
        &self,
        arg0: &Operand,
        arg1: &Operand,
        original_lhs: &Expr,
        original_rhs: &Expr,
        modified_locals: &HashSet<usize>,
    ) -> Option<(Expr, Expr)> {
        // Only attempt when original resolution produced mismatched sorts.
        if original_lhs.sort() == original_rhs.sort() {
            return None;
        }
        // Helper: try to reconstruct an operand from flattened fields.
        // For mutable locals: follow ref_targets → reconstruct from flattened fields.
        // For promoted constants: the original resolved expr is already correct
        // (just happens to be the wrong sort in the ref-resolution chain).
        let try_reconstruct_one = |arg: &Operand, original: &Expr| -> Option<Expr> {
            let local = match arg {
                Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => p.local,
                _ => return None,
            };
            // Try ref_targets → flattened reconstruction.
            if let Some(target) = self.ref_resolution.ref_targets.get(&local) {
                if let Some(dt) =
                    self.reconstruct_flattened_bare_read(target.local, modified_locals)
                {
                    return Some(dt);
                }
            }
            // If original is already a Datatype, use it directly.
            if original.sort().datatype_name().is_some() {
                return Some(original.clone());
            }
            // Try const_ref_values — promoted constant Datatype values.
            if let Some(expr) = self.ref_resolution.const_ref_values.get(&local) {
                if expr.sort().datatype_name().is_some() {
                    return Some(expr.clone());
                }
            }
            // Try reconstructing the arg local itself (for refs assigned from
            // promoted constant aggregates that are flattened).
            if self.flatten.flattened_tuple_locals.contains(&local) {
                if let Some(dt) = self.reconstruct_flattened_bare_read(local, modified_locals) {
                    return Some(dt);
                }
            }
            None
        };
        let rlhs = try_reconstruct_one(arg0, original_lhs)?;
        let rrhs = try_reconstruct_one(arg1, original_rhs)?;
        if rlhs.sort() != rrhs.sort() {
            return None;
        }
        debug!(
            sort = ?rlhs.sort(),
            fn_name = %self.fn_name,
            "cmp_stub: reconstructed flattened tuple operands for PartialEq"
        );
        Some((rlhs, rrhs))
    }

    /// Part of #4023: BV discriminant vs Datatype sort coercion for PartialEq.
    /// Converts Datatype operand to constructor-index BV via ITE chain when the
    /// enum flatten layer encodes the destination as a BV discriminant. Sound for
    /// enums where equality is purely discriminant-based (ZST/Bool payloads).
    fn try_coerce_bv_datatype_eq(lhs: Expr, rhs: Expr, is_eq: bool) -> Option<Expr> {
        // Identify which is BV and which is Datatype.
        let (bv_expr, dt_expr) = if lhs.sort().is_bitvec() && rhs.sort().datatype_name().is_some() {
            (lhs, rhs)
        } else if rhs.sort().is_bitvec() && lhs.sort().datatype_name().is_some() {
            (rhs, lhs)
        } else {
            return None;
        };

        let bv_width = bv_expr.sort().bitvec_width()?;
        let dt_sort = dt_expr.sort().datatype_sort()?;
        let dt_name = &dt_sort.name;
        let ctors = &dt_sort.constructors;

        if ctors.is_empty() {
            return None;
        }

        // Part of #4026: Guard against packed BV encodings. For niche-encoded
        // enums (e.g., MyEnum with DataFul(bool)), the flatten layer packs
        // discriminant + payload bits into a single BV. The constructor-index
        // coercion is only sound when the BV is a pure discriminant — i.e.,
        // its width equals the minimum bits needed for the constructor count.
        // If wider, payload bits are packed in and the index mapping is wrong.
        let min_bits =
            if ctors.len() <= 1 { 1u32 } else { (ctors.len() as f64).log2().ceil() as u32 };
        if bv_width > min_bits {
            return None;
        }

        // Build ITE chain: for constructor i, if is_constructor(dt, ctor_i) then BV(i)
        // Start from the last constructor as the else-branch default.
        let last_idx = ctors.len() - 1;
        let mut result_bv = Expr::bitvec_const(last_idx as i128, bv_width);

        for (idx, ctor) in ctors.iter().enumerate().rev().skip(1) {
            let is_this_ctor = dt_expr.clone().is_constructor(dt_name.clone(), ctor.name.clone());
            let idx_bv = Expr::bitvec_const(idx as i128, bv_width);
            result_bv = Expr::ite(is_this_ctor, idx_bv, result_bv);
        }

        // Now compare the coerced BV against the original BV operand.
        Some(if is_eq { bv_expr.eq(result_bv) } else { bv_expr.ne(result_bv) })
    }

    /// Assign the comparison result expression to the destination local.
    fn maybe_emit_zst_cmp_result(
        &mut self,
        cx: &ChcCallContext<'_>,
        dest_local: usize,
        lhs: &Expr,
        rhs: &Expr,
    ) -> bool {
        if *lhs.sort() != ptr_sort() || *rhs.sort() != ptr_sort() {
            return false;
        }
        if !extract_single_ref_pointee(&cx.args[0], self.body.locals()).map_or(false, is_zst_ty) {
            return false;
        }

        let cmp_result = match cx.stub {
            // ZSTs are always equal: eq/le/ge -> true; ne/lt/gt -> false.
            StubKind::PrimitivePartialEqEq
            | StubKind::PrimitivePartialOrdLe
            | StubKind::PrimitivePartialOrdGe => Expr::bool_const(true),
            StubKind::OrdCmp => {
                // Ordering::Equal encoded as 0i8.
                Expr::bitvec_const(0u64, 8)
            }
            _ => Expr::bool_const(false),
        };
        self.emit_cmp_result(cx, dest_local, cmp_result);
        true
    }

    /// Assign the comparison result expression to the destination local.
    fn emit_cmp_result(&mut self, cx: &ChcCallContext<'_>, dest_local: usize, cmp_result: Expr) {
        if let Some((_, dest_var)) = self.resolve_destination(dest_local) {
            let out_sort = dest_var.sort();
            let final_result = if *cmp_result.sort() == *out_sort {
                Some(cmp_result)
            } else if cmp_result.sort().is_bool() {
                if out_sort.is_bool() {
                    Some(cmp_result)
                } else {
                    out_sort.bitvec_width().map(|w| {
                        Expr::ite(cmp_result, Expr::bitvec_const(1, w), Expr::bitvec_const(0, w))
                    })
                }
            } else {
                out_sort
                    .bitvec_width()
                    .map(|w| coerce_bitvec_width_safe(cmp_result, w, SignExtension::SignExtend))
            };
            if let Some(converted) = final_result {
                let eq_constraint = self.make_coerced_eq_constraint(
                    &dest_var,
                    converted,
                    out_sort,
                    dest_local,
                    "codegen_call_primitive_cmp_stubkind",
                );
                let new_output_args = self.build_output_args(cx.modified_locals, &[dest_local]);
                self.emit_goto_rule_extra(
                    cx.from_app,
                    cx.target,
                    &new_output_args,
                    cx.stmt_constraints,
                    eq_constraint,
                );
            } else {
                // Sort conversion failed — cmp result unconstrained (Part of #3123).
                #[rustfmt::skip]
                emit_sound_fallback_goto(self, cx.from_app, cx.target, cx.modified_locals, &[dest_local], cx.stmt_constraints);
            }
        } else {
            // resolve_destination failed — dest unconstrained (Part of #3123).
            #[rustfmt::skip]
            emit_sound_fallback_goto(self, cx.from_app, cx.target, cx.modified_locals, &[dest_local], cx.stmt_constraints);
        }
    }

    pub(in crate::codegen_ay::chc) fn primitive_cmp_method(path: &str) -> Option<&'static str> {
        if path.contains("BigInt") || path.contains("BigUint") || path.contains("BigRational") {
            return None;
        }

        match path.rsplit("::").next() {
            Some("cmp") => Some("cmp"),
            Some("partial_cmp") => Some("partial_cmp"),
            Some("eq") => Some("eq"),
            Some("ne") => Some("ne"),
            Some("lt") => Some("lt"),
            Some("le") => Some("le"),
            Some("gt") => Some("gt"),
            Some("ge") => Some("ge"),
            // Part of #4008: Ord::{min, max, clamp} on raw pointers.
            Some("min") if path.contains("::Ord") => Some("min"),
            Some("max") if path.contains("::Ord") => Some("max"),
            Some("clamp") if path.contains("::Ord") => Some("clamp"),
            _ => None, // non-enum: &str
        }
    }

    pub(in crate::codegen_ay::chc) fn step_unchecked_method(path: &str) -> Option<bool> {
        if !path.contains("Step") {
            return None;
        }
        match path.rsplit("::").next() {
            Some("forward_unchecked") => Some(true),
            Some("backward_unchecked") => Some(false),
            _ => None, // non-enum: &str
        }
    }
}

#[derive(Clone)]
enum OptionLikeView {
    None,
    Some(Expr),
    Symbolic { is_some: Expr, payload: Expr },
}

fn try_option_like_datatype_partial_eq(lhs: &Expr, rhs: &Expr, is_eq: bool) -> Option<Expr> {
    if lhs.sort() != rhs.sort() || !is_option_like_sort(lhs.sort()) {
        return None;
    }
    let lhs = option_like_view(lhs)?;
    let rhs = option_like_view(rhs)?;
    let eq = option_like_view_eq(lhs, rhs)?;
    Some(if is_eq { eq } else { eq.not() })
}

fn is_option_like_sort(sort: &Sort) -> bool {
    let Some(dt) = sort.datatype_sort() else {
        return false;
    };
    if dt.constructors.len() != 2 {
        return false;
    }
    let mut arities = dt.constructors.iter().map(|ctor| ctor.fields.len()).collect::<Vec<_>>();
    arities.sort_unstable();
    arities == [0, 1]
}

fn option_like_view(expr: &Expr) -> Option<OptionLikeView> {
    match expr.value() {
        ExprValue::DatatypeConstructor { args, .. } if args.is_empty() => {
            Some(OptionLikeView::None)
        }
        ExprValue::DatatypeConstructor { args, .. } if args.len() == 1 => {
            Some(OptionLikeView::Some(args[0].clone()))
        }
        ExprValue::Ite { cond, then_expr, else_expr } => {
            let then_view = option_like_view(then_expr)?;
            let else_view = option_like_view(else_expr)?;
            match (then_view, else_view) {
                (OptionLikeView::Some(payload), OptionLikeView::None) => {
                    Some(OptionLikeView::Symbolic { is_some: cond.clone(), payload })
                }
                (OptionLikeView::None, OptionLikeView::Some(payload)) => {
                    Some(OptionLikeView::Symbolic { is_some: cond.clone().not(), payload })
                }
                _ => None,
            }
        }
        _ => None,
    }
}

fn option_like_view_eq(lhs: OptionLikeView, rhs: OptionLikeView) -> Option<Expr> {
    match (lhs, rhs) {
        (OptionLikeView::None, OptionLikeView::None) => Some(Expr::bool_const(true)),
        (OptionLikeView::Some(lhs), OptionLikeView::Some(rhs)) => Some(lhs.eq(rhs)),
        (OptionLikeView::None, OptionLikeView::Some(_))
        | (OptionLikeView::Some(_), OptionLikeView::None) => Some(Expr::bool_const(false)),
        (OptionLikeView::Symbolic { is_some, payload }, OptionLikeView::Some(expected))
        | (OptionLikeView::Some(expected), OptionLikeView::Symbolic { is_some, payload }) => {
            Some(is_some.and(payload.eq(expected)))
        }
        (OptionLikeView::Symbolic { is_some, .. }, OptionLikeView::None)
        | (OptionLikeView::None, OptionLikeView::Symbolic { is_some, .. }) => Some(is_some.not()),
        (
            OptionLikeView::Symbolic { is_some: lhs_is_some, payload: lhs_payload },
            OptionLikeView::Symbolic { is_some: rhs_is_some, payload: rhs_payload },
        ) => {
            let same_discriminant = lhs_is_some.clone().eq(rhs_is_some.clone());
            let same_payload_when_some =
                lhs_is_some.and(rhs_is_some).implies(lhs_payload.eq(rhs_payload));
            Some(same_discriminant.and(same_payload_when_some))
        }
    }
}

fn fixed_array_elem_len_from_ty(mut ty: Ty) -> Option<(Ty, u64)> {
    for _ in 0..4 {
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Array(elem, len_const)) => {
                return len_const.eval_target_usize().ok().map(|len| (elem, len));
            }
            TyKind::RigidTy(RigidTy::Ref(_, inner, _) | RigidTy::RawPtr(inner, _)) => ty = inner,
            _ => return None,
        }
    }
    None
}

fn is_unit_ty(ty: Ty) -> bool {
    matches!(ty.kind(), TyKind::RigidTy(RigidTy::Tuple(fields)) if fields.is_empty())
}
