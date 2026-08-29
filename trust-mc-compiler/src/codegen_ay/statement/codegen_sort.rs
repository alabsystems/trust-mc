// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Sort inference and coercion (converted from include!() per #2595).

use super::{IntoOption, StatementCodegen};
use crate::codegen_ay::names::{self, struct_sort};
use crate::codegen_ay::types::{SignExtension, bool_sort, bv8_sort, coerce_bitvec_width, ptr_sort};
use ay_bindings::{Expr, Sort};
use rustc_public::mir::{
    AggregateKind, AssertMessage, BinOp, Operand, Place, ProjectionElem, Rvalue, UnOp,
};
use rustc_public::ty::{RigidTy, TyKind};

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    pub(super) fn codegen_assign_checked_binary_op(
        &mut self,
        lhs: &Place,
        op: BinOp,
        l: &Operand,
        r: &Operand,
    ) {
        // Defer location formatting — same format used by 5 error paths below (Part of #2267).
        let location = || format!("{:?}", lhs);

        if !lhs.projection.is_empty() {
            self.ctx.unsupported_with_fallback("CheckedBinaryOp assign projection", location());
            return;
        }

        let is_signed = self.is_signed_integer_op(l, r).unwrap_or_else(|| {
            // Default to signed when signedness is unknown (Part of #3141, #2714).
            // Signed is the conservative choice: signed overflow is UB in C but
            // defined in Rust, so signed checks are strictly more checking.
            tracing::debug!("CheckedBinaryOp: signedness unknown, defaulting to signed");
            true
        });

        let Some(lhs_expr) = self.codegen_operand(l) else {
            self.ctx.unsupported_with_fallback("CheckedBinaryOp lhs operand", location());
            return;
        };
        let Some(rhs_expr) = self.codegen_operand(r) else {
            self.ctx.unsupported_with_fallback("CheckedBinaryOp rhs operand", location());
            return;
        };

        let result_expr =
            self.codegen_binop_typed(op, lhs_expr.clone(), rhs_expr.clone(), Some(is_signed));
        let Some((no_overflow, _label)) = self.overflow_check(op, &lhs_expr, &rhs_expr, is_signed)
        else {
            self.ctx.unsupported_with_fallback("CheckedBinaryOp overflow op", location());
            return;
        };
        let overflowed_expr = no_overflow.not();

        let base_name = self.ssa_base_name(lhs);

        let result_base = crate::codegen_ay::names::indexed_field_name(&base_name, 0);
        let result_name = self.ssa_name_from_base(&result_base, true);
        let result_var = self.ctx.declare_var(&result_name, result_expr.sort().clone());
        // SSA def with ite semantics (#2081)
        self.assert_ssa_def(result_var.clone(), result_expr, &result_base);
        self.env_update(result_base, result_var);

        let overflow_base = crate::codegen_ay::names::indexed_field_name(&base_name, 1);
        let overflow_name = self.ssa_name_from_base(&overflow_base, true);
        let overflow_var = self.ctx.declare_var(&overflow_name, bool_sort());
        // SSA def with ite semantics (#2081)
        self.assert_ssa_def(overflow_var.clone(), overflowed_expr, &overflow_base);
        self.env_update(overflow_base, overflow_var);
    }

    pub(super) fn tuple_field_tys(&self, place: &Place) -> Option<Vec<rustc_public::ty::Ty>> {
        // Allow field projections but not Deref (same reasoning as tuple aggregate).
        // Field projections are handled by ssa_base_name; Deref requires ref_pointees (#431).
        let has_deref = place.projection.iter().any(|p| matches!(p, ProjectionElem::Deref));
        if has_deref {
            return None;
        }
        // place.ty computes the type after applying all projections.
        let ty = place.ty(self.body.locals()).into_option()?;
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Tuple(tys)) => Some(tys),
            _ => None, // external enum: TyKind
        }
    }

    fn is_tuple_local(&self, local: rustc_public::mir::Local) -> bool {
        matches!(self.body.locals()[local].ty.kind(), TyKind::RigidTy(RigidTy::Tuple(_)))
    }

    pub(super) fn tuple_flattening_allowed(&self, place: &Place) -> bool {
        let local = place.local;
        if !self.is_tuple_local(local) {
            // Conservative: allow non-tuple locals (e.g., tuple stored in struct field)
            // to keep existing behavior until a field-level analysis exists.
            return true;
        }

        self.tuple_usage.is_field_only(local)
    }

    #[must_use]
    pub(super) fn infer_sort_from_place(&self, place: &Place) -> Option<Sort> {
        let ty = place.ty(self.body.locals()).into_option()?;
        Self::infer_sort_from_ty(ty)
    }

    /// Coerce a bitvector to a target width.
    ///
    /// - If the expression is narrower than target, zero-extend.
    /// - If the expression is wider than target, truncate (extract low bits).
    /// - If already the target width, return unchanged.
    ///
    /// This is used for shift operations where MIR allows different-width operands
    /// (e.g., `u32 << u8`) but SMT-LIB requires same-width operands.
    #[must_use]
    pub(super) fn coerce_to_width(expr: Expr, target_width: u32) -> Expr {
        // Delegate to shared implementation with unsigned (zero-extend) semantics
        coerce_bitvec_width(expr, target_width, SignExtension::ZeroExtend)
    }

    /// Ensure bitvectors are already the same width when signedness is unknown.
    ///
    /// When widths differ, record an unsupported construct and avoid emitting
    /// mismatched-width constraints.
    ///
    /// REQUIRES: lhs.sort().is_bitvec() && rhs.sort().is_bitvec()
    /// ENSURES: result.is_some() ==> result.0.width == result.1.width
    /// ENSURES: result.is_none() ==> widths differ (recorded as unsupported)
    pub(super) fn coerce_to_match_widths_untyped(
        &mut self,
        lhs: Expr,
        rhs: Expr,
        location: &str,
    ) -> Option<(Expr, Expr)> {
        let lhs_width = lhs.sort().bitvec_width();
        let rhs_width = rhs.sort().bitvec_width();

        match (lhs_width, rhs_width) {
            (Some(lw), Some(rw)) if lw != rw => {
                let detail = format!("{location} (lhs {lw} != rhs {rw})");
                self.ctx.unsupported("Signedness-unknown width mismatch", &detail);
                debug_assert_eq!(lw, rw, "signedness-unknown width mismatch at {location}");
                None
            }
            _ => Some((lhs, rhs)), // non-enum: tuple (same-width or non-bitvec)
        }
    }

    /// Coerce two bitvectors to the same width for comparisons, using signedness.
    ///
    /// When widening a bitvector, use sign-extension if `signed`, else zero-extension.
    ///
    /// REQUIRES: If lhs/rhs are bitvectors, widths may differ
    /// ENSURES: result.0.width == result.1.width == max(lhs.width, rhs.width)
    /// ENSURES: Narrower operand is sign/zero extended based on `signed`
    #[must_use]
    pub(super) fn coerce_to_match_widths_typed(lhs: Expr, rhs: Expr, signed: bool) -> (Expr, Expr) {
        let lhs_width = lhs.sort().bitvec_width();
        let rhs_width = rhs.sort().bitvec_width();

        match (lhs_width, rhs_width) {
            (Some(lw), Some(rw)) if lw != rw => {
                let target = lw.max(rw);
                (
                    Self::coerce_to_width_typed(lhs, target, signed),
                    Self::coerce_to_width_typed(rhs, target, signed),
                )
            }
            (None, _) | (_, None) => {
                // #1043: One or both operands are not bitvecs
                // Handle Int/BitVec mixed case by converting to Int
                if lhs.sort().is_int() || rhs.sort().is_int() {
                    // Part of #2757: Use signed bv2int when operand is signed.
                    let lhs_int = if lhs.sort().is_int() {
                        lhs
                    } else if lhs.sort().is_bitvec() {
                        if signed { lhs.bv2int_signed() } else { lhs.bv2int() }
                    } else {
                        lhs
                    };
                    let rhs_int = if rhs.sort().is_int() {
                        rhs
                    } else if rhs.sort().is_bitvec() {
                        if signed { rhs.bv2int_signed() } else { rhs.bv2int() }
                    } else {
                        rhs
                    };
                    (lhs_int, rhs_int)
                } else {
                    // #1582: Handle closure environment tuples (single-field Datatypes)
                    // Extract the field if one operand is a single-field tuple and the other is bitvec
                    let lhs = Self::unwrap_tuple_first_field(lhs);
                    let rhs = Self::unwrap_tuple_first_field(rhs);
                    // After unwrapping, try to coerce widths again
                    let lhs_width = lhs.sort().bitvec_width();
                    let rhs_width = rhs.sort().bitvec_width();
                    if let (Some(lw), Some(rw)) = (lhs_width, rhs_width)
                        && lw != rw
                    {
                        let target = lw.max(rw);
                        return (
                            Self::coerce_to_width_typed(lhs, target, signed),
                            Self::coerce_to_width_typed(rhs, target, signed),
                        );
                    }
                    (lhs, rhs)
                }
            }
            _ => (lhs, rhs), // non-enum: tuple (same-width — no coercion needed)
        }
    }

    /// Coerce a single bitvector to a target width.
    ///
    /// REQUIRES: expr.sort().is_bitvec()
    /// ENSURES: result.sort().bitvec_width() == target_width
    /// ENSURES: If narrower, extends using sign/zero extension based on `signed`
    /// ENSURES: If wider, truncates to low bits (extract)
    #[must_use]
    pub(super) fn coerce_to_width_typed(expr: Expr, target_width: u32, signed: bool) -> Expr {
        // Delegate to shared implementation
        coerce_bitvec_width(expr, target_width, SignExtension::for_signedness(signed))
    }

    /// Unwrap SINGLE-FIELD tuple datatypes to their bitvec field for binary operations.
    ///
    /// #1582: When closures are inlined, closure environments (single-field tuples)
    /// may end up as operands to binary operations. This extracts the sole field.
    ///
    /// #1590: Multi-field tuples (closure arg tuples like `Tuple_bv32_bv32`) are NOT
    /// unwrapped here - they should have been handled by proper field projections in
    /// codegen_place. Extracting fld_0 for all operands causes multi-arg closures to
    /// use the same value for all arguments, which is incorrect.
    ///
    /// ENSURES: If expr is a single-field Datatype with bitvec field, returns that field
    /// ENSURES: Otherwise, returns expr unchanged (including multi-field tuples)
    #[must_use]
    pub(super) fn unwrap_tuple_first_field(expr: Expr) -> Expr {
        use ay_bindings::sort::SortInner;

        let sort = expr.sort().clone();
        // ONLY single-field, single-constructor datatypes (closure environments)
        if let SortInner::Datatype(dt) = sort.inner()
            && dt.constructors.len() == 1
            && let Some(cons) = dt.constructors.first()
            && cons.fields.len() == 1  // #1590: Only single-field tuples
            && let Some(field) = cons.fields.first()
            && field.sort.is_bitvec()
        {
            tracing::debug!("#1582: Unwrapping single-field tuple {} -> {}", dt.name, field.name);
            // field_select accepts impl Into<String> — pass &str to avoid String clones
            return expr.field_select(&*dt.name, &*field.name, field.sort.clone());
        }
        // #1590: Multi-field tuples are returned unchanged - caller must handle
        // via proper field projections
        expr
    }

    /// Infer AY sort from a MIR operand.
    #[must_use]
    fn infer_sort_from_operand(&self, operand: &Operand) -> Option<Sort> {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => self.infer_sort_from_place(place),
            Operand::Constant(c) => Self::infer_sort_from_ty(c.const_.ty()),
        }
    }

    /// Infer AY sort from an rvalue.
    #[must_use]
    pub(super) fn infer_sort_from_rvalue(&self, rvalue: &Rvalue) -> Sort {
        if let Some(sort) = self.try_infer_sort_from_rvalue_ty(rvalue) {
            return sort;
        }
        match rvalue {
            Rvalue::Use(Operand::Constant(_c)) => {
                // For constants, infer from the constant type
                Sort::bitvec(32) // Default to 32-bit
            }
            Rvalue::Use(_) => Sort::bitvec(32),
            Rvalue::BinaryOp(op, ..) => {
                match op {
                    BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                        bool_sort()
                    }
                    _ => Sort::bitvec(32), // external enum: BinOp — arithmetic ops return bitvec
                }
            }
            Rvalue::CheckedBinaryOp(..) => {
                // Packed tuple: (overflow_bit[1] ++ result[w]) = w+1 bits
                // Default to 33 bits (32-bit operands + 1-bit overflow)
                Sort::bitvec(33)
            }
            Rvalue::UnaryOp(UnOp::Not, operand) => {
                // Not on bool returns bool, on int returns int (bitwise not)
                self.infer_sort_from_operand(operand).unwrap_or_else(Sort::bool)
            }
            Rvalue::UnaryOp(UnOp::Neg, _) => Sort::bitvec(32),
            Rvalue::UnaryOp(UnOp::PtrMetadata, _) => ptr_sort(),
            Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place) => {
                // #1129: Check if we need a fat pointer for unsized types
                if let Some(pointee_ty) = place.ty(self.body.locals()).into_option() {
                    if Self::use_thin_pointer_for_pointee(pointee_ty) {
                        ptr_sort() // Thin pointer
                    } else {
                        // Fat pointer: (data_ptr, metadata)
                        struct_sort("FatPtr", [("data", ptr_sort()), ("meta", ptr_sort())])
                    }
                } else {
                    ptr_sort() // Fallback to thin pointer
                }
            }
            Rvalue::Len(..) => ptr_sort(),        // usize
            Rvalue::Cast(..) => Sort::bitvec(32), // Simplified
            Rvalue::Aggregate(kind, operands) => {
                // Match the codegen_aggregate logic for sort inference
                match kind {
                    AggregateKind::Tuple => Self::infer_tuple_sort_from_operands(operands, self)
                        .unwrap_or_else(|| Sort::bitvec(32)),
                    AggregateKind::Array(elem_ty) => {
                        let elem_sort =
                            Self::infer_sort_from_ty(*elem_ty).unwrap_or_else(|| Sort::bitvec(32));
                        Sort::array(ptr_sort(), elem_sort)
                    }
                    // ADT, Closure, Coroutine - fallback to generic placeholder
                    _ => Sort::bitvec(32), // external enum: AggregateKind
                }
            }
            Rvalue::Discriminant(..) => Sort::bitvec(32), // Discriminants are integers
            Rvalue::ShallowInitBox(..) => ptr_sort(),
            Rvalue::CopyForDeref(..) => ptr_sort(),
            Rvalue::ThreadLocalRef(..) => ptr_sort(),
            Rvalue::NullaryOp(..) => ptr_sort(),
            Rvalue::Repeat(..) => Sort::array(ptr_sort(), bv8_sort()), // Array fallback
        }
    }

    #[must_use]
    pub(super) fn try_infer_sort_from_rvalue_ty(&self, rvalue: &Rvalue) -> Option<Sort> {
        let ty = rvalue.ty(self.body.locals()).into_option()?;
        Self::infer_sort_from_ty(ty).or_else(|| Self::try_infer_sort_from_compound_ty(ty))
    }

    /// Infer tuple sort from operands when type information is unavailable.
    fn infer_tuple_sort_from_operands(operands: &[Operand], codegen: &Self) -> Option<Sort> {
        if operands.is_empty() {
            return Some(struct_sort("Unit", Vec::<(&str, Sort)>::new()));
        }
        let mut fields = Vec::with_capacity(operands.len());
        for (i, op) in operands.iter().enumerate() {
            let sort = codegen.infer_sort_from_operand(op)?;
            fields.push((names::tuple_field_name(i), sort));
        }
        let name = Self::tuple_sort_name(&fields);
        Some(struct_sort(name, fields))
    }

    /// Get assertion label for a given AssertMessage type.
    ///
    /// Returns standard Kani property class names for verification output.
    pub(super) fn assert_label_for_message(msg: &AssertMessage) -> &'static str {
        match msg {
            AssertMessage::BoundsCheck { .. } => "bounds_check",
            AssertMessage::DivisionByZero { .. } => "div_by_zero_check",
            AssertMessage::RemainderByZero { .. } => "mod_by_zero_check",
            AssertMessage::Overflow { .. } => "overflow_check",
            AssertMessage::OverflowNeg { .. } => "overflow_check_neg",
            // rustc's ub-check asserts. Kani renders these as class
            // `safety_check` with the rustc AssertKind texts ("null pointer
            // dereference occurred" / "misaligned pointer dereference: ..."),
            // which the corpus pins (zst, issue-3571, ptr_to_ref_cast). The
            // CBMC-flavored `null_pointer_check` / `alignment_check` wordings
            // stay on the place_deref instrumentation sites.
            AssertMessage::NullPointerDereference => "raw_ptr_deref_null",
            AssertMessage::MisalignedPointerDereference { .. } => "raw_ptr_deref_misaligned",
            AssertMessage::InvalidEnumConstruction { .. } => "enum_check",
            AssertMessage::ResumedAfterReturn { .. }
            | AssertMessage::ResumedAfterDrop { .. }
            | AssertMessage::ResumedAfterPanic { .. } => "coroutine_check",
        }
    }
}
