// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Shared precise `str`-`nth` result builder.
//!
//! Part of #4161: single-sourced `StrBytesNth`/`StrCharsNth` expression
//! construction, used by both the main string dispatcher and the inline
//! walker adapter.

use std::collections::HashSet;

use ay_bindings::{Expr, Sort};
use rustc_public::mir::{Operand, ProjectionElem};
use rustc_public::ty::{RigidTy, TyKind};

use super::super::ChcCtx;
use super::super::codegen_call_coerce::CallCoerce;
use super::super::codegen_types::CodegenTypes;
use super::super::stubs_option_helpers::OptionHelpers;
use super::codegen_call_string_backing::StringBacking;
use crate::codegen_ay::types::POINTER_WIDTH;

/// Result of tracing a Call terminator for string-passthrough functions.
enum CallTraceResult {
    /// Caller's first arg resolved to a local -- continue tracing.
    Redirect(usize),
    /// Fully resolved to const string bytes.
    Resolved((Vec<u8>, usize)),
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Build the precise `Option<u8>` / `Option<char>` result expression for
    /// `kani_str_bytes_nth` / `kani_str_chars_nth`.
    ///
    /// Returns `Some(ite(index < len, Some(byte), None))` on success,
    /// `None` if the Option sort cannot be decomposed.
    pub(in crate::codegen_ay::chc) fn try_build_str_nth_result_expr(
        &self,
        backing: &StringBacking,
        index_expr: Expr,
        dest_sort: &Sort,
        is_chars: bool,
    ) -> Option<Expr> {
        let in_bounds = index_expr.clone().bvult(backing.len.clone());
        let byte_val = backing.data.clone().select(backing.offset.clone().bvadd(index_expr));
        let payload = if is_chars {
            // Zero-extend BV8 → BV32 for char representation
            byte_val.zero_extend(24)
        } else {
            byte_val
        };
        let some_expr = self.make_some_expr_for_option(payload, dest_sort)?;
        let none_expr = self.make_none_expr_for_option(dest_sort)?;
        Some(Expr::ite(in_bounds, some_expr, none_expr))
    }

    /// Resolve the whole-call result sort for `kani_str_*_nth`.
    ///
    /// Flattened `Option<T>` destinations use a Bool tag in their first output
    /// slot, so callers must not infer the result sort from
    /// `resolve_destination(dest_local)`.
    pub(in crate::codegen_ay::chc) fn str_nth_result_sort(
        &self,
        destination: &rustc_public::mir::Place,
    ) -> Option<Sort> {
        let dest_local = destination.local;
        if self.flatten.flattened_tuple_locals.contains(&dest_local) {
            let dest_ty = destination.ty(self.body.locals()).ok()?;
            Self::translate_ty(self.resolve_body_ty(dest_ty))
        } else {
            self.resolve_destination(dest_local).map(|(_, dest_var)| dest_var.sort().clone())
        }
    }

    /// Constrain a `kani_str_*_nth` result onto either a flattened Option local
    /// or a normal datatype destination.
    pub(in crate::codegen_ay::chc) fn bind_str_nth_result(
        &mut self,
        dest_local: usize,
        result_expr: Expr,
        constraints: &mut Vec<Expr>,
        reason: &'static str,
    ) -> bool {
        if let Some(flat_constraints) =
            self.build_flattened_destination_constraints(dest_local, result_expr.clone())
        {
            constraints.extend(flat_constraints);
            return true;
        }

        if let Some((_, dest_var)) = self.resolve_destination(dest_local)
            && let Some(eq) = self.make_coerced_eq_constraint(
                &dest_var,
                result_expr,
                dest_var.sort(),
                dest_local,
                reason,
            )
        {
            constraints.push(eq);
            return true;
        }

        false
    }

    /// Part of #4161: constant-fold `kani_str_bytes_nth`/`kani_str_chars_nth`
    /// when both source `&str` and index are concrete.
    ///
    /// Fallback for when `resolve_string_backing` fails (backing array not
    /// tracked in ref_resolution tables) but the source operand traces back
    /// to a const `&str` allocation whose bytes can be read at codegen time.
    pub(in crate::codegen_ay::chc) fn try_const_fold_str_nth(
        &mut self,
        source_arg: &Operand,
        index_arg: &Operand,
        modified_locals: &HashSet<usize>,
        dest_sort: &Sort,
        is_chars: bool,
    ) -> Option<Expr> {
        let (bytes, str_len) = self.try_extract_const_str_bytes(source_arg)?;
        let index_val = self.try_extract_const_usize_operand(index_arg, modified_locals)?;

        if index_val < str_len {
            let byte = bytes[index_val];
            let payload = if is_chars {
                Expr::bitvec_const(byte as u128, 32)
            } else {
                Expr::bitvec_const(byte as u128, 8)
            };
            self.make_some_expr_for_option(payload, dest_sort)
        } else {
            self.make_none_expr_for_option(dest_sort)
        }
    }

    /// Extract concrete bytes and length from a `&str` operand.
    ///
    /// Handles both `Operand::Constant` (direct const `&str`) and
    /// `Operand::Copy/Move` (local assigned from a const `&str`).
    /// Also used by `emit_kani_assert_error_rule` to surface the user's
    /// `kani::assert` message as the property description (Kani parity).
    pub(in crate::codegen_ay::chc) fn try_extract_const_str_bytes(
        &self,
        arg: &Operand,
    ) -> Option<(Vec<u8>, usize)> {
        match arg {
            Operand::Constant(const_op) => Self::extract_str_bytes_from_const(&const_op.const_),
            Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                self.trace_local_to_const_str_bytes(place.local)
            }
            // Part of #4118: handle Copy/Move with projections (e.g. &(*_X).data)
            Operand::Copy(place) | Operand::Move(place) => self.trace_str_field_of_ref(place),
        }
    }

    /// Extract concrete str bytes from a MIR constant that is `&str`.
    fn extract_str_bytes_from_const(
        mir_const: &rustc_public::ty::MirConst,
    ) -> Option<(Vec<u8>, usize)> {
        use rustc_public::mir::alloc::GlobalAlloc;
        use rustc_public::ty::{ConstantKind, TyConstKind};

        let ty = mir_const.ty();
        let TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) = ty.kind() else { return None };
        if !matches!(pointee.kind(), TyKind::RigidTy(RigidTy::Str)) {
            return None;
        }

        let alloc = match mir_const.kind() {
            ConstantKind::Allocated(alloc) => alloc,
            ConstantKind::Ty(ty_const) => match ty_const.kind() {
                TyConstKind::Value(_ty, alloc) => alloc,
                _ => return None,
            },
            _ => return None,
        };

        // &str fat pointer: [data_ptr (8 bytes), length (8 bytes)]
        let ptr_bytes = (POINTER_WIDTH / 8) as usize;
        if alloc.bytes.len() < ptr_bytes * 2 {
            return None;
        }

        // Extract length from second word
        let mut len_arr = [0u8; 8];
        for (i, opt_byte) in alloc.bytes[ptr_bytes..ptr_bytes * 2].iter().enumerate() {
            len_arr[i] = (*opt_byte)?;
        }
        let str_len = u64::from_le_bytes(len_arr) as usize;
        if str_len > 256 {
            return None;
        }

        // Follow provenance to the actual string data allocation
        let alloc_id = alloc.provenance.ptrs.first()?.1.0;
        let GlobalAlloc::Memory(inner_alloc) = GlobalAlloc::from(alloc_id) else {
            return None;
        };
        if inner_alloc.bytes.len() < str_len {
            return None;
        }
        let bytes: Vec<u8> =
            inner_alloc.bytes.iter().take(str_len).map(|opt| opt.unwrap_or(0)).collect();
        Some((bytes, str_len))
    }

    /// Trace a local through MIR assignments and known string-passthrough
    /// Call terminators back to a const `&str` allocation.
    fn trace_local_to_const_str_bytes(&self, local: usize) -> Option<(Vec<u8>, usize)> {
        use rustc_public::mir::{Rvalue, StatementKind};

        let mut current = local;
        for _ in 0..12 {
            let mut found_source = false;
            for bb_data in &self.body.blocks {
                // Check statements: assignments, copies, casts, refs.
                for stmt in &bb_data.statements {
                    let StatementKind::Assign(lhs, rhs) = &stmt.kind else { continue };
                    if lhs.local != current {
                        continue;
                    }
                    match rhs {
                        Rvalue::Use(Operand::Constant(const_op)) => {
                            return Self::extract_str_bytes_from_const(&const_op.const_);
                        }
                        Rvalue::Use(Operand::Copy(src) | Operand::Move(src))
                        | Rvalue::Cast(_, Operand::Copy(src) | Operand::Move(src), _)
                            if src.projection.is_empty() =>
                        {
                            current = src.local;
                            found_source = true;
                            break;
                        }
                        Rvalue::Ref(_, _, ref_place) if ref_place.projection.is_empty() => {
                            current = ref_place.local;
                            found_source = true;
                            break;
                        }
                        // Part of #4118: Handle Ref to str field of custom DST.
                        Rvalue::Ref(_, _, ref_place) | Rvalue::AddressOf(_, ref_place)
                            if ref_place.projection.len() == 2
                                && matches!(ref_place.projection[0], ProjectionElem::Deref)
                                && matches!(
                                    &ref_place.projection[1],
                                    ProjectionElem::Field(_, field_ty)
                                        if matches!(field_ty.kind(), TyKind::RigidTy(RigidTy::Str))
                                ) =>
                        {
                            if let Some(result) = self.trace_str_field_of_ref(ref_place) {
                                return Some(result);
                            }
                        }
                        _ => {}
                    }
                }
                if found_source {
                    break;
                }

                // Check Call terminators for string-passthrough functions.
                if let Some(r) = self.trace_call_passthrough_str(&bb_data.terminator.kind, current)
                {
                    match r {
                        CallTraceResult::Redirect(next) => {
                            current = next;
                            found_source = true;
                        }
                        CallTraceResult::Resolved(bytes) => return Some(bytes),
                    }
                }
                if found_source {
                    break;
                }
            }
            if !found_source {
                break;
            }
        }
        None
    }

    /// Part of #4118: Trace `&(*_Y).data` where `data: str` through the parent
    /// struct to const bytes, slicing at the field offset.
    fn trace_str_field_of_ref(
        &self,
        ref_place: &rustc_public::mir::Place,
    ) -> Option<(Vec<u8>, usize)> {
        // Require [Deref, Field(_, _)] projection pattern.
        if ref_place.projection.len() < 2
            || !matches!(ref_place.projection[0], ProjectionElem::Deref)
        {
            return None;
        }
        let ProjectionElem::Field(field_idx, _) = &ref_place.projection[1] else {
            return None;
        };
        let parent_ref_ty = self.body.locals().get(ref_place.local).map(|d| d.ty)?;
        let parent_ty = match parent_ref_ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(_, inner, _))
            | TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => inner,
            _ => parent_ref_ty,
        };
        let offset = Self::field_offset_from_layout(parent_ty, *field_idx)? as usize;
        let (bytes, _) = self.trace_local_to_const_str_bytes_via_call_arg(ref_place.local)?;
        if offset < bytes.len() {
            let sliced = bytes[offset..].to_vec();
            let sliced_len = sliced.len();
            Some((sliced, sliced_len))
        } else {
            None
        }
    }

    /// Part of #4118: trace through a Call terminator's first argument to find
    /// const string bytes for the parent struct local.
    ///
    /// For custom DST constructors like `MyStr::new(&mut buf)`, the first
    /// argument (`&mut buf`) points to the String whose bytes become the
    /// struct's memory. This traces: `_parent = Call(&mut _buf)` → `_buf` →
    /// `String::from("literal")` → const bytes.
    fn trace_local_to_const_str_bytes_via_call_arg(
        &self,
        local: usize,
    ) -> Option<(Vec<u8>, usize)> {
        use rustc_public::mir::TerminatorKind;

        for bb_data in &self.body.blocks {
            let TerminatorKind::Call { args, destination, .. } = &bb_data.terminator.kind else {
                continue;
            };
            if destination.local != local {
                continue;
            }
            // Trace through the first argument.
            let Some(first_arg) = args.first() else { continue };
            let Some(arg_local) = Self::first_arg_local(first_arg) else {
                continue;
            };
            // The arg is typically &mut String. Resolve provenance to the
            // underlying String local, then trace that to const bytes.
            let resolved = self.resolve_provenance_local(arg_local);
            if let Some(result) = self.trace_local_to_const_str_bytes(resolved) {
                return Some(result);
            }
            if resolved != arg_local {
                if let Some(result) = self.trace_local_to_const_str_bytes(arg_local) {
                    return Some(result);
                }
            }
        }
        None
    }

    /// Part of #4118: check if a Call terminator is a string-passthrough
    /// (Deref::deref, ToString::to_string, String::from) and either redirect
    /// to the first arg local or resolve a direct constant.
    fn trace_call_passthrough_str(
        &self,
        term_kind: &rustc_public::mir::TerminatorKind,
        target_local: usize,
    ) -> Option<CallTraceResult> {
        use rustc_public::mir::TerminatorKind;

        let TerminatorKind::Call { func, args, destination, .. } = term_kind else {
            return None;
        };
        if destination.local != target_local || args.is_empty() {
            return None;
        }
        let callee = self.resolve_callee_path(func)?;
        if !Self::is_str_passthrough_callee(&callee) {
            return None;
        }
        if let Some(arg_local) = Self::first_arg_local(&args[0]) {
            return Some(CallTraceResult::Redirect(arg_local));
        }
        // Part of #4118: When passthrough callee's arg is a direct
        // constant (e.g. String::from("literal")), extract bytes directly.
        if let Operand::Constant(const_op) = &args[0] {
            if let Some(result) = Self::extract_str_bytes_from_const(&const_op.const_) {
                return Some(CallTraceResult::Resolved(result));
            }
        }
        None
    }

    /// Returns true for callees that preserve the `&str` byte content,
    /// allowing const-fold to trace through them.
    fn is_str_passthrough_callee(callee: &str) -> bool {
        // <String as Deref>::deref — returns &str from &String
        callee.contains("Deref>::deref")
        // <str as ToString>::to_string — copies literal bytes into String
        || callee.contains("ToString>::to_string")
        || callee.contains("ToString::to_string")
        // String::from — copies &str bytes into String
        || (callee.contains("String") && callee.contains("::from"))
    }

    /// Part of #4118: compute field offset from type layout without requiring
    /// `&mut self`. Used by the const-fold path which takes `&self`.
    fn field_offset_from_layout(ty: rustc_public::ty::Ty, field_idx: usize) -> Option<u64> {
        let layout = ty.layout().ok()?;
        if let rustc_public::abi::FieldsShape::Arbitrary { offsets } = layout.shape().fields {
            offsets.get(field_idx).map(|off| off.bytes() as u64)
        } else {
            None
        }
    }

    fn first_arg_local(arg: &Operand) -> Option<usize> {
        match arg {
            Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                Some(place.local)
            }
            _ => None,
        }
    }

    /// Try to extract a concrete `usize` value from an operand.
    fn try_extract_const_usize_operand(
        &mut self,
        arg: &Operand,
        modified_locals: &HashSet<usize>,
    ) -> Option<usize> {
        let expr = self.translate_operand_with_modified(arg, modified_locals)?;
        if let ay_bindings::ExprValue::BitVecConst { value, .. } = expr.value() {
            u64::try_from(value).ok().map(|v| v as usize)
        } else {
            None
        }
    }
}
