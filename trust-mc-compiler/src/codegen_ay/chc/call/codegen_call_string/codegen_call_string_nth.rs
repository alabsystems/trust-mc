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
    /// Bytes: `ite(index < len, Some(byte), None)`. Chars: the `index`-th
    /// char is the `index`-th byte only while every byte up to it is ASCII;
    /// the model read the byte whatever it was, so `"h\u{e9}llo".chars().nth(1)`
    /// was `Some('\u{c3}')`, proving value assertions Kani fails and
    /// certifying the true values as Genuine failures (walker fail-closed
    /// repair round 5, `str_chars_nth_multibyte_dual.rs`). The byte is used
    /// under an ASCII guard over the bytes up to a constant index (or every
    /// byte of a constant-length string), and a fresh value, a recorded
    /// sound havoc, stands for the char otherwise. `None` if the Option sort
    /// cannot be decomposed.
    pub(in crate::codegen_ay::chc) fn try_build_str_nth_result_expr(
        &mut self,
        backing: &StringBacking,
        index_expr: Expr,
        dest_sort: &Sort,
        is_chars: bool,
    ) -> Option<Expr> {
        let in_bounds = index_expr.clone().bvult(backing.len.clone());
        let byte_val =
            backing.data.clone().select(backing.offset.clone().bvadd(index_expr.clone()));
        let none_expr = self.make_none_expr_for_option(dest_sort)?;
        if !is_chars {
            let some_expr = self.make_some_expr_for_option(byte_val, dest_sort)?;
            return Some(Expr::ite(in_bounds, some_expr, none_expr));
        }
        // Zero-extend BV8 → BV32 for char representation
        let some_expr = self.make_some_expr_for_option(byte_val.zero_extend(24), dest_sort)?;
        let multibyte = self.fresh_str_chars_nth_value(dest_sort.clone());
        let in_bounds_value = match Self::str_ascii_prefix_guard(backing, &index_expr) {
            Some(ascii) => Expr::ite(ascii, some_expr, multibyte),
            None => multibyte,
        };
        Some(Expr::ite(in_bounds, in_bounds_value, none_expr))
    }

    /// The bytes of `backing` a char-by-char walk to `index` reads are all
    /// ASCII: every byte up to a constant `index`, or every byte of a string
    /// of constant length. `None` past `MAX_ASCII_GUARD_BYTES`, or when
    /// neither is constant.
    fn str_ascii_prefix_guard(backing: &StringBacking, index_expr: &Expr) -> Option<Expr> {
        const MAX_ASCII_GUARD_BYTES: u64 = 256;
        let count = match Self::try_eval_const_bv(index_expr) {
            Some(index) => index.checked_add(1)?,
            None => Self::try_eval_const_bv(&backing.len)?,
        };
        if count > MAX_ASCII_GUARD_BYTES {
            return None;
        }
        let byte_width = backing.data.sort().array_sort()?.element_sort.bitvec_width()?;
        let mut guard = Expr::bool_const(true);
        for j in 0..count {
            let byte = backing
                .data
                .clone()
                .select(backing.offset.clone().bvadd(Expr::bitvec_const(j, POINTER_WIDTH)));
            guard = guard.and(byte.bvult(Expr::bitvec_const(0x80u64, byte_width)));
        }
        Some(guard)
    }

    /// A fresh `Option<char>` for a `chars().nth(..)` whose bytes may hold a
    /// multi-byte char: universally quantified, so it admits the real value,
    /// and recorded with itself as the freed variable, so a counterexample
    /// that reads it is never certified Genuine.
    fn fresh_str_chars_nth_value(&mut self, sort: Sort) -> Expr {
        use super::super::super::codegen_ctx::globals::chc_fresh_name;
        use crate::codegen_ay::chc::codegen_ctx::{Havoc, sound_havoc};
        let name = chc_fresh_name("__str_chars_nth_multibyte");
        Havoc::mint(self, sound_havoc::STR_CHARS_NTH_MULTIBYTE_OVERAPPROX, name, sort)
    }

    /// `kani_str_chars_nth` over the known bytes of a `&str`: the `index`-th
    /// char of their UTF-8 decoding, exactly, as a chain over the char
    /// positions when `index` is symbolic. `None` when the bytes are not
    /// UTF-8 or the Option sort cannot be decomposed.
    pub(in crate::codegen_ay::chc) fn str_chars_nth_from_bytes(
        &self,
        bytes: &[u8],
        index_expr: &Expr,
        dest_sort: &Sort,
    ) -> Option<Expr> {
        let chars: Vec<char> = std::str::from_utf8(bytes).ok()?.chars().collect();
        let some_of = |c: char| {
            self.make_some_expr_for_option(Expr::bitvec_const(u32::from(c), 32), dest_sort)
        };
        if let Some(index) = Self::try_eval_const_bv(index_expr) {
            return match usize::try_from(index).ok().and_then(|index| chars.get(index)) {
                Some(&c) => some_of(c),
                None => self.make_none_expr_for_option(dest_sort),
            };
        }
        let width = index_expr.sort().bitvec_width()?;
        let mut result = self.make_none_expr_for_option(dest_sort)?;
        for (position, &c) in chars.iter().enumerate().rev() {
            let at = index_expr.clone().eq(Expr::bitvec_const(position as u64, width));
            result = Expr::ite(at, some_of(c)?, result);
        }
        Some(result)
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
        if is_chars {
            // The UTF-8 decoding, not the byte (`str_chars_nth_from_bytes`).
            let index = Expr::bitvec_const(index_val as u64, POINTER_WIDTH);
            return self.str_chars_nth_from_bytes(&bytes[..str_len], &index, dest_sort);
        }

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
            Operand::Constant(const_op) => self.extract_str_bytes_from_const(&const_op.const_),
            Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                self.trace_local_to_const_str_bytes(place.local)
            }
            // Part of #4118: handle Copy/Move with projections (e.g. &(*_X).data)
            Operand::Copy(place) | Operand::Move(place) => self.trace_str_field_of_ref(place),
            #[cfg(trust_toolchain)]
            Operand::RuntimeChecks(_) => None,
        }
    }

    /// Extract concrete str bytes from a MIR constant that is `&str`: the
    /// pointee WINDOW its pointer names (`const_pointer::fixed_pointee`) — at
    /// the pointer's offset, for the length its metadata word carries — every
    /// byte initialized data. It read the target from byte 0 (and filled
    /// uninitialized bytes with 0): `T = "hello".split_at(2).1` iterated as
    /// `"hel"`, and `T.chars().nth(0) == Some('h')` PROVED.
    fn extract_str_bytes_from_const(
        &self,
        mir_const: &rustc_public::ty::MirConst,
    ) -> Option<(Vec<u8>, usize)> {
        use crate::codegen_ay::shared::const_pointer::{self, ConstRead};

        let ty = mir_const.ty();
        let TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) = ty.kind() else { return None };
        if !matches!(pointee.kind(), TyKind::RigidTy(RigidTy::Str)) {
            return None;
        }
        let bytes = const_pointer::const_bytes(mir_const)?;
        let (r, window) = const_pointer::fixed_pointee(self.tcx, &bytes, 0, pointee)?;
        let str_len = usize::try_from(r.metadata?).ok()?;
        if str_len > 256 || window.len() != str_len {
            return None;
        }
        Some((window.read_data_bytes(0, str_len)?, str_len))
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
                        Rvalue::Use(Operand::Constant(const_op), ..) => {
                            return self.extract_str_bytes_from_const(&const_op.const_);
                        }
                        Rvalue::Use(Operand::Copy(src) | Operand::Move(src), ..)
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
            if let Some(result) = self.extract_str_bytes_from_const(&const_op.const_) {
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
