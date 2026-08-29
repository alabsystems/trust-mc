// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Pointer arithmetic stubs: ptr.add, ptr.sub, ptr.wrapping_*,
//! ptr.write, ptr.read.
//!
//! Extracted from `stubs_util_intrinsics.rs` — Part of #4206.

use std::collections::HashSet;

use ay_bindings::Expr;
use rustc_public::mir::Operand;
use rustc_public::ty::{GenericArgKind, RigidTy, TyKind};
use tracing::{debug, warn};

use crate::codegen_ay::shared::IntoOption;
use rustc_public::CrateDef;

use super::ChcCtx;
use super::chc_call_context::ChcCallContext;
use super::codegen_call_coerce::CallCoerce;
use super::codegen_rules::CodegenRules;
use super::pointer_step::{step_split_pointer, step_split_pointer_sub, step_wrapping_pointer};
use super::stubs::StubKind;
use super::types::{POINTER_WIDTH, SignExtension, coerce_bitvec_width_safe};

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Translate ptr.add(count) -> *mut T: compute ptr + count * sizeof(T).
    ///
    /// Uses the pointee type from the first argument (self pointer) to determine
    /// element size. Returns the offset pointer as a bv64 expression.
    /// Part of #1836: CHC pointer arithmetic for heap data flow.
    pub(in crate::codegen_ay::chc) fn translate_ptr_add_call(
        &mut self,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        if args.len() < 2 {
            return None;
        }

        // Get pointer (self)
        let ptr = match &args[0] {
            Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => self
                .known_stack_addr_expr(place.local)
                .or_else(|| self.translate_operand_with_modified(&args[0], modified_locals))?,
            _ => self.translate_operand_with_modified(&args[0], modified_locals)?,
        };
        let ptr = coerce_bitvec_width_safe(ptr, POINTER_WIDTH, SignExtension::ZeroExtend);

        // Get count. Part of #72: when the count rides host relation state
        // (e.g. `usize::MAX / (size_of * 4)` computed in prior statements),
        // recover the exact literal via the FAIL-CLOSED unique-definition walk
        // so the split-pointer constant fold can detect out-of-lane wraps.
        let count = self.translate_operand_with_modified(&args[1], modified_locals)?;
        let count = if trust_mc_core::chc_const_prop::eval::try_eval_to_const(&count).is_none() {
            self.unique_def_const_operand(&args[1], 32).unwrap_or(count)
        } else {
            count
        };
        let count = coerce_bitvec_width_safe(count, POINTER_WIDTH, SignExtension::ZeroExtend);

        // Get sizeof(T) from the pointer's pointee type.
        // Supports raw/ref pointers and transparent wrappers (NonNull/Unique).
        let elem_size_opt =
            args[0].ty(self.body.locals()).into_option().and_then(|ty| match ty.kind() {
                TyKind::RigidTy(RigidTy::RawPtr(pointee, _))
                | TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) => self.get_type_size(pointee),
                TyKind::RigidTy(RigidTy::Adt(def, generic_args))
                    if def.trimmed_name() == "NonNull" || def.trimmed_name() == "Unique" =>
                {
                    generic_args.0.iter().find_map(|arg| {
                        if let GenericArgKind::Type(pointee) = arg {
                            self.get_type_size(*pointee)
                        } else {
                            None
                        }
                    })
                }
                _other => None, // external enum: TyKind
            });
        let elem_size = if let Some(s) = elem_size_opt {
            s
        } else {
            // Fail closed: unknown pointee size → return None so the assignment
            // is unconstrained rather than encoding unsound byte-scaled arithmetic (#2315).
            warn!("CHC: ptr.add pointee size unknown, dropping translation");
            self.record_sound_fallback_reason("ptr_add_pointee_size_unknown");
            return None;
        };

        // Compute offset in bytes: count * sizeof(T)
        let elem_size_expr = Expr::bitvec_const(elem_size as u128, POINTER_WIDTH);
        let offset_bytes = count.bvmul(elem_size_expr);

        // Part of #3921: split-pointer step preserves obj_id.
        let new_ptr = step_split_pointer(ptr, offset_bytes).result;

        debug!(elem_size, "CHC: translate_ptr_add_call - ptr + count * sizeof(T)");

        Some(new_ptr)
    }

    /// Translate ptr.sub(count) -> *mut T: compute ptr - count * sizeof(T).
    ///
    /// Mirror of `translate_ptr_add_call` for subtraction.
    /// Part of #3518: PtrWrappingSub needs element-sized steps, not byte steps.
    pub(in crate::codegen_ay::chc) fn translate_ptr_sub_call(
        &mut self,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        if args.len() < 2 {
            return None;
        }

        let ptr = self.translate_operand_with_modified(&args[0], modified_locals)?;
        let ptr = coerce_bitvec_width_safe(ptr, POINTER_WIDTH, SignExtension::ZeroExtend);

        let count = self.translate_operand_with_modified(&args[1], modified_locals)?;
        let count = coerce_bitvec_width_safe(count, POINTER_WIDTH, SignExtension::ZeroExtend);

        // Same pointee size extraction as translate_ptr_add_call.
        let elem_size_opt =
            args[0].ty(self.body.locals()).into_option().and_then(|ty| match ty.kind() {
                TyKind::RigidTy(RigidTy::RawPtr(pointee, _))
                | TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) => self.get_type_size(pointee),
                TyKind::RigidTy(RigidTy::Adt(def, generic_args))
                    if def.trimmed_name() == "NonNull" || def.trimmed_name() == "Unique" =>
                {
                    generic_args.0.iter().find_map(|arg| {
                        if let GenericArgKind::Type(pointee) = arg {
                            self.get_type_size(*pointee)
                        } else {
                            None
                        }
                    })
                }
                _other => None, // external enum: TyKind
            });
        let elem_size = if let Some(s) = elem_size_opt {
            s
        } else {
            warn!("CHC: ptr.sub pointee size unknown, dropping translation");
            self.record_sound_fallback_reason("ptr_sub_pointee_size_unknown");
            return None;
        };

        let elem_size_expr = Expr::bitvec_const(elem_size as u128, POINTER_WIDTH);
        let offset_bytes = count.bvmul(elem_size_expr);
        // Part of #3921: split-pointer step preserves obj_id.
        let new_ptr = step_split_pointer_sub(ptr, offset_bytes).result;

        debug!(elem_size, "CHC: translate_ptr_sub_call - ptr - count * sizeof(T)");

        Some(new_ptr)
    }

    /// Emit transition for wrapping element-sized pointer arithmetic
    /// (`wrapping_add`, `wrapping_sub`, `wrapping_offset`).
    ///
    /// Uses `sizeof(T)` scaling via `translate_ptr_add_call` / `translate_ptr_sub_call`.
    /// Part of #3518: split from byte-level `emit_ptr_wrapping_byte_transition`.
    pub(in crate::codegen_ay::chc) fn emit_ptr_wrapping_element_transition(
        &mut self,
        cx: &ChcCallContext<'_>,
    ) {
        let dest_local = cx.destination.local;
        let is_sub = cx.stub == StubKind::PtrWrappingSub;

        let result_opt = if is_sub {
            self.translate_ptr_sub_call(cx.args, cx.modified_locals)
        } else {
            self.translate_ptr_add_call(cx.args, cx.modified_locals)
        };

        let Some(result_expr) = result_opt else {
            warn!(
                fn_name = %self.fn_name,
                "CHC: wrapping element pointer translation failed; emitting unconstrained transition with fallback metadata"
            );
            self.record_sound_fallback_reason("wrapping_elem_ptr_translation_failed");
            let new_output_args = self.build_output_args(cx.modified_locals, &[dest_local]);
            self.emit_goto_rule(cx.from_app, cx.target, &new_output_args, cx.stmt_constraints);
            return;
        };

        let Some((_, dest_var)) = self.resolve_destination(dest_local) else {
            warn!(
                fn_name = %self.fn_name,
                "CHC: wrapping element pointer missing destination output state; emitting unconstrained transition with fallback metadata"
            );
            self.record_sound_fallback_reason("wrapping_elem_ptr_missing_dest");
            let new_output_args = self.build_output_args(cx.modified_locals, &[dest_local]);
            self.emit_goto_rule(cx.from_app, cx.target, &new_output_args, cx.stmt_constraints);
            return;
        };

        if let Some(eq) = self.make_coerced_eq_constraint(
            &dest_var,
            result_expr,
            dest_var.sort(),
            dest_local,
            "emit_ptr_wrapping_element_transition",
        ) {
            let new_output_args = self.build_output_args(cx.modified_locals, &[dest_local]);
            self.emit_goto_rule_extra(
                cx.from_app,
                cx.target,
                &new_output_args,
                cx.stmt_constraints,
                [eq],
            );
        } else {
            warn!(
                fn_name = %self.fn_name,
                "CHC: wrapping element pointer coercion failed; emitting unconstrained transition with fallback metadata"
            );
            self.record_sound_fallback_reason("wrapping_elem_ptr_coercion_failed");
            let new_output_args = self.build_output_args(cx.modified_locals, &[dest_local]);
            self.emit_goto_rule(cx.from_app, cx.target, &new_output_args, cx.stmt_constraints);
        }
    }

    /// Translate wrapping byte pointer arithmetic: `ptr +/- byte_count`.
    pub(in crate::codegen_ay::chc) fn translate_ptr_wrapping_byte_call(
        &mut self,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
        is_sub: bool,
        signed_count: bool,
    ) -> Option<Expr> {
        if args.len() < 2 {
            return None;
        }

        let ptr = self.translate_operand_with_modified(&args[0], modified_locals)?;
        let ptr = coerce_bitvec_width_safe(ptr, POINTER_WIDTH, SignExtension::ZeroExtend);

        let byte_count = self.translate_operand_with_modified(&args[1], modified_locals)?;
        // `wrapping_byte_offset` takes an ISIZE. Zero-extending a narrow
        // negative count turns a backwards step into a huge forwards one, so
        // the extension must follow the count's SIGNEDNESS, not the opcode.
        // `wrapping_byte_add`/`wrapping_byte_sub` take a usize and keep
        // zero-extension.
        let count_ext =
            if signed_count { SignExtension::SignExtend } else { SignExtension::ZeroExtend };
        let byte_count = coerce_bitvec_width_safe(byte_count, POINTER_WIDTH, count_ext);

        // Wrapping pointer arithmetic is DEFINED out of bounds and wraps the
        // whole address space, so the step must be exact mod 2^64. The plain
        // split step truncates the offset to the low 32-bit lane and drops the
        // carry out of it, which collapses every nonzero multiple of 2^32 to a
        // no-op — `p.wrapping_byte_offset(1 << 32) == p` became derivable, and
        // the encoder statically discharged that false assertion. An OOB deref
        // of the result is still caught by heap_access_checks.
        Some(step_wrapping_pointer(ptr, byte_count, is_sub))
    }

    /// Emit transition for wrapping byte pointer arithmetic (`wrapping_byte_add/sub/offset`).
    /// Part of #3518: PtrWrappingSub no longer routes here — only byte variants.
    pub(in crate::codegen_ay::chc) fn emit_ptr_wrapping_byte_transition(
        &mut self,
        cx: &ChcCallContext<'_>,
    ) {
        let dest_local = cx.destination.local;
        let is_sub = cx.stub == StubKind::PtrWrappingByteSub;

        let Some(result_expr) = self.translate_ptr_wrapping_byte_call(
            cx.args,
            cx.modified_locals,
            is_sub,
            cx.stub == StubKind::PtrWrappingByteOffset,
        ) else {
            warn!(
                fn_name = %self.fn_name,
                "CHC: wrapping_byte pointer translation failed; emitting unconstrained transition with fallback metadata"
            );
            self.record_sound_fallback_reason("wrapping_byte_ptr_translation_failed");
            let new_output_args = self.build_output_args(cx.modified_locals, &[dest_local]);
            self.emit_goto_rule(cx.from_app, cx.target, &new_output_args, cx.stmt_constraints);
            return;
        };

        let Some((_, dest_var)) = self.resolve_destination(dest_local) else {
            warn!(
                fn_name = %self.fn_name,
                "CHC: wrapping_byte pointer missing destination output state; emitting unconstrained transition with fallback metadata"
            );
            self.record_sound_fallback_reason("wrapping_byte_ptr_missing_dest");
            let new_output_args = self.build_output_args(cx.modified_locals, &[dest_local]);
            self.emit_goto_rule(cx.from_app, cx.target, &new_output_args, cx.stmt_constraints);
            return;
        };

        if let Some(eq) = self.make_coerced_eq_constraint(
            &dest_var,
            result_expr,
            dest_var.sort(),
            dest_local,
            "emit_ptr_wrapping_byte_transition",
        ) {
            let new_output_args = self.build_output_args(cx.modified_locals, &[dest_local]);
            self.emit_goto_rule_extra(
                cx.from_app,
                cx.target,
                &new_output_args,
                cx.stmt_constraints,
                [eq],
            );
        } else {
            warn!(
                fn_name = %self.fn_name,
                "CHC: wrapping_byte pointer coercion failed; emitting unconstrained transition with fallback metadata"
            );
            self.record_sound_fallback_reason("wrapping_byte_ptr_coercion_failed");
            let new_output_args = self.build_output_args(cx.modified_locals, &[dest_local]);
            self.emit_goto_rule(cx.from_app, cx.target, &new_output_args, cx.stmt_constraints);
        }
    }

    /// Translate ptr.write(value): store value to memory at ptr address.
    ///
    /// Calls `build_memory_store(loc, value, pointee_ty)` which handles
    /// type-indexed arrays, region arrays, and store chain accumulation.
    /// Part of #1836: CHC memory write for heap data flow.
    pub(in crate::codegen_ay::chc) fn translate_ptr_write_call(
        &mut self,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
    ) -> bool {
        if args.len() < 2 {
            return false;
        }

        // Get pointer (self). Recover a concrete heap base address when the raw
        // pointer local is known to target a specific allocation so call-side
        // ptr.write uses the same address family as later ptr.read/realloc paths.
        let ptr = match &args[0] {
            Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => self
                .trace_deref_store_alloc_id(place.local)
                .map(|obj_id| {
                    Expr::bitvec_const(obj_id as i128, 32).concat(Expr::bitvec_const(0, 32))
                })
                .or_else(|| self.translate_operand_with_modified(&args[0], modified_locals)),
            _ => self.translate_operand_with_modified(&args[0], modified_locals),
        };
        let ptr_ty = args[0].ty(self.body.locals()).into_option();
        // ESTABLISH the address instead of coercing into one.
        //
        // This used to be `coerce_bitvec_width_safe(.., ZeroExtend)` followed by
        // `Loc::of_address`, i.e. a tag on a WIDENED term. The MIR type says
        // args[0] is a raw pointer, but the coercion is total: it zero-extends a
        // narrow datum and passes a non-bitvec sort straight through, so the tag
        // asserted address-ness of terms that are demonstrably values.
        // `normalize_deref_address_expr` is the encoder's `Loc` producer for
        // exactly this question — it peels a wrapper datatype, refuses
        // sub-pointer-width terms and refuses `is_value_widened_into_address`
        // shapes — and a `None` here fails closed into `record_fallback()`
        // (DEMOTED) at the call site.
        let ptr = match (ptr, ptr_ty) {
            (Some(p), Some(ty)) => match self.normalize_deref_address_expr(p, ty) {
                Some(loc) => loc,
                None => return false,
            },
            _ => return false,
        };

        // Get value to write
        let value = match self.translate_operand_with_modified(&args[1], modified_locals) {
            Some(v) => v,
            None => return false,
        };

        // Get pointee type from the pointer argument
        let pointee_ty = ptr_ty.and_then(Self::deref_pointee_ty);

        if let Some(pointee_ty) = pointee_ty {
            // Part of #3108: Mirror array elements to flat memory for ptr.write([T; N]).
            let mut mirror_constraints = Vec::new();
            self.mirror_array_elements_to_flat_memory(
                &value,
                pointee_ty,
                ptr.as_expr(),
                &mut mirror_constraints,
            );
            self.heap_state.pending_updates.extend(mirror_constraints);
            // The `Loc` was minted by `normalize_deref_address_expr` above, so
            // this is a thread-through, not a re-tag.
            self.build_memory_store(ptr, value, pointee_ty);
            debug!("CHC: translate_ptr_write_call - stored value via build_memory_store");
            true
        } else {
            debug!("CHC: translate_ptr_write_call - could not resolve pointee type");
            false
        }
    }

    /// Translate ptr.read() / std::ptr::read(ptr) -> T: load value from memory at ptr address.
    ///
    /// Calls `load_from_memory(addr, pointee_ty)` which handles type-indexed arrays,
    /// region arrays, and store chain integration.
    /// Part of #1836: CHC memory read for heap data flow.
    pub(in crate::codegen_ay::chc) fn translate_ptr_read_call(
        &mut self,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        if args.is_empty() {
            return None;
        }

        // Get pointer argument. When the raw pointer local is known to refer to
        // a specific heap allocation, recover the constant base address so the
        // mem-track load uses the same address family as the corresponding store.
        let ptr = match &args[0] {
            Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => self
                .trace_deref_store_alloc_id(place.local)
                .map(|obj_id| {
                    Expr::bitvec_const(obj_id as i128, 32).concat(Expr::bitvec_const(0, 32))
                })
                .or_else(|| self.translate_operand_with_modified(&args[0], modified_locals)),
            _ => self.translate_operand_with_modified(&args[0], modified_locals),
        }?;
        let ptr_ty = args[0].ty(self.body.locals()).into_option()?;

        // Get pointee type from the pointer argument
        let pointee_ty = Self::deref_pointee_ty(ptr_ty)?;

        // ESTABLISH the address rather than coerce into one. `deref_pointee_ty`
        // just succeeded, so the MIR type of args[0] is a raw pointer — but the
        // old `coerce_bitvec_width_safe(.., ZeroExtend)` here would zero-extend a
        // narrow datum or pass a datatype straight through, and the tag then
        // asserted address-ness of the laundered result (the comment on the old
        // line said as much). `normalize_deref_address_expr` peels a wrapper
        // datatype and refuses both fabrications; `None` fails closed to the
        // caller's fallback lane.
        let ptr = self.normalize_deref_address_expr(ptr, ptr_ty)?;
        let result = self.load_from_memory(ptr, pointee_ty)?.into_expr();

        debug!("CHC: translate_ptr_read_call - loaded value via load_from_memory");

        Some(result)
    }
}
