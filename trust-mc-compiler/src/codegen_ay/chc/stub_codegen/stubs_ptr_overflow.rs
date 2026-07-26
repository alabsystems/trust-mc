// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CHC pointer offset overflow checks.
//!
//! Emits error rules for pointer arithmetic overflow when
//! `--extra-pointer-checks` is enabled. Part of #3176.
//!
//! Extracted from stubs_util_intrinsics.rs per file size limit.

use std::collections::HashSet;

use crate::codegen_ay::shared::IntoOption;
use ay_bindings::Expr;
use rustc_public::CrateDef;
use rustc_public::mir::Operand;
use rustc_public::ty::{GenericArgKind, RigidTy, TyKind};
use tracing::debug;

use super::ChcCtx;
use super::pointer_step::step_split_pointer;
use super::types::{POINTER_WIDTH, SignExtension, coerce_bitvec_width_safe};

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Emit CHC error rules for pointer offset overflow checks (#3176).
    ///
    /// Mirrors the BMC `emit_offset_overflow_check` logic:
    /// 1. offset_value_overflow: count exceeds isize bounds
    /// 2. offset_bytes_overflow: count * sizeof(T) overflows isize
    /// 3. offset_result_overflow: ptr + byte_offset wraps around address space
    ///
    /// Only called when `extra_pointer_checks` is enabled.
    pub(in crate::codegen_ay::chc) fn emit_ptr_offset_overflow_error_rules(
        &mut self,
        from_app: &trust_mc_core::chc::RelationApp,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
        stmt_constraints: &[Expr],
        target: usize,
    ) {
        if args.len() < 2 {
            return;
        }

        // Re-translate ptr and count (cheap BV expressions).
        let Some(ptr) = self.translate_operand_with_modified(&args[0], modified_locals) else {
            return;
        };
        let ptr = coerce_bitvec_width_safe(ptr, POINTER_WIDTH, SignExtension::ZeroExtend);
        let Some(count) = self.translate_operand_with_modified(&args[1], modified_locals) else {
            return;
        };
        let count = coerce_bitvec_width_safe(count, POINTER_WIDTH, SignExtension::ZeroExtend);

        // Resolve pointee size (same logic as translate_ptr_add_call).
        let elem_size =
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
                _other => None,
            });
        let Some(elem_size) = elem_size else {
            return;
        };

        let isize_max = Expr::bitvec_const((1i128 << (POINTER_WIDTH - 1)) - 1, POINTER_WIDTH);
        let isize_min = Expr::bitvec_const(-(1i128 << (POINTER_WIDTH - 1)), POINTER_WIDTH);
        let zero = Expr::bitvec_const(0u128, POINTER_WIDTH);

        // Check 1: offset value within isize bounds.
        // Violation: count > isize::MAX or count < isize::MIN.
        let count_too_large = count.clone().bvsgt(isize_max);
        let count_too_small = count.clone().bvslt(isize_min);
        let value_overflow = count_too_large.or(count_too_small);
        self.emit_error_rule_for_condition(
            from_app,
            value_overflow.not(),
            stmt_constraints,
            target,
        );
        debug!("CHC: emitted offset_value_overflow error rule (#3176)");

        // Check 4 (Part of #3176): base pointer has valid allocation provenance.
        // This must run before the ZST fast-path return so dangling-pointer
        // arithmetic on zero-sized pointees still fails under extra checks.
        if !self.int_lift {
            if let Some((obj_id, _offset)) = self.split_pointer(&ptr) {
                let obj_valid = self.current_obj_valid_array();
                // Part of #3221: track metadata access for pruning correctness.
                self.mark_heap_metadata_read();
                let is_valid = obj_valid.select(obj_id);
                self.emit_error_rule_for_condition(from_app, is_valid, stmt_constraints, target);
                debug!("CHC: emitted provenance_valid error rule (#3176)");
            }
        }

        // For ZST (size 0), no byte offset, so no further checks needed.
        if elem_size == 0 {
            return;
        }

        // Check 2: byte offset overflow (count * sizeof(T) overflows).
        if elem_size > 1 {
            let size_expr = Expr::bitvec_const(elem_size as u128, POINTER_WIDTH);
            let offset = count.clone().bvmul(size_expr.clone());
            let div_back = offset.bvsdiv(size_expr);
            let mul_overflow = div_back.ne(count.clone());
            self.emit_error_rule_for_condition(
                from_app,
                mul_overflow.not(),
                stmt_constraints,
                target,
            );
            debug!("CHC: emitted offset_bytes_overflow error rule (#3176)");
        }

        // Check 3: result pointer overflow (ptr + byte_offset wraps around).
        // Part of #3921: use split-pointer step for same-object preservation.
        let byte_offset = if elem_size > 1 {
            count.clone().bvmul(Expr::bitvec_const(elem_size as u128, POINTER_WIDTH))
        } else {
            count.clone()
        };
        let step = step_split_pointer(ptr.clone(), byte_offset);
        let result_ptr = step.result;

        // If offset is positive and result < ptr, wrapped forward.
        let positive_offset = count.clone().bvsge(zero.clone());
        let wrapped_forward = positive_offset.and(result_ptr.clone().bvult(ptr.clone()));

        // If offset is negative and result > ptr, wrapped backward.
        let negative_offset = count.bvslt(zero);
        let wrapped_backward = negative_offset.and(result_ptr.bvugt(ptr));

        let ptr_overflow = wrapped_forward.or(wrapped_backward);
        self.emit_error_rule_for_condition(from_app, ptr_overflow.not(), stmt_constraints, target);
        debug!("CHC: emitted offset_result_overflow error rule (#3176)");

        // When split-pointer recomposition was used, also enforce same-object.
        if let Some(same_object_ok) = step.same_object_ok {
            self.emit_error_rule_for_condition(from_app, same_object_ok, stmt_constraints, target);
            debug!("CHC: emitted split_pointer_same_object error rule (#3921)");
        }
    }
}
