// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Extra-pointer-check helpers for RawVec/Layout dangling constructors.

use ay_bindings::Expr;

use crate::codegen_ay::names::{self, struct_sort};
use crate::codegen_ay::provenance::{Loc, Val};
use crate::codegen_ay::types::{POINTER_WIDTH, ptr_sort};

use super::super::ChcCtx;
use super::super::chc_call_context::ChcCallContext;
use super::super::codegen_call_coerce::CallCoerce;
use super::super::codegen_ctx::globals::{chc_fresh_name, declare_pending_var};
use super::super::codegen_expr_heap;
use super::super::codegen_rules::CodegenRules;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    pub(in crate::codegen_ay::chc) fn emit_rawvec_new_in_extra_checks(
        &mut self,
        cx: &ChcCallContext<'_>,
    ) -> bool {
        if self.int_lift {
            return false;
        }
        let dest_local = cx.destination.local;
        let Some((_, dest_var)) = self.resolve_destination(dest_local) else {
            return false;
        };
        let Some(sort_name) = dest_var.sort().datatype_name() else {
            return false;
        };
        if !sort_name.contains("RawVec") {
            return false;
        }

        let zero = Expr::bitvec_const(0u64, POINTER_WIDTH);
        // Freshly declared RawVec allocation base: an ADDRESS by construction.
        let ptr = Loc::of_address(declare_pending_var(chc_fresh_name("rawvec_ptr"), ptr_sort()));
        let rawvec_sort = struct_sort("RawVec", names::rawvec_fields());
        let rawvec = Expr::datatype_constructor(
            "RawVec",
            "RawVec_mk",
            vec![ptr.as_expr().clone(), zero.clone()],
            rawvec_sort,
        );

        let mut extra_constraints = vec![dest_var.eq(rawvec), ptr.as_expr().clone().bvugt(zero)];
        if let Some((obj_id, _offset)) = self.split_pointer(ptr.as_expr()) {
            let current_valid = self.current_obj_valid_array();
            let invalidated = current_valid.store(obj_id, Expr::bool_const(false));
            extra_constraints.push(codegen_expr_heap::obj_valid_out().eq(invalidated));
            self.mark_heap_metadata_modified();
        }

        let new_output_args = self.build_output_args(cx.modified_locals, &[dest_local]);
        self.emit_goto_rule_extra(
            cx.from_app,
            cx.target,
            &new_output_args,
            cx.stmt_constraints,
            extra_constraints,
        );
        true
    }

    pub(in crate::codegen_ay::chc) fn emit_layout_dangling_extra_checks(
        &mut self,
        cx: &ChcCallContext<'_>,
    ) -> bool {
        if self.int_lift {
            return false;
        }
        let dest_local = cx.destination.local;
        let Some((_, dest_var)) = self.resolve_destination(dest_local) else {
            return false;
        };
        // Well-formedness of the `dest_var == dangling_ptr` constraint emitted
        // below: the destination slot must be as wide as the address it
        // receives. NOT an "is the destination a pointer?" oracle.
        if dest_var.sort().bitvec_width() != Some(POINTER_WIDTH) {
            return false;
        }

        // The ALIGNMENT is a value: a `usize` count read out of the `Layout`.
        let align = Val::of_value(
            cx.args
                .first()
                .and_then(|arg| self.resolve_layout_operand_expr(arg, cx.modified_locals))
                .and_then(Self::extract_layout_size_align)
                .map(|(_, align)| align.extract(63, 0))
                .unwrap_or_else(|| Expr::bitvec_const(8u64, POINTER_WIDTH)),
        );
        let zero = Expr::bitvec_const(0u64, POINTER_WIDTH);
        // Address-vs-value (wave 1): `Layout::dangling()` is Rust's
        // `align as *mut T` — a genuine int-to-pointer with exposed provenance,
        // the one operation that legitimately turns a value into an address
        // (see the conversion queue, §4 item 2: this is the call site that will
        // become `Loc::from_exposed`). The old code laundered exactly this
        // crossing through a width test — `if align is 64 bits wide, it may be
        // used as the pointer` — with a dead `else` arm: `align` comes from
        // `extract_layout_size_align`, which only ever yields `extract(63, 0)`
        // of a bv128 (or the bv64 literal 8), so the test was vacuously true and
        // the fallback unreachable. Guard DELETED; the crossing is now explicit.
        let dangling_ptr = Loc::of_address(align.into_expr());

        let mut extra_constraints = vec![
            dest_var.eq(dangling_ptr.as_expr().clone()),
            dangling_ptr.as_expr().clone().bvugt(zero),
        ];
        if let Some((obj_id, _offset)) = self.split_pointer(dangling_ptr.as_expr()) {
            let current_valid = self.current_obj_valid_array();
            let invalidated = current_valid.store(obj_id, Expr::bool_const(false));
            extra_constraints.push(codegen_expr_heap::obj_valid_out().eq(invalidated));
            self.mark_heap_metadata_modified();
        }

        let new_output_args = self.build_output_args(cx.modified_locals, &[dest_local]);
        self.emit_goto_rule_extra(
            cx.from_app,
            cx.target,
            &new_output_args,
            cx.stmt_constraints,
            extra_constraints,
        );
        true
    }
}
