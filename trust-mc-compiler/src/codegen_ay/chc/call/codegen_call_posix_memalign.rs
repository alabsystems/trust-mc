// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Direct `libc::posix_memalign` call handling for CHC.
//!
//! The generic foreign-call fallback is correct by default, but this libc API
//! has a concrete contract in the Kani regression suite. Model the direct FFI
//! shape before the generic error() path:
//! - invalid alignment -> `EINVAL`, out-pointer unchanged
//! - valid alignment -> `0`, out-pointer = fresh heap allocation
//!
//! Part of #3736.

use crate::codegen_ay::chc::codegen_ctx::types::AllocCallResult;
use crate::codegen_ay::stubs::StubKind;
use crate::codegen_ay::types::POINTER_WIDTH;
use ay_bindings::{Expr, Sort};

use super::super::ChcCtx;
use super::super::chc_call_context::DispatchCallContext;
use super::super::codegen_call_atomic::resolve_ptr_target_local;
use super::super::codegen_call_coerce::CallCoerce;
use super::super::codegen_rules::CodegenRules;

pub(in crate::codegen_ay::chc) trait CallDispatchPosixMemalign {
    fn try_dispatch_call_posix_memalign(&mut self, dcx: &DispatchCallContext<'_>) -> bool;
}

impl<'tcx, 'body> CallDispatchPosixMemalign for ChcCtx<'tcx, 'body> {
    fn try_dispatch_call_posix_memalign(&mut self, dcx: &DispatchCallContext<'_>) -> bool {
        let Some(target) = dcx.target else {
            return false;
        };
        let callee_path = dcx.callee_path.clone().or_else(|| self.resolve_callee_path(dcx.func));
        let Some(ref callee_path) = callee_path else {
            return false;
        };
        if callee_path != "libc::posix_memalign" || dcx.args.len() < 3 {
            return false;
        }

        let dest_local: usize = dcx.destination.local;
        let Some((_, dest_var)) = self.resolve_destination(dest_local) else {
            return false;
        };
        let dest_sort = dest_var.sort().clone();
        let Some(referent_local) = resolve_ptr_target_local(self, &dcx.args[0]) else {
            return false;
        };
        let Some((_, referent_var)) = self.resolve_destination(referent_local) else {
            return false;
        };
        let referent_sort = referent_var.sort().clone();

        let Some(align_expr) =
            self.translate_operand_with_modified(&dcx.args[1], dcx.modified_locals)
        else {
            return false;
        };
        if self.translate_operand_with_modified(&dcx.args[2], dcx.modified_locals).is_none() {
            return false;
        }
        let concrete_valid_align = Self::posix_memalign_concrete_align_validity(&align_expr);
        let Some(valid_align) = Self::posix_memalign_valid_align_expr(align_expr) else {
            return false;
        };

        let Some(invalid_dest_eq) = self.make_coerced_eq_constraint(
            &dest_var,
            Expr::bitvec_const(22u128, 32),
            &dest_sort,
            dest_local,
            "posix_memalign_invalid",
        ) else {
            return false;
        };
        if concrete_valid_align == Some(false) {
            let invalid_out = self.build_output_args(dcx.modified_locals, &[dest_local]);
            self.emit_goto_rule_extra(
                dcx.from_app,
                *target,
                &invalid_out,
                dcx.stmt_constraints,
                [invalid_dest_eq],
            );
            return true;
        }

        let Some((success_constraints, alloc_obj_id)) = self.posix_memalign_success_constraints(
            dcx,
            &dest_var,
            &dest_sort,
            dest_local,
            &referent_var,
            &referent_sort,
            referent_local,
            valid_align.clone(),
        ) else {
            return false;
        };

        if concrete_valid_align != Some(true) {
            let invalid_out = self.build_output_args(dcx.modified_locals, &[dest_local]);
            self.emit_goto_rule_extra(
                dcx.from_app,
                *target,
                &invalid_out,
                dcx.stmt_constraints,
                [valid_align.clone().not(), invalid_dest_eq],
            );
        }

        let success_out =
            self.build_output_args(dcx.modified_locals, &[dest_local, referent_local]);
        self.emit_goto_rule_extra(
            dcx.from_app,
            *target,
            &success_out,
            dcx.stmt_constraints,
            success_constraints,
        );
        self.record_alloc_dest(referent_local, alloc_obj_id);
        true
    }
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    fn posix_memalign_concrete_align_validity(align_expr: &Expr) -> Option<bool> {
        let align = Self::try_extract_concrete_usize(align_expr)?;
        let ptr_bytes = (POINTER_WIDTH / 8) as usize;
        Some(align != 0 && align.is_power_of_two() && align % ptr_bytes == 0)
    }

    fn posix_memalign_valid_align_expr(align_expr: Expr) -> Option<Expr> {
        let align_width = align_expr.sort().bitvec_width()?;
        let zero = Expr::bitvec_const(0u128, align_width);
        let one = Expr::bitvec_const(1u128, align_width);
        let ptr_bytes = Expr::bitvec_const((POINTER_WIDTH / 8) as u128, align_width);
        let not_zero = align_expr.clone().ne(zero.clone());
        let is_power_of_two = align_expr.clone().bvand(align_expr.clone().bvsub(one)).eq(zero);
        let is_multiple_of_ptr =
            align_expr.bvurem(ptr_bytes).eq(Expr::bitvec_const(0u128, align_width));
        Some(not_zero.and(is_power_of_two).and(is_multiple_of_ptr))
    }

    #[allow(clippy::too_many_arguments)]
    fn posix_memalign_success_constraints(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        dest_var: &Expr,
        dest_sort: &Sort,
        dest_local: usize,
        referent_var: &Expr,
        referent_sort: &Sort,
        referent_local: usize,
        valid_align: Expr,
    ) -> Option<(Vec<Expr>, Option<u32>)> {
        let alloc_args = [dcx.args[2].clone(), dcx.args[1].clone()];
        let alloc_result =
            self.translate_rust_alloc(StubKind::RustAlloc, &alloc_args, dcx.modified_locals)?;
        let AllocCallResult {
            result: Some(ptr_expr),
            heap_constraints,
            alloc_obj_id,
            transition_branches,
            ..
        } = alloc_result
        else {
            return None;
        };
        if !transition_branches.is_empty() {
            return None;
        }

        let success_dest_eq = self.make_coerced_eq_constraint(
            dest_var,
            Expr::bitvec_const(0u128, 32),
            dest_sort,
            dest_local,
            "posix_memalign_success",
        )?;
        let out_ptr_eq = self.make_coerced_eq_constraint(
            referent_var,
            ptr_expr,
            referent_sort,
            referent_local,
            "posix_memalign_out_ptr",
        )?;

        let mut constraints = vec![valid_align, success_dest_eq, out_ptr_eq];
        constraints.extend(heap_constraints);
        Some((constraints, alloc_obj_id))
    }
}
