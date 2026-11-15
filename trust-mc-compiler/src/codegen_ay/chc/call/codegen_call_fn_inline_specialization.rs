// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Specialized inline dispatch handlers for CHC codegen.
//!
//! Contains copy-swap body pattern matching. Extracted from
//! `codegen_call_fn_inline.rs` for module size compliance (#4130).

use rustc_public::CrateDef;
use rustc_public::mir::mono::Instance;
use rustc_public::mir::{Operand, TerminatorKind};
use rustc_public::rustc_internal;
use rustc_public::ty::{RigidTy, TyKind};
use tracing::debug;

use super::ChcCtx;
use super::chc_call_context::DispatchCallContext;
use super::codegen_call_coerce::CallCoerce;
use super::codegen_call_misc::CallMisc;
use super::codegen_rules::CodegenRules;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    pub(in crate::codegen_ay::chc) fn try_dispatch_copy_swap_body(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        body: &rustc_public::mir::Body,
        callee_name: &str,
    ) -> bool {
        if !self.body_matches_copy_swap_pattern(body) || dcx.args.len() < 2 {
            return false;
        }
        let Some(target) = dcx.target else { return false };
        let Some(x_local) = super::ptr_receiver_mem::resolve_ptr_target_local(self, &dcx.args[0])
        else {
            return false;
        };
        let Some(y_local) = super::ptr_receiver_mem::resolve_ptr_target_local(self, &dcx.args[1])
        else {
            return false;
        };
        let Some(x_val) = self.resolve_ref_or_const_referent(&dcx.args[0], dcx.modified_locals)
        else {
            return false;
        };
        let Some(y_val) = self.resolve_ref_or_const_referent(&dcx.args[1], dcx.modified_locals)
        else {
            return false;
        };

        let Some(mut x_constraints) =
            self.build_local_update_constraints(x_local, y_val, "fn_inline_copy_swap_x")
        else {
            return false;
        };
        let Some(mut y_constraints) =
            self.build_local_update_constraints(y_local, x_val, "fn_inline_copy_swap_y")
        else {
            return false;
        };

        let dest_local = dcx.destination.local;
        let mut extra_dests = vec![dest_local, x_local];
        if y_local != x_local {
            extra_dests.push(y_local);
        }

        x_constraints.append(&mut y_constraints);

        // Part of #3932: Clear stale cross-block constant propagation entries for
        // the swapped locals. Without this, subsequent blocks read cached constants
        // (e.g. _1=12) instead of the updated state variables (_1__out=13).
        self.encode.invalidate_local_cache(x_local);
        self.encode.invalidate_local_cache(y_local);
        debug!(
            bb_idx = dcx.bb_idx,
            %callee_name,
            x_local,
            y_local,
            "fn_inline: direct copy-swap body dispatch"
        );
        self.emit_goto_rule_extra(
            dcx.from_app,
            *target,
            &self.build_output_args(dcx.modified_locals, &extra_dests),
            dcx.stmt_constraints,
            x_constraints,
        );
        true
    }

    fn body_matches_copy_swap_pattern(&self, body: &rustc_public::mir::Body) -> bool {
        if body.arg_locals().len() != 2 {
            return false;
        }
        let arg1_is_mut_ref = body.locals().get(1).is_some_and(|decl| {
            matches!(
                decl.ty.kind(),
                TyKind::RigidTy(RigidTy::Ref(_, _, rustc_public::mir::Mutability::Mut))
            )
        });
        let arg2_is_mut_ref = body.locals().get(2).is_some_and(|decl| {
            matches!(
                decl.ty.kind(),
                TyKind::RigidTy(RigidTy::Ref(_, _, rustc_public::mir::Mutability::Mut))
            )
        });
        if !arg1_is_mut_ref || !arg2_is_mut_ref {
            return false;
        }

        let mut copy_calls = 0usize;
        let mut uninitialized_calls = 0usize;
        let mut forget_calls = 0usize;

        for block in &body.blocks {
            let TerminatorKind::Call { func, .. } = &block.terminator.kind else { continue };
            let Some(path) = self.resolve_inline_body_callee_path(body, func) else {
                return false;
            };
            if path.contains("copy_nonoverlapping") {
                copy_calls += 1;
            } else if path.ends_with("::uninitialized") {
                uninitialized_calls += 1;
            } else if path.ends_with("::forget") {
                forget_calls += 1;
            } else {
                return false;
            }
        }

        copy_calls == 3 && uninitialized_calls == 1 && forget_calls == 1
    }

    pub(in crate::codegen_ay::chc) fn resolve_inline_body_callee_path(
        &self,
        body: &rustc_public::mir::Body,
        func: &Operand,
    ) -> Option<String> {
        let func_ty = func.ty(body.locals()).ok()?;
        let (fn_def, fn_substs) = match func_ty.kind() {
            TyKind::RigidTy(RigidTy::FnDef(def, substs)) => (def, substs),
            _ => return None,
        };
        let instance = Instance::resolve(fn_def, &fn_substs).ok()?;
        Some(self.tcx.def_path_str(rustc_internal::internal(self.tcx, instance.def.def_id())))
    }
}
