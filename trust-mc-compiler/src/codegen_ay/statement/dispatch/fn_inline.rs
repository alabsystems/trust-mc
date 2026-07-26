// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! BMC direct function call inlining.
//!
//! When a `FnDef` call falls through all specialized dispatchers (kani hooks,
//! stubs, closures, virtual calls, pow, math-unary), this handler attempts to
//! resolve the callee to a concrete Instance and inline its body using the
//! shared BMC mini-inliner from `inline_body.rs`.
//!
//! This is the BMC counterpart of CHC `codegen_call_fn_inline.rs`. Unlike the
//! CHC version, it does not emit CHC rules or manage vtable/mem-bridge state —
//! it delegates entirely to `try_inline_small_instance_call`.
//!
//! Part of #3377: BMC missing fn_inline dispatch capability.

use rustc_public::mir::mono::{Instance, InstanceKind};
use rustc_public::mir::{BasicBlockIdx, Operand, Place};
use rustc_public::ty::{Abi, RigidTy, TyKind};
use tracing::debug;

use crate::codegen_ay::statement::StatementCodegen;

use super::super::IntoOption;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Attempt to inline a direct `FnDef` call via the BMC mini-inliner.
    ///
    /// Returns `Some(next_bb)` if the call was successfully inlined,
    /// `None` if this handler declines (caller should continue dispatch chain).
    pub(in crate::codegen_ay::statement) fn try_codegen_fn_inline_call(
        &mut self,
        func: &Operand,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        let func_ty = func.ty(self.body.locals()).into_option()?;
        let (fn_def, fn_substs) = match func_ty.kind() {
            TyKind::RigidTy(RigidTy::FnDef(def, substs)) => (def, substs),
            _ => return None,
        };

        let instance = Instance::resolve(fn_def, &fn_substs).into_option()?;

        // Skip virtual calls — handled by the virtual dispatch handler.
        if matches!(instance.kind, InstanceKind::Virtual { .. }) {
            return None;
        }

        if self.should_delegate_closure_call(func, func_ty, args) {
            return self.codegen_closure_call(func, args, destination, target);
        }

        // Translate arguments using the shared inline arg helper.
        let params: Option<Vec<_>> = args
            .iter()
            .map(|arg| {
                let arg_ty = arg.ty(self.body.locals()).into_option()?;
                self.translate_inline_arg_value(arg, arg_ty)
            })
            .collect();
        let params = params?;

        let next_bb =
            self.try_inline_small_instance_call(instance, &params, destination, target)?;

        debug!(
            callee = instance.name(),
            "fn_inline(bmc): successfully inlined direct function call"
        );
        Some(next_bb)
    }

    fn is_closure_trait_call(&self, func: &Operand) -> bool {
        let Some(path) = self.resolve_callee_path(func) else {
            return false;
        };
        path.contains("ops::")
            && ((path.contains("FnOnce") && path.contains("call_once"))
                || (path.contains("FnMut") && path.contains("call_mut"))
                || (path.contains("::Fn") && path.contains("::call")))
    }

    fn should_delegate_closure_call(
        &self,
        func: &Operand,
        func_ty: rustc_public::ty::Ty,
        args: &[Operand],
    ) -> bool {
        if self.is_closure_trait_call(func) {
            return true;
        }

        let Some(sig) = func_ty.kind().fn_sig() else {
            return false;
        };
        sig.skip_binder().abi == Abi::RustCall
            && args.iter().any(|arg| self.arg_is_closure_type(arg))
    }

    fn arg_is_closure_type(&self, arg: &Operand) -> bool {
        let Some(ty) = arg.ty(self.body.locals()).into_option() else {
            return false;
        };
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Closure(..)) => true,
            TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => {
                matches!(inner.kind(), TyKind::RigidTy(RigidTy::Closure(..)))
            }
            _ => false,
        }
    }
}
