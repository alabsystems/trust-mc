// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! BMC function pointer call resolution.
//!
//! Handles `TerminatorKind::Call` where the callee operand has type
//! `RigidTy::FnPtr(..)` — indirect calls through function pointers.
//!
//! Resolution strategy mirrors CHC `codegen_call_fn_ptr.rs`: scan the caller
//! MIR for `PointerCoercion::ReifyFnPointer` and `ClosureFnPointer` casts
//! that produce the function pointer local, then inline the resolved body
//! via `try_inline_small_instance_call`.
//!
//! Unlike the CHC version, this does not emit CHC rules or manage
//! vtable/mem-bridge state — it delegates to the shared BMC mini-inliner.
//!
//! Part of #3377: BMC missing fn_ptr dispatch capability.

use ay_bindings::Expr;
use rustc_public::mir::mono::Instance;
use rustc_public::mir::{
    BasicBlockIdx, CastKind, Operand, Place, PointerCoercion, Rvalue, StatementKind,
};
use rustc_public::ty::{ClosureKind, RigidTy, TyKind};
use tracing::debug;

use crate::codegen_ay::statement::StatementCodegen;

use super::super::IntoOption;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Attempt to resolve and inline an indirect function pointer call.
    ///
    /// Returns `Some(next_bb)` if the call was successfully resolved and inlined,
    /// `None` if this handler declines.
    pub(in crate::codegen_ay::statement) fn try_codegen_fn_ptr_call(
        &mut self,
        func: &Operand,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        let func_ty = func.ty(self.body.locals()).into_option()?;
        if !matches!(func_ty.kind(), TyKind::RigidTy(RigidTy::FnPtr(..))) {
            return None;
        }

        let (instance, is_closure) = self.resolve_bmc_fn_ptr_callee(func)?;

        // Translate arguments using the shared inline arg helper.
        let params: Option<Vec<_>> = args
            .iter()
            .map(|arg| {
                let arg_ty = arg.ty(self.body.locals()).into_option()?;
                self.translate_inline_arg_value(arg, arg_ty)
            })
            .collect();
        let params = match params {
            Some(p) => p,
            None => {
                debug!(
                    callee = instance.name(),
                    is_closure,
                    arg_count = args.len(),
                    "fn_ptr(bmc): parameter translation failed"
                );
                return None;
            }
        };

        // For closure fn pointers, the body uses RustCall ABI where local 1 is
        // the closure env (empty tuple for non-capturing closures). The body's
        // arg_locals include the env as the first parameter, so we must prepend
        // a dummy ZST env value to match the body's expected arity.
        // This mirrors the CHC path (translate_closure_inline_result) which maps
        // params to local 2..2+N, skipping local 1 (the closure env).
        let params = if is_closure {
            let mut closure_params = Vec::with_capacity(params.len() + 1);
            closure_params.push(super::inline_body::InlineArgValue {
                expr: Expr::bool_const(false),
                pointee_base: None,
                flattened_entries: Vec::new(),
                nested_ref_pointees: Vec::new(),
            });
            closure_params.extend(params);
            closure_params
        } else {
            params
        };

        debug!(
            callee = instance.name(),
            is_closure,
            param_count = params.len(),
            "fn_ptr(bmc): attempting inline with resolved callee"
        );
        let next_bb =
            self.try_inline_small_instance_call(instance, &params, destination, target)?;

        debug!(
            callee = instance.name(),
            is_closure, "fn_ptr(bmc): successfully resolved and inlined function pointer call"
        );
        Some(next_bb)
    }

    /// Resolve a function pointer operand to its concrete Instance.
    ///
    /// Scans the caller MIR for `ReifyFnPointer` and `ClosureFnPointer` casts
    /// that flow into the fn_ptr local, following copy/move chains.
    /// Returns `(instance, is_closure)`.
    fn collect_fn_ptr_copy_chain(&self, func: &Operand) -> std::collections::HashSet<usize> {
        let fn_ptr_local = match func {
            Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => Some(p.local),
            _ => None,
        };
        let mut target_locals = std::collections::HashSet::new();
        if let Some(local) = fn_ptr_local {
            target_locals.insert(local);
            for _ in 0..5 {
                let mut new_locals = Vec::new();
                for bb in &self.body.blocks {
                    for stmt in &bb.statements {
                        if let StatementKind::Assign(place, rvalue) = &stmt.kind {
                            if !target_locals.contains(&place.local) {
                                continue;
                            }
                            if let Rvalue::Use(Operand::Copy(src) | Operand::Move(src)) = rvalue {
                                if src.projection.is_empty() {
                                    new_locals.push(src.local);
                                }
                            }
                        }
                    }
                }
                if new_locals.is_empty() {
                    break;
                }
                target_locals.extend(new_locals);
            }
        }
        target_locals
    }

    pub(in crate::codegen_ay::statement) fn resolve_bmc_fn_ptr_callee(
        &self,
        func: &Operand,
    ) -> Option<(Instance, bool)> {
        let target_locals = self.collect_fn_ptr_copy_chain(func);

        // Scan for ReifyFnPointer/ClosureFnPointer casts.
        for bb in &self.body.blocks {
            for stmt in &bb.statements {
                if let StatementKind::Assign(place, rvalue) = &stmt.kind {
                    // If we have target locals, only check assignments to them.
                    // Otherwise (no projection resolution), check all assignments.
                    if !target_locals.is_empty() && !target_locals.contains(&place.local) {
                        continue;
                    }
                    match rvalue {
                        Rvalue::Cast(
                            CastKind::PointerCoercion(PointerCoercion::ReifyFnPointer),
                            operand,
                            _,
                        ) => {
                            if let Some(instance) = self.resolve_reify_fn_ptr_instance(operand) {
                                debug!("fn_ptr(bmc): resolved via ReifyFnPointer");
                                return Some((instance, false));
                            }
                        }
                        Rvalue::Cast(
                            CastKind::PointerCoercion(PointerCoercion::ClosureFnPointer(_)),
                            operand,
                            _,
                        ) => {
                            if let Some(instance) = self.resolve_closure_fn_ptr_instance(operand) {
                                debug!("fn_ptr(bmc): resolved via ClosureFnPointer");
                                return Some((instance, true));
                            }
                        }
                        _ => {}
                    }
                }
            }
        }

        // Fallback: check pre-resolved fn_ptr callees from parent (caller) scope.
        // When the fn_ptr is received as a parameter, the cast is in the caller,
        // not in this body. The parent state carries the resolution.
        if let Some((instance, is_closure)) = self.parent_fn_ptr_callees.first() {
            debug!("fn_ptr(bmc): resolved via parent scope fallback");
            return Some((*instance, *is_closure));
        }

        None
    }

    /// Scan this body for `ReifyFnPointer` casts whose target is a FOREIGN
    /// item, returning the short names. Kept separate from
    /// [`resolve_all_fn_ptr_callees`] because an extern declaration has no MIR
    /// and `Instance::resolve` fails on it — the tuple registry structurally
    /// cannot represent these.
    pub(in crate::codegen_ay::statement) fn resolve_all_foreign_fn_ptr_names(&self) -> Vec<String> {
        let mut names = Vec::new();
        for bb in &self.body.blocks {
            for stmt in &bb.statements {
                if let StatementKind::Assign(_, rvalue) = &stmt.kind
                    && let Rvalue::Cast(
                        CastKind::PointerCoercion(PointerCoercion::ReifyFnPointer),
                        operand,
                        _,
                    ) = rvalue
                    && self.is_foreign_call(operand)
                {
                    let full = self.callee_display_name(operand);
                    names.push(full);
                }
            }
        }
        names
    }

    /// Scan this body for all ReifyFnPointer/ClosureFnPointer casts and resolve
    /// them. Used to pre-populate `parent_fn_ptr_callees` for nested inlines.
    pub(in crate::codegen_ay::statement) fn resolve_all_fn_ptr_callees(
        &self,
    ) -> Vec<(Instance, bool)> {
        let mut callees = Vec::new();
        for bb in &self.body.blocks {
            for stmt in &bb.statements {
                if let StatementKind::Assign(_place, rvalue) = &stmt.kind {
                    match rvalue {
                        Rvalue::Cast(
                            CastKind::PointerCoercion(PointerCoercion::ReifyFnPointer),
                            operand,
                            _,
                        ) => {
                            if let Some(instance) = self.resolve_reify_fn_ptr_instance(operand) {
                                callees.push((instance, false));
                            }
                        }
                        Rvalue::Cast(
                            CastKind::PointerCoercion(PointerCoercion::ClosureFnPointer(_)),
                            operand,
                            _,
                        ) => {
                            if let Some(instance) = self.resolve_closure_fn_ptr_instance(operand) {
                                callees.push((instance, true));
                            }
                        }
                        _ => {}
                    }
                }
            }
        }
        callees
    }

    /// Resolve a `ReifyFnPointer` operand to a concrete Instance.
    fn resolve_reify_fn_ptr_instance(&self, operand: &Operand) -> Option<Instance> {
        let ty = operand.ty(self.body.locals()).into_option()?;
        let (fn_def, fn_substs) = match ty.kind() {
            TyKind::RigidTy(RigidTy::FnDef(def, substs)) => (def, substs),
            _ => return None,
        };
        let instance = Instance::resolve(fn_def, &fn_substs).into_option()?;
        // Verify the instance has a body we can inline.
        instance.body()?;
        Some(instance)
    }

    /// Resolve a `ClosureFnPointer` operand to a concrete Instance.
    ///
    /// Tries all three closure kinds (Fn, FnMut, FnOnce) since the closure's
    /// native kind determines which resolve_closure call yields a body.
    fn resolve_closure_fn_ptr_instance(&self, operand: &Operand) -> Option<Instance> {
        let ty = operand.ty(self.body.locals()).into_option()?;
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Closure(def, args)) => {
                for kind in [ClosureKind::Fn, ClosureKind::FnMut, ClosureKind::FnOnce] {
                    if let Ok(inst) = Instance::resolve_closure(def, &args, kind) {
                        if inst.body().is_some() {
                            return Some(inst);
                        }
                    }
                }
                None
            }
            TyKind::RigidTy(RigidTy::FnDef(fn_def, fn_substs)) => {
                let instance = Instance::resolve(fn_def, &fn_substs).into_option()?;
                instance.body()?;
                Some(instance)
            }
            _ => None,
        }
    }
}
