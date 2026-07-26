// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Inline `kani::internal::apply_closure` (function-contract closures, "Layer B").
//!
//! A `#[kani::ensures(|x| pred)]` contract expands to
//! `apply_closure(closure, &value)`, where
//! `apply_closure<T, U: Fn(&T) -> bool>(f: U, x: &T) -> bool { f(x) }`
//! is a type-inference shim defined in `kani_core` (`library/kani_core/src/lib.rs`).
//!
//! The MIR pre-inline pass *should* flatten this call before BMC codegen, but its
//! depth boost (`needs_contract_inline_boost`) only scans the harness's own body.
//! Harnesses that reach a contracted function only *transitively* (e.g. aterm's
//! `advance -> process_byte -> process_byte_inner`) leave a residual
//! `apply_closure` Call terminator, which previously fell through every dispatcher
//! to `unsupported_call_successors` and demoted the verdict (EncodingGap).
//!
//! This handler models `apply_closure(f, x) == f(x)` directly: it resolves the
//! closure `f` to its concrete body and inlines it via the shared BMC mini-inliner
//! with `x` seeded as the closure's (un-tupled) value argument. The closure's
//! inner `Fn::call` / `type_invariant` calls are then handled by the existing
//! mini-inline Call dispatch.
//!
//! SOUNDNESS (mandatory): on an inline DECLINE we return `None` so the existing
//! (sound) `unsupported_with_fallback` demotion stands. We MUST NOT synthesize a
//! symbolic `bool` here — that value would flow into the `ensures` ASSERT and
//! could produce a FALSE COUNTEREXAMPLE. The path match is exact
//! (`::apply_closure` + `internal`) so a different call is never mis-routed.

use std::sync::Arc;

use rustc_public::mir::mono::Instance;
use rustc_public::mir::{BasicBlockIdx, Operand, Place};
use rustc_public::ty::{ClosureKind, RigidTy, Ty, TyKind};
use tracing::debug;

use crate::codegen_ay::statement::StatementCodegen;

use super::super::IntoOption;
use super::inline_body::InlineArgValue;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Attempt to model a `kani::internal::apply_closure(f, x)` call as `f(x)` by
    /// inlining the closure body `f` with `x` as its argument.
    ///
    /// Returns `Some(next_bb)` when the closure body was inlined, `None` when this
    /// handler declines (caller continues the dispatch chain, so the sound
    /// unsupported fallback is preserved). NEVER emits a symbolic result.
    pub(in crate::codegen_ay::statement) fn try_codegen_apply_closure(
        &mut self,
        func: &Operand,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        // Exact path match — only `kani::internal::apply_closure`. Bail otherwise
        // so we never mis-route a different call.
        let path = self.resolve_callee_path(func)?;
        if !(path.ends_with("::apply_closure") && path.contains("internal")) {
            return None;
        }
        // Signature is `apply_closure(f: U, x: &T)`: exactly the closure and one
        // un-tupled reference argument.
        if args.len() != 2 {
            debug!(args = args.len(), "apply_closure: unexpected arity, declining");
            return None;
        }

        // args[0] = the closure `f` (a `Closure` value, or a `Ref<Closure>` after
        // monomorphization); args[1] = the single `&T`.
        let closure_ty = args[0].ty(self.body.locals()).into_option()?;
        let instance = self.resolve_apply_closure_instance(closure_ty)?;

        let body = self.ctx.body_or_instance_body(instance)?;
        let arg_locals = body.arg_locals();
        // The DIRECT closure body takes exactly (env_receiver, value). A tupled
        // `FnOnce` forwarding shim would have arity 2 but a `(&T,)` tuple value
        // local, which would mis-seed our un-tupled `x`. Decline both shapes so
        // the sound fallback stands rather than encoding a wrong value.
        if arg_locals.len() != 2 {
            debug!(
                callee = instance.name(),
                arity = arg_locals.len(),
                "apply_closure: closure body arity != 2, declining"
            );
            return None;
        }
        let receiver_ty = arg_locals[0].ty;
        let value_ty = arg_locals[1].ty;
        if matches!(value_ty.kind(), TyKind::RigidTy(RigidTy::Tuple(_))) {
            debug!(
                callee = instance.name(),
                "apply_closure: value local is RustCall-tupled (FnOnce shim), declining"
            );
            return None;
        }

        // Normalize the two arguments to the closure body's signature.
        let receiver = self.build_apply_closure_receiver(&args[0], closure_ty, receiver_ty)?;
        let value = self.translate_inline_arg_value(&args[1], value_ty)?;
        let params = vec![receiver, value];

        // SOUNDNESS: on decline (`None`), propagate `None` — do NOT emit a symbolic
        // bool. The caller falls through to the existing unsupported fallback.
        let next_bb =
            self.try_inline_small_instance_call(instance, &params, destination, target)?;
        debug!(callee = instance.name(), "apply_closure: inlined contract closure body");
        Some(next_bb)
    }

    /// Build the closure-environment receiver parameter for the inlined closure body.
    ///
    /// `apply_closure` takes `f: U` BY VALUE, but the direct (`Fn`/`FnMut`) closure
    /// body takes its environment BY REFERENCE (`&closure_env`). When `f` is a
    /// closure value but the body's receiver is a reference, we manufacture a
    /// pointee so the body's `(*receiver).<upvar>` deref resolves straight back to
    /// the closure value — and thus to its captured `&mut self` upvar, which is
    /// what backs the `type_invariant(self)` read. When `f` is already a
    /// `Ref<Closure>`, the standard arg translation recovers the genuine pointee.
    fn build_apply_closure_receiver(
        &mut self,
        closure_arg: &Operand,
        closure_ty: Ty,
        receiver_ty: Ty,
    ) -> Option<InlineArgValue> {
        let receiver_is_ref = matches!(
            receiver_ty.kind(),
            TyKind::RigidTy(RigidTy::Ref(..)) | TyKind::RigidTy(RigidTy::RawPtr(..))
        );
        let closure_is_value = matches!(closure_ty.kind(), TyKind::RigidTy(RigidTy::Closure(..)));

        if receiver_is_ref && closure_is_value {
            // Closure passed by value into a by-reference receiver: the closure
            // value's own SSA base IS the pointee the body derefs back to.
            let expr = self.codegen_operand(closure_arg)?;
            let pointee_base = match closure_arg {
                Operand::Copy(place) | Operand::Move(place) => {
                    Some(Arc::from(self.ssa_base_name(place).as_str()))
                }
                Operand::Constant(_) => None,
            };
            return Some(InlineArgValue {
                expr,
                pointee_base,
                flattened_entries: Vec::new(),
                nested_ref_pointees: Vec::new(),
            });
        }

        // Ref<Closure> receiver (genuine alias) or by-value receiver: the shared
        // translation already recovers the right expr + pointee mapping.
        self.translate_inline_arg_value(closure_arg, receiver_ty)
    }

    /// Resolve the closure `f` passed to `apply_closure` to its DIRECT body.
    ///
    /// Tries `Fn` first (apply_closure requires `U: Fn(&T) -> bool`, so the
    /// closure's natural kind is `Fn`): that resolution yields the closure's own
    /// MIR — receiver = closure env, single value arg = the UN-tupled `&T`. We
    /// deliberately avoid `FnOnce`-first ordering (which would resolve to a
    /// RustCall-tupled `ClosureOnceShim` whose argument is `(&T,)`).
    fn resolve_apply_closure_instance(&self, closure_ty: Ty) -> Option<Instance> {
        let (def, generic_args) = match closure_ty.kind() {
            TyKind::RigidTy(RigidTy::Closure(def, generic_args)) => (def, generic_args),
            TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => match inner.kind() {
                TyKind::RigidTy(RigidTy::Closure(def, generic_args)) => (def, generic_args),
                _ => return None,
            },
            _ => return None,
        };
        for kind in [ClosureKind::Fn, ClosureKind::FnMut, ClosureKind::FnOnce] {
            if let Ok(instance) = Instance::resolve_closure(def, &generic_args, kind)
                && instance.body().is_some()
            {
                return Some(instance);
            }
        }
        None
    }
}
