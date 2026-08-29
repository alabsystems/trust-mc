// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Precheck stubs for abstracted functions, BTree internals, and Cow<str>.
//!
//! Extracted from helpers.rs per design D1 (file-decomposition-500loc-compliance).

use ay_bindings::Expr;
use rustc_public::CrateDef;
use rustc_public::mir::{BasicBlockIdx, Operand, Place};
use rustc_public::ty::{GenericArgKind, RigidTy, TyKind};
use std::sync::atomic::Ordering;
use tracing::{debug, warn};

use super::ABSTRACTED_FALLBACK_COUNT;
use crate::codegen_ay::statement::StatementCodegen;
use crate::codegen_ay::stubs::StubKind;

use super::super::IntoOption;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Fallback for abstracted functions without explicit stubs (Part of #1691).
    ///
    /// When a call to an abstracted function (like UTF8 internals) has no specific stub,
    /// we return a symbolic value of the appropriate type. This handles pre-inlined stdlib
    /// code that can't be intercepted at the reachability level.
    pub(in crate::codegen_ay::statement) fn try_codegen_abstracted_fallback(
        &mut self,
        func: &Operand,
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        let callee_path = if let Some(path) = self.resolve_callee_path(func) {
            path
        } else {
            // resolve_callee_path can fail for certain function types.
            // FALLBACK: Extract function name from type Debug representation.
            // WARNING: This is fragile - it parses {:?} output which may change between Rust versions.
            let func_ty_str = func.ty(self.body.locals()).ok().map(|ty| format!("{:?}", ty))?;

            let start = func_ty_str.find("name: \"")?;
            let after_name = &func_ty_str[start + 7..];
            let end = after_name.find('"')?;
            after_name[..end].to_string()
        };
        debug!(?callee_path, "try_codegen_abstracted_fallback: checking");

        let abstracted_patterns =
            &["core::str::lossy::", "Utf8Chunk::", "Utf8Chunks::", "borrow::Cow::"];

        let is_abstracted = abstracted_patterns.iter().any(|pattern| callee_path.contains(pattern));

        let is_utf8_iterator_next =
            callee_path.contains("Iterator::next") && callee_path.contains("Utf8Chunks");

        if is_abstracted || is_utf8_iterator_next {
            let count = ABSTRACTED_FALLBACK_COUNT.fetch_add(1, Ordering::Relaxed) + 1;
            warn!("Abstracted fallback (hit #{}) for pre-inlined code: {}", count, callee_path);
            self.codegen_symbolic_result(destination);
            return target;
        }

        None
    }

    /// Pre-check for BTree internal stubs that require examining generic arguments.
    ///
    /// Returns sound over-approximation (unconstrained symbolic) for BTree/RawVec
    /// internals that leak through the reachability filter. User-visible operations
    /// (insert, get, contains) are handled by proper stubs in the collection
    /// dispatcher. See CHC equivalent: `codegen_call_unconstrained_stub_impl`.
    ///
    /// Part of #1627: BTreeSet perf test support.
    /// Reclassified from UNSOUND to SOUND_APPROXIMATION: #3098 design analysis.
    pub(in crate::codegen_ay::statement) fn try_codegen_btree_internal_precheck(
        &mut self,
        func: &Operand,
        callee_path: &str,
        _args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<Option<BasicBlockIdx>> {
        let func_ty = func.ty(self.body.locals()).into_option()?;
        let fn_args = match func_ty.kind() {
            TyKind::RigidTy(RigidTy::FnDef(_, args)) => args,
            _ => return None, // external enum: TyKind
        };

        // Part of #2043: Use structural matching instead of format!("{:?}") + contains().
        let has_setvalzst = |args: &rustc_public::ty::GenericArgs| {
            args.0.iter().any(|arg| {
                if let GenericArgKind::Type(ty) = arg
                    && let TyKind::RigidTy(RigidTy::Adt(def, _)) = ty.kind()
                {
                    let name = def.trimmed_name();
                    name == "SetValZST" || name.contains("SetValZST")
                } else {
                    false
                }
            })
        };

        let has_btree_internal = |args: &rustc_public::ty::GenericArgs| {
            args.0.iter().any(|arg| {
                if let GenericArgKind::Type(ty) = arg
                    && let TyKind::RigidTy(RigidTy::Adt(def, _)) = ty.kind()
                {
                    let name = def.trimmed_name();
                    let full_name = def.name();
                    name == "NodeRef" || name.contains("NodeRef") || full_name.contains("btree")
                } else {
                    false
                }
            })
        };

        // mem::replace<SetValZST> (Part of #1627, telemetry #1662, reclassified #3098)
        if callee_path.contains("mem::replace") && has_setvalzst(&fn_args) {
            let count = ABSTRACTED_FALLBACK_COUNT.fetch_add(1, Ordering::Relaxed) + 1;
            warn!(
                "SOUND_APPROXIMATION: Pre-inlined mem::replace<SetValZST> (hit #{}) - canonical ZST value",
                count
            );
            self.assign_value_to_place(destination, Expr::bool_const(true));
            return Some(target);
        }

        // Option::as_ref<NodeRef<...>> (Part of #1627, telemetry #1662)
        // Reclassified: sound over-approximation — as_ref is a pure borrow with no
        // side effects, so a symbolic return is universally quantified (Part of #3152).
        if callee_path.contains("Option")
            && callee_path.contains("as_ref")
            && has_btree_internal(&fn_args)
        {
            let count = ABSTRACTED_FALLBACK_COUNT.fetch_add(1, Ordering::Relaxed) + 1;
            warn!(
                "Sound over-approx: Pre-inlined Option::as_ref (BTree internal) (hit #{}) - returning symbolic",
                count
            );
            self.codegen_symbolic_result(destination);
            return Some(target);
        }

        // BTree internal functions (Part of #1659, telemetry #1662, reclassified #3098)
        if callee_path.contains("btree::node::") || callee_path.contains("btree::search::") {
            let count = ABSTRACTED_FALLBACK_COUNT.fetch_add(1, Ordering::Relaxed) + 1;
            warn!(
                "SOUND_APPROXIMATION: Pre-inlined BTree internal function (hit #{}) - returning symbolic: {}",
                count, callee_path
            );
            self.codegen_symbolic_result(destination);
            return Some(target);
        }

        // RawVec internal functions (Part of #1711)
        if callee_path.contains("raw_vec::RawVec") || callee_path.contains("raw_vec::RawVecInner") {
            let has_stub = callee_path.ends_with("::capacity")
                || callee_path.ends_with("::ptr")
                || callee_path.ends_with("::grow_one")
                || callee_path.ends_with("::new_in")
                // Part of #2877: reserve_exact/grow_amortized are modeled as
                // RawVecGrowOne capacity-growth stubs.
                || callee_path.ends_with("::reserve_exact")
                || callee_path.ends_with("::grow_amortized")
                // Part of #3007: drop/shrink_to_fit have no-op stubs in
                // stub_dispatch_memory.rs — let them through to the dispatcher.
                || callee_path.ends_with("::drop")
                || callee_path.ends_with("::shrink_to_fit");
            if !has_stub {
                let count = ABSTRACTED_FALLBACK_COUNT.fetch_add(1, Ordering::Relaxed) + 1;
                warn!(
                    "SOUND_APPROXIMATION: Pre-inlined RawVec internal function (hit #{}) - returning symbolic: {}",
                    count, callee_path
                );
                self.codegen_symbolic_result(destination);
                return Some(target);
            }
        }

        None
    }

    /// Pre-check for Cow<str>::to_string() calls (Part of #1738).
    /// Examines generic args because the def_path_str doesn't contain "Cow".
    /// `<String as BoundedArbitrary>::bounded_any::<N>()` — a symbolic String
    /// of at most N bytes. Reaches codegen because the inline pass declines it
    /// (see `should_inline_mutable`); without that this call is expanded into
    /// `utf8_chunks()` internals that abstract to unconstrained symbolics, and
    /// the bound is lost.
    pub(in crate::codegen_ay::statement) fn try_codegen_bounded_string_precheck(
        &mut self,
        func: &Operand,
        callee_path: &str,
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<Option<BasicBlockIdx>> {
        if !callee_path.ends_with("::bounded_any") || !callee_path.contains("String") {
            return None;
        }

        let func_ty = func.ty(self.body.locals()).into_option()?;
        let fn_args = match func_ty.kind() {
            TyKind::RigidTy(RigidTy::FnDef(_, args)) => args,
            _ => return None, // external enum: TyKind
        };
        // No resolvable const bound means there is no bound to state; decline
        // and let the existing fallback handle it.
        let bound = fn_args.0.iter().find_map(|arg| match arg {
            GenericArgKind::Const(c) => c.eval_target_usize().into_option(),
            _ => None,
        })?;

        debug!(bound, "bounded_any::<String, N>: modelling a String of at most N bytes");
        self.codegen_bounded_string_value(bound, destination);
        Some(target)
    }

    pub(in crate::codegen_ay::statement) fn try_codegen_cow_tostring_precheck(
        &mut self,
        func: &Operand,
        callee_path: &str,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<Option<BasicBlockIdx>> {
        if !callee_path.ends_with("::to_string") && !callee_path.contains("ToString::to_string") {
            return None;
        }

        let func_ty = func.ty(self.body.locals()).into_option()?;
        let fn_args = match func_ty.kind() {
            TyKind::RigidTy(RigidTy::FnDef(_, args)) => args,
            _ => return None, // external enum: TyKind
        };

        // Part of #2267: Structural matching instead of format!("{:?}") + contains().
        let is_cow_str = fn_args.0.first().is_some_and(|arg| {
            let GenericArgKind::Type(ty) = arg else { return false };
            // Unwrap one level of reference if present (e.g., &Cow<'_, str>)
            let inner_ty = match ty.kind() {
                TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => inner,
                _ => *ty, // external enum: TyKind
            };
            if let TyKind::RigidTy(RigidTy::Adt(def, inner_args)) = inner_ty.kind() {
                def.trimmed_name().contains("Cow")
                    && inner_args.0.iter().any(|a| matches!(a,
                        GenericArgKind::Type(t) if matches!(t.kind(), TyKind::RigidTy(RigidTy::Str))))
            } else {
                false
            }
        });

        if is_cow_str {
            debug!(
                "Cow<str>::to_string detected via generic arg precheck, routing to CowToString stub"
            );
            return Some(self.codegen_string_stub(
                StubKind::CowToString,
                args,
                destination,
                target,
                callee_path,
            ));
        }

        None
    }

    /// `MaybeUninit::uninit()` / `MaybeUninit::assume_init()` precheck.
    ///
    /// These are tiny generic stdlib methods that otherwise get mini-inlined into
    /// a union construction / transmute the BMC backend can't encode, leaving the
    /// destination unconstrained (and breaking the enclosing struct aggregate,
    /// e.g. `ArrayVec::new`). Model them at their exact semantics, before inlining:
    ///
    /// - `uninit()`: uninitialized memory is EXACTLY an arbitrary value of the
    ///   inner type. Declare a fresh unconstrained value of the destination sort
    ///   (`MaybeUninit<T>` is transparent → `T`'s sort). Universally quantified →
    ///   sound for proofs; any later element store/read threads through it.
    /// - `assume_init(self)`: a transparent transmute `MaybeUninit<T> → T`; the
    ///   single argument already carries the (transparently-modelled) inner value,
    ///   so pass it through unchanged.
    ///
    /// `assume_init_read`/`assume_init_drop`/`assume_init_ref` are NOT matched here
    /// (handled by the element-read modelling), only the plain `::assume_init`.
    pub(in crate::codegen_ay::statement) fn try_codegen_maybe_uninit_precheck(
        &mut self,
        callee_path: &str,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<Option<BasicBlockIdx>> {
        if !callee_path.contains("MaybeUninit") {
            return None;
        }
        if callee_path.ends_with("::uninit") {
            let dest_ty = destination.ty(self.body.locals()).into_option()?;
            let dest_sort = Self::infer_sort_from_ty(dest_ty)?;
            let name = self.ctx.fresh_name("maybe_uninit");
            let fresh = self.ctx.declare_var(&name, dest_sort);
            self.assign_value_to_place(destination, fresh);
            debug!(%callee_path, "MaybeUninit::uninit → fresh inner value (uninit = arbitrary)");
            return Some(target);
        }
        if callee_path.ends_with("::assume_init") {
            let arg_expr = args.first().and_then(|a| self.codegen_operand(a))?;
            self.assign_value_to_place(destination, arg_expr);
            debug!(%callee_path, "MaybeUninit::assume_init → transparent passthrough");
            return Some(target);
        }
        None
    }
}
