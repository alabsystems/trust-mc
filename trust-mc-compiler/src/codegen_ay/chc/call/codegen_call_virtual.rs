// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Virtual call (dynamic dispatch) handler for CHC codegen.
//!
//! Detects `InstanceKind::Virtual` calls and attempts to resolve them to
//! concrete implementations for inline translation.
//!
//! - **Single-impl**: The method body is inlined directly.
//! - **Multi-impl**: Each implementation is inlined and combined via an ITE
//!   (if-then-else) chain conditioned on the receiver's `fld_vtable` field.
//!   This implements Option B (Static Dispatch Enumeration) from the vtable
//!   encoding design (`designs/archive/2026-02-01-trait-object-vtable-encoding.md`).
//! - **Zero-impl**: Falls through to the over-approximation fallback (sound).
//!
//! Part of #3159: DynTrait category recovery Phase 1.

use crate::codegen_ay::chc::codegen_ctx::Havoc;
use ay_bindings::{Expr, Sort, SortInner};
use rustc_public::mir::mono::{Instance, InstanceKind};
use rustc_public::ty::{RigidTy, TyKind};
use tracing::debug;

use super::ChcCtx;
use super::chc_call_context::DispatchCallContext;
use super::codegen_call_coerce::CallCoerce;
use super::codegen_call_fn_inline::widen_inline_result_for_fat_pointer;
use super::codegen_call_virtual_inline::{
    InlineReturn, build_dispatch_ite_chain, is_fn_trait_call, receiver_base_local,
    translate_virtual_body_inline, try_fn_trait_direct_dispatch,
};
use super::codegen_rules::CodegenRules;
use super::dyn_coercion::{self, ResolvedDispatchBody};
use super::inline_field_map::populate_inline_self_field_hints;
use super::inline_result_shared::{
    InlineResultEpilogueSpec, emit_prepared_inline_result, prepare_inline_result_epilogue,
};
use crate::codegen_ay::provenance::Val;
use crate::codegen_ay::ptr_repr::PtrRepr;
use crate::codegen_ay::types::{CtorFieldExt, POINTER_WIDTH};

/// Extension trait for virtual call dispatch on `ChcCtx`.
pub(in crate::codegen_ay::chc) trait CallDispatchVirtual {
    /// Attempt to dispatch a virtual (dyn Trait) call by resolving to a
    /// concrete implementation. Returns `true` if handled.
    fn try_dispatch_call_virtual(&mut self, dcx: &DispatchCallContext<'_>) -> bool;
}

impl<'tcx, 'body> CallDispatchVirtual for ChcCtx<'tcx, 'body> {
    fn try_dispatch_call_virtual(&mut self, dcx: &DispatchCallContext<'_>) -> bool {
        let Some(target) = dcx.target else { return false };

        let Some((fn_def, fn_args, vtable_idx)) = resolve_virtual_instance(self, dcx) else {
            return false;
        };

        debug!(
            bb_idx = dcx.bb_idx,
            ?vtable_idx,
            "virtual call detected — attempting devirtualization"
        );

        // Part of #3589: Use merged candidate sequence that combines non-blanket
        // impls with MIR-coercion-derived candidates. This replaces the old
        // two-step pattern (find_concrete_virtual_impls then fallback) which
        // missed blanket impls when non-blanket impls existed for the same trait.
        let Some(method_trait_def_id) = self.resolve_parent_trait_def_id(fn_def) else {
            return false;
        };
        // Design 3 (dyn_dispatch_scope.rs): dispatch over the receiver's
        // principal, whose candidate list the stored vtable ids index, and
        // decide the default arm from the harness's dyn-coercion universe.
        let Some(dispatch_trait) =
            super::dyn_dispatch_scope::dispatch_trait_for_call(self, method_trait_def_id, &fn_args)
        else {
            self.record_sound_fallback_reason(super::dyn_dispatch_scope::DYN_PRINCIPAL_MISMATCH);
            return false;
        };
        let trait_def_id = dispatch_trait.def_id;
        let candidates = dyn_coercion::collect_dyn_trait_candidates(self, trait_def_id);
        let scope =
            super::dyn_dispatch_scope::DynDispatchScope::new(self, &dispatch_trait, &candidates);
        let (concrete_bodies, dropped_candidate) =
            dyn_coercion::resolve_dispatch_bodies(self, &candidates, fn_def, &fn_args);

        if concrete_bodies.is_empty() {
            debug!(bb_idx = dcx.bb_idx, "virtual call: no concrete impls found");
            if dropped_candidate {
                // Every resolved candidate lost its body: the fall-through
                // over-approximation is sound, but record the narrowing.
                self.record_sound_fallback_reason("dyn_dispatch_candidate_body_dropped");
            }
            return false;
        }
        // SOUNDNESS: a silently narrowed candidate set must never take the
        // single-impl UNCONDITIONAL inline below (no disc guard — inlining the
        // lone survivor fabricates the wrong impl's value when the runtime
        // type was the dropped candidate). Route the lone survivor through the
        // GUARDED dispatch ITE instead (disc == survivor id, default arm =
        // fresh unconstrained var): sound for the dropped type, still proving
        // when the discriminant resolves to the survivor. v28 gate evidence:
        // a hard refusal here FP'd trait_to_trait_coercion + any_cast_int,
        // whose dropped candidates are body-less resolved shims.
        if dropped_candidate {
            self.record_aggregate_gap("dyn_dispatch_candidate_body_dropped");
        }

        debug!(
            bb_idx = dcx.bb_idx,
            impl_count = concrete_bodies.len(),
            "virtual call: found concrete impls, attempting inline"
        );

        // Part of #3995: Short-circuit Fn/FnMut/FnOnce trait calls to the
        // direct fn-item body, bypassing the blanket impl shim.
        if let Some(result) =
            self.try_fn_trait_shortcircuit(dcx, &candidates, &concrete_bodies, &scope)
        {
            self.emit_virtual_result(dcx, result, *target);
            return true;
        }

        // Soundness (missed-bug C): decline the single-impl unconditional inline
        // when candidate collection is provably incomplete — a parametric
        // (`has_param`) non-blanket impl was dropped in Phase 1 and no in-body
        // `Unsize` coercion grounded the sole candidate. The real runtime type
        // may be a parametric instantiation coerced to `dyn` cross-function
        // (e.g. `impl<T> Speak for Loud<T>` reached via a callee), which the lone
        // concrete candidate misses; inlining it unconditionally would fabricate
        // a wrong value and vacuously discharge a downstream assert. Fail closed
        // to the sound over-approximation (dest unconstrained), exactly as a
        // failed single-impl inline does below.
        if concrete_bodies.len() == 1
            && dyn_coercion::single_candidate_set_is_incomplete(self, trait_def_id, &candidates)
        {
            self.record_sound_fallback_reason("virtual_candidates_incomplete_parametric");
            debug!(
                bb_idx = dcx.bb_idx,
                "virtual call: candidate set incomplete (dropped parametric impl, \
                 no grounding in-body coercion); over-approximating"
            );
            return false;
        }

        // Single-impl: inline directly, only when the harness's dyn-coercion
        // universe says this impl is the receiver's ONLY runtime type (design
        // 3). A one-entry candidate list is not enough: a type coerced in a
        // callee need not be in it. Anything else takes the guarded dispatch
        // below, whose default arm fails closed unless the arms cover every
        // runtime type.
        if concrete_bodies.len() == 1
            && !dropped_candidate
            && scope.is_sole_runtime(concrete_bodies[0].vtable_id)
        {
            let impl_body = &concrete_bodies[0].body;

            let Some(inline_result) = self.translate_and_inline_virtual(dcx, impl_body) else {
                debug!(bb_idx = dcx.bb_idx, "virtual call: single-impl inline failed");
                return false;
            };

            self.emit_virtual_result(dcx, inline_result, *target);
            return true;
        }

        // Multi-impl: inline each body and build ITE case-split.
        let Some(inline_result) =
            self.dispatch_multi_impl_virtual(dcx, &concrete_bodies, method_trait_def_id, &scope)
        else {
            debug!(bb_idx = dcx.bb_idx, "virtual call: multi-impl dispatch failed");
            return false;
        };

        self.emit_virtual_result(dcx, inline_result, *target);
        true
    }
}

/// Resolve the func operand to a virtual Instance, returning (fn_def, fn_args, vtable_idx).
fn resolve_virtual_instance(
    ctx: &ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
) -> Option<(rustc_public::ty::FnDef, rustc_public::ty::GenericArgs, usize)> {
    let func_ty = dcx.func.ty(ctx.body.locals()).ok()?;
    let (fn_def, fn_args) = match func_ty.kind() {
        TyKind::RigidTy(RigidTy::FnDef(def, args)) => (def, args),
        _ => return None,
    };
    let instance = Instance::resolve(fn_def, &fn_args).ok()?;
    match instance.kind {
        InstanceKind::Virtual { idx } => Some((fn_def, fn_args, idx)),
        _ => None,
    }
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// The vtable discriminant embedded in a wide pointer, if it has one.
    ///
    /// Wave 4 of the address-vs-value conversion: a vtable id is metadata — a
    /// VALUE — so the result is a [`Val`].
    ///
    /// The `bitvec_width() == 2 * POINTER_WIDTH` test that used to be the whole
    /// second branch is deleted. It could not distinguish a real `[vtable|data]`
    /// pair from a thin pointer that `coerce_bitvec_width_safe` had widened into
    /// the same slot, and on the latter it returned the extension padding as a
    /// vtable id. That id is not a discriminant the program ever computed;
    /// downstream it pins `capture_known_vtable_constraint` /
    /// `build_dispatch_ite_chain` to whichever impl carries it, which is a
    /// dispatch decision made from padding. `PtrRepr::into_metadata` answers
    /// `None` for `Thin` and `WidenedThin` alike, so every caller falls through
    /// to its own recovery (source-local table, wrapper peeling, statically
    /// unique vtable) instead.
    ///
    /// The datatype branch is unchanged and is a declared role: the field is
    /// literally named `fld_vtable`.
    pub(in crate::codegen_ay::chc) fn extract_embedded_vtable_expr(
        &self,
        expr: &Expr,
    ) -> Option<Val> {
        if let SortInner::Datatype(dt) = expr.sort().inner()
            && let Some(cons) = dt.constructors.first()
            && cons.has_field("fld_vtable")
        {
            return Some(Val::of_value(expr.clone().field_select(
                &dt.name,
                "fld_vtable",
                Sort::bitvec(POINTER_WIDTH),
            )));
        }

        PtrRepr::classify(expr)?.into_metadata()
    }

    /// Look up the vtable discriminant expression for a local, checking both
    /// the in-memory side table and CHC state variables.
    ///
    /// Part of #3159: Extracted from `try_extract_vtable_discriminant` so
    /// `nested_call.rs` can also access vtable identity for inlined callees.
    pub(in crate::codegen_ay::chc) fn known_vtable_expr_for_local(
        &self,
        local_idx: usize,
    ) -> Option<Expr> {
        let mut current_local = local_idx;
        let mut visited = std::collections::HashSet::from([current_local]);

        for _hop in 0..4 {
            if current_local < self.body.locals().len()
                && let Some(vtable_expr) = self.zst_unique_vtable_expr_for_local(current_local)
            {
                debug!(
                    local_idx,
                    current_local, "virtual dispatch: using statically unique vtable"
                );
                return Some(vtable_expr);
            }

            // Part of #4111: Check CHC state variables FIRST, before the
            // compile-time side table (dyn_vtable_ids). The state variable
            // carries path-sensitive vtable identity through the CHC solver,
            // while dyn_vtable_ids is a plain HashMap that gets overwritten
            // when multiple coercion sites (e.g., if/else returning different
            // concrete types as Box<dyn Trait>) write to the same local.
            // Using the stale side-table value causes the constant-vtable
            // short-circuit in build_dispatch_ite_chain to fire incorrectly,
            // collapsing multi-impl dispatch to a single implementation.
            //
            // Read the input state var unless this block already modified the
            // local's vtable slot. In that case the output name carries the
            // freshly captured value, matching propagate_vtable_discriminant's
            // "read __out when modified in this rule" convention.
            if let Some((in_name, out_name)) = self.vtable_state_vars.get(&current_local) {
                let state_var_name = if self
                    .state_var_index_by_name(in_name)
                    .map(|idx| self.encode.modified_state_indices.contains(&idx))
                    .unwrap_or(false)
                {
                    out_name
                } else {
                    in_name
                };
                debug!(
                    local_idx,
                    current_local,
                    vtable_sv = %state_var_name,
                    "virtual dispatch: using CHC state variable for vtable (#4111)"
                );
                return Some(Expr::var(&**state_var_name, Sort::bitvec(POINTER_WIDTH)));
            }

            // Fall back to compile-time side table only when no CHC state
            // variable exists. This is correct for single-coercion-site cases
            // where the vtable was assigned once in the current block.
            if let Some(vtable_expr) = self.dyn_vtable_ids.get(&current_local) {
                debug!(
                    local_idx,
                    current_local,
                    "virtual dispatch: using stored vtable from dyn_vtable_ids (#3159)"
                );
                return Some(vtable_expr.clone());
            }

            // Guard against out-of-bounds access when the ref-target hop chain
            // crosses body boundaries (e.g., callee-body local indices leaking
            // into the harness body's ref_targets). Part of #3903.
            if current_local >= self.body.locals().len() {
                return None;
            }
            let local_ty = self.body.locals()[current_local].ty;
            if let Some(vtable_id) = self.resolve_unique_wrapped_dyn_vtable_id(local_ty) {
                debug!(
                    local_idx,
                    current_local,
                    vtable_id,
                    "virtual dispatch: recovered vtable from wrapper-typed local"
                );
                return Some(Expr::bitvec_const(vtable_id as u128, POINTER_WIDTH));
            }

            let ref_target = self.ref_resolution.ref_targets.get(&current_local)?;
            if !(ref_target.projections.is_empty()
                || matches!(
                    ref_target.projections.as_slice(),
                    [rustc_public::mir::ProjectionElem::Deref]
                ))
            {
                return None;
            }
            if !visited.insert(ref_target.local) {
                return None;
            }
            debug!(
                local_idx,
                current_local,
                alias_local = ref_target.local,
                "virtual dispatch: following ref_targets for vtable lookup"
            );
            current_local = ref_target.local;
        }

        None
    }

    /// Multi-impl dispatch: inline each body and build an ITE case-split
    /// conditioned on the receiver's vtable discriminant.
    ///
    /// Part of #3159: Option B (Static Dispatch Enumeration).
    fn dispatch_multi_impl_virtual(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        concrete_bodies: &[ResolvedDispatchBody],
        trait_def_id: rustc_span::def_id::DefId,
        scope: &super::dyn_dispatch_scope::DynDispatchScope,
    ) -> Option<InlineReturn> {
        let native_vtable = self.checked_host_receiver_vtable(dcx, Some(trait_def_id));
        // Translate arguments once (shared across all inlined bodies).
        let mut param_exprs = Vec::with_capacity(dcx.args.len());
        for arg in dcx.args {
            param_exprs.push(self.translate_operand_with_modified(arg, dcx.modified_locals)?);
        }

        // Extract vtable discriminant from the receiver (first arg).
        // Part of #3159: pass receiver operand so we can look up its local in
        // dyn_vtable_ids when the receiver sort is BV64 (not Dyn_Trait DT).
        let receiver_local = dcx.args.first().and_then(receiver_base_local);
        let vtable_disc = native_vtable.unwrap_or_else(|| {
            self.try_extract_vtable_discriminant_for_trait(
                &param_exprs,
                receiver_local,
                Some(trait_def_id),
            )
        });

        // Part of #3608: Mark type arrays read by each impl's virtual inline field map.
        for dispatch_body in concrete_bodies {
            self.mark_inline_field_reads(&dispatch_body.body, &param_exprs, dcx.bb_idx);
        }

        populate_inline_self_field_hints(self, dcx);

        // Part of #3226: Delegate to shared ITE chain builder.
        let empty_vtable_ids = std::collections::HashMap::new();
        build_dispatch_ite_chain(
            self,
            concrete_bodies,
            &param_exprs,
            vtable_disc,
            dcx.bb_idx,
            &empty_vtable_ids,
            scope,
        )
    }

    /// Extract the vtable discriminant from the receiver expression.
    ///
    /// Priority order:
    /// 1. If the receiver has a Dyn_* sort with a `fld_vtable` field, extract it.
    /// 2. If the receiver's local has a stored vtable expr in `dyn_vtable_ids`,
    ///    use that (Part of #3159: BV64 locals with side-table vtable tracking).
    /// 3. If the receiver's local has a CHC state variable in `vtable_state_vars`,
    ///    read that (Part of #3159: cross-block path-sensitive vtable tracking).
    /// 4. Fallback: fresh unconstrained symbolic variable (sound over-approximation).
    pub(in crate::codegen_ay::chc) fn try_extract_vtable_discriminant(
        &mut self,
        param_exprs: &[Expr],
        receiver_local: Option<usize>,
    ) -> Expr {
        self.try_extract_vtable_discriminant_for_trait(param_exprs, receiver_local, None)
    }

    pub(in crate::codegen_ay::chc) fn try_extract_vtable_discriminant_for_trait(
        &mut self,
        param_exprs: &[Expr],
        receiver_local: Option<usize>,
        trait_def_id: Option<rustc_span::def_id::DefId>,
    ) -> Expr {
        if let Some(receiver) = param_exprs.first()
            && let Some(vtable_expr) = self.extract_embedded_vtable_expr(receiver)
        {
            return vtable_expr.into_expr();
        }
        // Part of #3159: Look up vtable from side table for BV64 receivers.
        // The vtable expr was captured when the Dyn_Trait RHS was coerced to BV64
        // during assignment, and propagated through Copy/Move.
        if let Some(local_idx) = receiver_local {
            if let Some(vtable_expr) = self.known_vtable_expr_for_local(local_idx) {
                return vtable_expr;
            }
        }
        if let Some(vtable_expr) = self.try_consume_spawn_scheduler_future_vtable_expr(trait_def_id)
        {
            return vtable_expr;
        }
        if let Some(vtable_expr) = self.try_consume_spawn_scheduler_run_vtable_expr() {
            return vtable_expr;
        }
        // Fallback: fresh declared symbolic — solver picks any value (sound).
        // Part of #3447: Record diagnostic — unconstrained vtable discriminant
        // means dispatch will explore all branches (sound over-approximation).
        // `virtual_missing_vtable` is not on the audited list: the recorder
        // counts it fail-closed (`place_translation_drop`), as the two lines
        // this replaced did by hand, and records its site reason.
        let booked = self.record_sound_fallback_reason("virtual_missing_vtable");
        Havoc::booked(booked, super::chc_fresh_name("__vtable_disc"), Sort::bitvec(POINTER_WIDTH))
    }

    /// Part of #3995: Short-circuit Fn/FnMut/FnOnce trait calls to the direct
    /// fn-item body, bypassing the blanket impl shim whose body contains
    /// `(**self)(args)` which the inline walker cannot translate. Mirrors the
    /// nested-call short-circuit in nested_call.rs:466.
    fn try_fn_trait_shortcircuit(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        candidates: &[dyn_coercion::DynCandidate],
        concrete_bodies: &[ResolvedDispatchBody],
        scope: &super::dyn_dispatch_scope::DynDispatchScope,
    ) -> Option<InlineReturn> {
        if !dcx.callee_path.as_deref().is_some_and(is_fn_trait_call) {
            return None;
        }
        // Only candidates whose `Fn*::call` resolved for this signature.
        let candidate_types: Vec<_> = candidates
            .iter()
            .filter(|c| concrete_bodies.iter().any(|b| b.vtable_id == c.vtable_id))
            .map(|c| (c.concrete_ty, c.vtable_id))
            .collect();
        let param_exprs: Option<Vec<Expr>> = dcx
            .args
            .iter()
            .map(|arg| self.translate_operand_with_modified(arg, dcx.modified_locals))
            .collect();
        let param_exprs = param_exprs?;
        let empty_vtable_ids = std::collections::HashMap::new();
        let closure_captures = dcx.args.first().map_or_else(Vec::new, |receiver| {
            self.extract_closure_env_captures(receiver, dcx.modified_locals)
        });
        // Several candidates are merged under their dispatch conditions, which
        // needs the receiver's discriminant (read only then: a one-candidate
        // call walks its body unconditionally, as before).
        //
        // Only the receiver's own vtable sources are read: the generic
        // extraction would also CONSUME the spawn scheduler's next run vtable,
        // which belongs to a later `Future::poll` call, not to this one.
        let sole = candidate_types.len() == 1 && scope.is_sole_runtime(candidate_types[0].1);
        let vtable_disc = (!sole).then(|| {
            let receiver_local = dcx.args.first().and_then(receiver_base_local);
            self.fn_trait_vtable_discriminant(&param_exprs, receiver_local)
        });
        let mut_ref_args =
            dcx.args.get(1).map(|arg| self.host_rustcall_mut_ref_args(arg)).unwrap_or_default();
        let receiver_origin = dcx.args.first().and_then(|arg| self.host_native_dyn_origin(arg));
        let result = try_fn_trait_direct_dispatch(
            self,
            &candidate_types,
            scope,
            vtable_disc.as_ref(),
            &param_exprs,
            receiver_origin.as_ref(),
            &mut_ref_args,
            &closure_captures,
            &empty_vtable_ids,
            0,
        );
        if result.is_some() {
            debug!(
                bb_idx = dcx.bb_idx,
                "virtual call: fn_trait_dispatch short-circuit succeeded (#3995)"
            );
        }
        result
    }

    /// The receiver's vtable discriminant for the Fn-trait short-circuit: the
    /// embedded or tracked vtable, else a fresh value recorded as
    /// `virtual_missing_vtable` (every candidate stays possible), as
    /// [`Self::try_extract_vtable_discriminant_for_trait`] does, but without
    /// consuming the spawn scheduler's vtable model.
    fn fn_trait_vtable_discriminant(
        &mut self,
        param_exprs: &[Expr],
        receiver_local: Option<usize>,
    ) -> Expr {
        if let Some(receiver) = param_exprs.first()
            && let Some(vtable_expr) = self.extract_embedded_vtable_expr(receiver)
        {
            return vtable_expr.into_expr();
        }
        if let Some(vtable_expr) =
            receiver_local.and_then(|local| self.known_vtable_expr_for_local(local))
        {
            return vtable_expr;
        }
        // `virtual_missing_vtable` is not on the audited list: the recorder
        // counts it fail-closed (`place_translation_drop`), as the two lines
        // this replaced did by hand, and records its site reason.
        let booked = self.record_sound_fallback_reason("virtual_missing_vtable");
        Havoc::booked(booked, super::chc_fresh_name("__vtable_disc"), Sort::bitvec(POINTER_WIDTH))
    }

    /// Translate arguments and inline the virtual method body.
    fn translate_and_inline_virtual(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        impl_body: &rustc_public::mir::Body,
    ) -> Option<InlineReturn> {
        let _ = self.checked_host_receiver_vtable(dcx, None);
        let mut param_exprs = Vec::with_capacity(dcx.args.len());
        for arg in dcx.args {
            param_exprs.push(self.translate_operand_with_modified(arg, dcx.modified_locals)?);
        }
        // Part of #3608: Mark type arrays read by the virtual inline's field map
        // so they survive post-codegen pruning and are threaded through predicates.
        self.mark_inline_field_reads(impl_body, &param_exprs, dcx.bb_idx);
        populate_inline_self_field_hints(self, dcx);
        let empty_vtable_ids = std::collections::HashMap::new();
        // F2 (inline_walk_guard.rs): the dyn door binds raw operand terms.
        self.inline_walk_param_address_seeds =
            Some(super::inline_walk_guard::dyn_door_address_seeds(self, impl_body, &param_exprs));
        let result = translate_virtual_body_inline(
            self,
            impl_body,
            &param_exprs,
            dcx.bb_idx,
            &empty_vtable_ids,
            None,
            0,
        );
        self.inline_walk_param_address_seeds = None;
        result
    }

    /// A unique native coercion retains its vtable through the compiler's
    /// actual Box cast and payload reborrow. Selecting its real arm avoids
    /// publishing approximations from an unreachable implementation. Recheck
    /// current allocation metadata here, before any field-value shortcut.
    fn checked_host_receiver_vtable(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        expected_trait: Option<rustc_span::def_id::DefId>,
    ) -> Option<Expr> {
        let origin = self.host_native_dyn_receiver_origin(dcx.args.first()?)?;
        if let Some(expected) = expected_trait {
            let principal = origin.dynamic.kind().trait_principal()?;
            let actual = rustc_public::rustc_internal::internal(
                self.tcx,
                rustc_public::CrateDef::def_id(&principal.value.def_id),
            );
            if actual != expected {
                self.record_sound_fallback_reason(
                    super::dyn_dispatch_scope::DYN_PRINCIPAL_MISMATCH,
                );
                return None;
            }
        }
        let address =
            Expr::bitvec_const(origin.allocation, 32).concat(Expr::bitvec_const(0u32, 32));
        let Some(checked) = self.checked_native_dyn_pointer(address, &origin) else {
            self.record_sound_fallback_reason("box_deref_validity_unmodeled");
            return None;
        };
        self.heap_state.pending_checks.extend(checked.checks);
        Some(origin.vtable_expr())
    }

    /// Emit the CHC rule constraining the destination to the virtual call result.
    ///
    /// Part of #3173: check for flattened destination first — if the destination
    /// local is flattened into N state var slots, decompose the result and
    /// constrain all slots (not just fld0 via resolve_destination).
    fn emit_virtual_result(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        inline_result: InlineReturn,
        target: usize,
    ) {
        let dest_local: usize = dcx.destination.local;
        let InlineReturn { value: result_expr, vtable, alias_updates, deferred_checks, .. } =
            inline_result;
        // Assert-guard SIDE-CHANNEL host emission (see emit_deferred_inline_check_errors).
        self.emit_deferred_inline_check_errors(dcx, deferred_checks);
        let (result_expr, extra_constraints) = self.take_inline_result_guards(dcx, result_expr);
        let result_expr =
            widen_inline_result_for_fat_pointer(self, dest_local, result_expr, &vtable);
        let empty_pre_resolved = std::collections::BTreeMap::new();
        let prepared = prepare_inline_result_epilogue(
            self,
            InlineResultEpilogueSpec {
                dcx,
                target,
                dest_local,
                result_expr,
                inline_vtable: vtable,
                fallback_vtable: None,
                alias_updates: &alias_updates,
                pre_resolved_args: &empty_pre_resolved,
                eq_reason: "codegen_call_virtual",
                alias_reason: "virtual_alias_update",
                extra_constraints,
                extra_dests: Vec::new(),
                drain_pending_updates: true,
                drain_pending_checks: true,
            },
        );

        if let Err(prepared) = emit_prepared_inline_result(self, prepared) {
            // Part of #3897: sound over-approximation for untracked destinations.
            // Previously used `false` which killed the transition — dest is now
            // unconstrained (sound over-approximation).
            debug!(
                bb_idx = dcx.bb_idx,
                dest_local,
                fn_name = %self.fn_name,
                "virtual: untracked destination, sound over-approx"
            );
            self.record_sound_fallback_reason("virtual_dest_untracked");
            let effective_stmts = prepared.effective_stmts().to_vec();
            let new_output_args =
                self.build_output_args(dcx.modified_locals, &prepared.extra_dests);
            self.emit_goto_rule_extra(
                dcx.from_app,
                target,
                &new_output_args,
                &effective_stmts,
                prepared.extra_constraints.into_iter().chain(prepared.mem_constraints),
            );
        }
        debug!(bb_idx = dcx.bb_idx, dest_local, "virtual call: devirtualized and constrained");
    }
}
// Utility methods (build_local_update_constraints, mark_inline_field_reads,
// resolve_parent_trait_def_id, spawn scheduler vtable) moved to
// codegen_call_virtual_utils.rs per #4206.
