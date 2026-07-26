// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! General-purpose function call inlining for CHC codegen.
//!
//! When a function call falls through all specialized dispatchers (kani hooks,
//! stubs, closures, virtual calls), this handler attempts to resolve the callee
//! to a concrete Instance, retrieve its MIR body, and inline the body using the
//! same translation infrastructure as the virtual call inliner.
//!
//! This catches many simple stdlib functions (e.g., `needs_drop`, `ManuallyDrop::drop`,
//! `IndexRange::zero_to`, array iterator internals) that would otherwise fall
//! through to the unconstrained fallback, causing false CTREX.
//!
//! Part of #3173: batch fix for zero-pass Kani regression categories.
//!
//! Sub-modules:
//! - `codegen_call_fn_inline_specialization`: any_where dispatch, copy-swap, captures
//! - `codegen_call_fn_inline_emit`: result emission, assert guards, fat-pointer widening

use ay_bindings::{Expr, ExprValue, Sort};
use rustc_public::CrateDef;
use rustc_public::mir::mono::{Instance, InstanceKind};
use rustc_public::mir::{Operand, TerminatorKind};
use rustc_public::rustc_internal;
use rustc_public::ty::{GenericArgKind, RigidTy, Ty, TyKind};
use std::collections::{BTreeMap, HashMap, HashSet};
use tracing::debug;

use crate::codegen_ay::shared::count_effective_blocks;
use crate::codegen_ay::types::POINTER_WIDTH;

use super::ChcCtx;
use super::chc_call_context::DispatchCallContext;
use super::codegen_call_misc::CallMisc;
use super::codegen_call_ptr_identity::trace_pointer_identity_ref_target;
use super::codegen_ctx::globals::chc_fresh_name;
use super::inline_alias_writeback::pre_resolve_arg_target_locals;
use super::inline_body::{InlineReturn, translate_inline_body};
use super::inline_bool_return::try_inline_simple_bool_return_helper;
use super::inline_budget::chc_inline_effective_block_limit;
use super::inline_field_map::populate_inline_self_field_hints;
use super::inline_known_calls::inline_known_call_expr_for_callee_path;
fn callee_uses_special_arithmetic_handler(callee_name: &str, last_seg: &str) -> bool {
    let is_primitive_impl =
        callee_name.starts_with("core::num::<impl ") || callee_name.starts_with("std::num::<impl ");

    if !is_primitive_impl {
        return false;
    }

    matches!(
        last_seg,
        "unchecked_add"
            | "unchecked_sub"
            | "unchecked_mul"
            | "unchecked_div"
            | "unchecked_rem"
            | "unchecked_shl"
            | "unchecked_shr"
            | "checked_shl"
            | "checked_shr"
    )
}

fn is_raw_ptr_from_raw_parts_inline_path(path: &str) -> bool {
    path.contains("from_raw_parts") && path.contains("ptr") && !path.contains("NonNull")
}

fn raw_ptr_from_raw_parts_inline_vtable(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    dest_local: usize,
    metadata: Option<Expr>,
) -> Option<Expr> {
    let metadata = metadata?;
    let metadata_is_dyn = dcx
        .args
        .get(1)
        .and_then(|arg| arg.ty(ctx.body.locals()).ok())
        .is_some_and(ty_mentions_dyn_trait);

    let dest_is_dyn = {
        let dest_ty = ctx.resolve_body_ty(ctx.body.locals()[dest_local].ty);
        let pointee = match dest_ty.kind() {
            TyKind::RigidTy(RigidTy::RawPtr(pointee, _))
            | TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) => Some(pointee),
            _ => None,
        };
        pointee
            .map(|pointee| ctx.resolve_body_ty(pointee))
            .and_then(|pointee| super::dyn_coercion::find_dyn_trait_tail_ty(ctx, pointee))
            .is_some()
    };
    debug!(
        dest_local,
        dest_is_dyn, metadata_is_dyn, "fn_inline: raw ptr from_raw_parts metadata classification"
    );
    (dest_is_dyn || metadata_is_dyn).then_some(metadata)
}

fn ty_mentions_dyn_trait(ty: Ty) -> bool {
    if matches!(ty.kind(), TyKind::RigidTy(RigidTy::Dynamic(..))) {
        return true;
    }

    match ty.kind() {
        TyKind::RigidTy(RigidTy::Ref(_, inner, _))
        | TyKind::RigidTy(RigidTy::RawPtr(inner, _))
        | TyKind::RigidTy(RigidTy::Slice(inner))
        | TyKind::RigidTy(RigidTy::Array(inner, _)) => ty_mentions_dyn_trait(inner),
        TyKind::RigidTy(RigidTy::Adt(_, args)) => args.0.iter().any(|arg| match arg {
            GenericArgKind::Type(inner) => ty_mentions_dyn_trait(*inner),
            _ => false,
        }),
        TyKind::RigidTy(RigidTy::Tuple(fields)) => {
            fields.iter().any(|field| ty_mentions_dyn_trait(*field))
        }
        _ => false,
    }
}

fn propagate_raw_ptr_from_raw_parts_inline_identity(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    data_expr: &Expr,
) {
    let dest_local = dcx.destination.local;
    let src_local = dcx.args.first().and_then(|arg| match arg {
        Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
            Some(place.local)
        }
        _ => None,
    });

    if let Some(obj_id) = src_local
        .and_then(|src| ctx.known_alloc_ids.get(&src).copied())
        .or_else(|| src_local.and_then(|src| ctx.trace_deref_store_alloc_id(src)))
        .or_else(|| ChcCtx::try_extract_obj_id(data_expr))
    {
        ctx.known_alloc_ids.insert(dest_local, obj_id);
    }

    if let Some(ref_target) = src_local
        .and_then(|src| ctx.ref_resolution.ref_targets.get(&src).cloned())
        .or_else(|| src_local.and_then(|src| trace_pointer_identity_ref_target(ctx, src)))
        .or_else(|| {
            ChcCtx::try_extract_obj_id(data_expr).and_then(|obj_id| {
                ctx.heap_state.local_idx_for_obj_id(obj_id).map(|local| {
                    super::codegen_ctx::types::RefTarget::with_projections(local, vec![])
                })
            })
        })
    {
        ctx.ref_resolution.ref_targets.insert(dest_local, ref_target);
        ctx.ref_resolution.call_forwarded_raw_ptrs.insert(dest_local);
    }
}

fn pointer_constant_byte_delta(expr: &Expr) -> Option<usize> {
    if let Some((_, byte_offset)) = ChcCtx::try_extract_constant_addr(expr) {
        return Some(byte_offset as usize);
    }

    match expr.value() {
        ExprValue::BvConcat(_, low) => bvadd_constant_delta(low),
        ExprValue::BvExtract { expr: inner, high: 63, low: 0 } => {
            pointer_constant_byte_delta(inner)
        }
        _ => bvadd_constant_delta(expr),
    }
}

fn bvadd_constant_delta(expr: &Expr) -> Option<usize> {
    let ExprValue::BvAdd(lhs, rhs) = expr.value() else {
        return None;
    };
    const_usize_after_eval(rhs).or_else(|| const_usize_after_eval(lhs))
}

fn const_usize_after_eval(expr: &Expr) -> Option<usize> {
    ChcCtx::const_usize_from_expr(expr).or_else(|| {
        trust_mc_core::chc_const_prop::eval::try_eval_to_const(expr)
            .and_then(|folded| ChcCtx::const_usize_from_expr(&folded))
    })
}

fn slice_from_raw_parts_elem_size(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    backing_local: usize,
) -> Option<usize> {
    let backing_ty = ctx.resolve_body_ty(ctx.body.locals()[backing_local].ty);
    ctx.get_array_element_ty(backing_ty).and_then(|elem_ty| ctx.get_type_size(elem_ty)).or_else(
        || {
            let arg_ty = ctx.resolve_body_ty(dcx.args.first()?.ty(ctx.body.locals()).ok()?);
            let pointee_ty = match arg_ty.kind() {
                TyKind::RigidTy(RigidTy::Ref(_, inner, _))
                | TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => ctx.resolve_body_ty(inner),
                _ => return None,
            };
            ctx.get_type_size(pointee_ty)
        },
    )
}

fn pointer_add_element_delta_for_local(
    ctx: &mut ChcCtx<'_, '_>,
    local: usize,
    modified_locals: &std::collections::HashSet<usize>,
) -> Option<usize> {
    for block in &ctx.body.blocks {
        let TerminatorKind::Call { func, args, destination, .. } = &block.terminator.kind else {
            continue;
        };
        if destination.local != local || !destination.projection.is_empty() {
            continue;
        }
        let callee = ctx.resolve_callee_path(func).or_else(|| ctx.resolve_fn_def_name(func))?;
        let is_ptr_add = callee.contains("::add") || callee.ends_with("::offset");
        if !is_ptr_add {
            continue;
        }
        let delta_expr = ctx.translate_operand_with_modified(args.get(1)?, modified_locals)?;
        return ChcCtx::const_usize_from_expr(&delta_expr);
    }
    None
}

// Re-export public items from sub-modules for existing consumers.
pub(in crate::codegen_ay::chc) use super::codegen_call_fn_inline_emit::widen_inline_result_for_fat_pointer;

pub(in crate::codegen_ay::chc) trait CallDispatchFnInline {
    fn try_dispatch_call_fn_inline(&mut self, dcx: &DispatchCallContext<'_>) -> bool;
}

impl<'tcx, 'body> CallDispatchFnInline for ChcCtx<'tcx, 'body> {
    fn try_dispatch_call_fn_inline(&mut self, dcx: &DispatchCallContext<'_>) -> bool {
        let Some(target) = dcx.target else { return false };
        if self.try_dispatch_call_any_where(dcx, *target) {
            return true;
        }
        // Resolve the callee to a concrete Instance.
        let func_ty = match dcx.func.ty(self.body.locals()) {
            Ok(ty) => ty,
            Err(_) => return false,
        };
        let (fn_def, fn_substs) = match func_ty.kind() {
            TyKind::RigidTy(RigidTy::FnDef(def, substs)) => (def, substs),
            _ => return false,
        };
        let instance = match Instance::resolve(fn_def, &fn_substs) {
            Ok(inst) => inst,
            Err(_) => return false,
        };

        // Skip virtual calls — those are handled by the virtual dispatch handler.
        if matches!(instance.kind, InstanceKind::Virtual { .. }) {
            return false;
        }

        // Get the TRANSFORMED MIR body (contract mode dispatch, stubs,
        // rewrites) — raw `instance.body()` bypasses the kani_middle transform
        // pipeline and leaves walked contract checks vacuous (mode dummy 0).
        let callee_name =
            self.tcx.def_path_str(rustc_internal::internal(self.tcx, instance.def.def_id()));
        let body = match crate::kani_middle::transform::walker_transformed_body(self.tcx, instance)
        {
            Some(b) => b,
            None => {
                debug!(
                    %callee_name,
                    fn_name = %self.fn_name,
                    "fn_inline: no body"
                );
                return false;
            }
        };
        // Kani parity fail-close: a contracted RECURSIVE fn without
        // #[kani::recursion] is a Kani-level verification FAILURE (its reentry
        // tracker assert fires). The walk applies replace-style semantics to
        // inner self-calls unconditionally, which silently erases that failure
        // (fail_missing_recursion_attr false-proved at the v24 gate once the
        // transformed-body keystone made the walked chain cleanly provable).
        // Demote so any PROOF verdict becomes FAILURE.
        if contract_recursion_unannotated(self.tcx, instance, &body) {
            debug!(
                %callee_name,
                fn_name = %self.fn_name,
                "fn_inline: contracted recursive callee lacks #[kani::recursion] — demoting (fail-closed)"
            );
            self.record_fallback();
        }
        // Soundness: unchecked arithmetic (unchecked_add/sub/mul) wrappers in
        // core::num have MIR bodies containing assert_unsafe_precondition! UB checks.
        // The inline walker records those Assert terminators as ite-fallback guards
        // (execution_state.rs:82-92) instead of error() rules, so overflow is NOT
        // detected — producing false PROOF. Block these from fn_inline so they fall
        // through to codegen_wrapping_arithmetic (step_wrapping.rs:238) which emits
        // correct error() rules for overflow detection. Mirrors Kani's MIR-level
        // FunctionInlinePass::has_special_codegen_handler (inline/mod.rs:269).
        //
        // Part of #3768: Also block checked_shl/checked_shr. fn_inline produces a
        // Datatype(Option_u32) result that cannot be decomposed by
        // decompose_datatype_for_flattened_dest (not an ITE of constructors),
        // causing flatten_dest_sort_mismatch. The codegen_checked_arithmetic handler
        // in step_wrapping.rs properly decomposes the Option<T> result into
        // flattened (overflow_flag, result) fields.
        {
            let last_seg = callee_name.rsplit("::").next().unwrap_or("");
            if callee_uses_special_arithmetic_handler(&callee_name, last_seg) {
                debug!(
                    %callee_name,
                    fn_name = %self.fn_name,
                    "fn_inline: skip arithmetic with specialized handler"
                );
                return false;
            }
        }

        // Part of #3875: SpecArrayEq::spec_eq body uses loop-based slice comparison
        // that the inline walker can't handle. Reject early so it falls through to
        // tail_dispatch which produces correct element-wise array comparison.
        if callee_name.contains("SpecArrayEq") && callee_name.contains("spec_eq") {
            self.inline_self_field_hints = None;
            return false;
        }
        if self.try_dispatch_copy_swap_body(dcx, &body, &callee_name) {
            self.inline_self_field_hints = None;
            return true;
        }

        // Part of #3830: Pre-populate field hints before arg translation.
        populate_inline_self_field_hints(self, dcx);
        // Translate arguments (needed by known-call fast path AND body walk).
        let mut params: Vec<Expr> = Vec::with_capacity(dcx.args.len());
        let mut used_self_placeholder = false;
        for (i, arg) in dcx.args.iter().enumerate() {
            if let Some(expr) = self.translate_call_arg_for_inline(arg, dcx.modified_locals) {
                // Part of #55 piece 4: when the translated arg is symbolic
                // (host state var — e.g. the MIR inliner folded the callee's
                // first level into the harness, leaving checked-arithmetic
                // results in relation state), try a FAIL-CLOSED unique-def
                // walk of the host MIR to recover an exact literal. A literal
                // param is what lets the walker's switchInt fold + const-arg
                // depth relief unroll concrete recursion (fib/fac/hanoi).
                //
                // The recovered literal only replaces the translated operand
                // when it agrees in SORT. A reference operand (e.g. `&Some(4)`)
                // resolves via `resolve_ref_or_const_referent` to its referent
                // VALUE (an `Option<u8>` datatype), but a unique-def walk of the
                // same operand evaluates it to the referent's POINTER ADDRESS (a
                // BV64 const) — a valid constant of the wrong sort. Accepting it
                // would clobber the datatype referent with a pointer, which the
                // callee then mis-decodes (e.g. `Some(4)` read as `None` because
                // the address bits unflatten with the enum tag at the wrong bit).
                // The sort guard keeps the scalar recursion-folding win while
                // preserving referent values for derived `PartialEq::eq` inlines.
                let expr = if trust_mc_core::chc_const_prop::eval::try_eval_to_const(&expr)
                    .is_none()
                {
                    match self.unique_def_const_operand(arg, 32) {
                        Some(lit) if lit.sort() == expr.sort() => lit,
                        _ => expr,
                    }
                } else {
                    expr
                };
                params.push(expr);
            } else if i == 0 && self.inline_self_field_hints.is_some() {
                // Fresh symbolic BV64 avoids obj_valid[0] collision (W3:4021).
                let placeholder_name = chc_fresh_name("inline_self_placeholder");
                let placeholder_var = Expr::var(&placeholder_name, Sort::bitvec(POINTER_WIDTH));
                debug!(fn_name = %self.fn_name, %callee_name, %placeholder_name, "fn_inline: placeholder");
                used_self_placeholder = true;
                params.push(placeholder_var);
            } else {
                debug!(i, fn_name = %self.fn_name, %callee_name, "fn_inline: skip (arg)");
                self.inline_self_field_hints = None;
                return false;
            }
        }

        // Part of #3159: Build caller_vtable_ids from dyn_vtable_ids.
        let mut caller_vtable_ids = HashMap::new();
        // Part of #4166: Build caller_subslice_lens/offsets for fat pointer
        // metadata propagation through inline parameter binding. Without this,
        // inlined functions lose subslice_len metadata for fat pointer args,
        // causing translate_ptr_metadata to return None and raw pointer
        // comparisons to treat fat pointers as thin pointers.
        let mut caller_subslice_lens: HashMap<usize, Expr> = HashMap::new();
        let mut caller_subslice_offsets: HashMap<usize, Expr> = HashMap::new();
        for (i, arg) in dcx.args.iter().enumerate() {
            let arg_local = match arg {
                Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => Some(p.local),
                _ => None,
            };
            if let Some(local_idx) = arg_local {
                if let Some(vtable) = self.known_vtable_expr_for_local(local_idx) {
                    caller_vtable_ids.insert(i + 1, vtable);
                }
                // Part of #4166: Propagate subslice_len/offset from caller arg
                // locals to callee parameter locals (i+1 = MIR arg numbering).
                if let Some(len_expr) = self.ref_resolution.subslice_len.get(&local_idx) {
                    caller_subslice_lens.insert(i + 1, len_expr.clone());
                }
                if let Some(off_expr) = self.ref_resolution.subslice_offset.get(&local_idx) {
                    caller_subslice_offsets.insert(i + 1, off_expr.clone());
                }
            } else if let std::collections::hash_map::Entry::Vacant(entry) =
                caller_vtable_ids.entry(i + 1)
            {
                // Part of #4225: For projected operands (e.g., `&outer.inner`
                // where `inner: dyn Trait`), the local has projections so
                // `known_vtable_expr_for_local` cannot be called. Fall back to
                // type-based vtable resolution using the argument's type.
                if let Ok(arg_ty) = arg.ty(self.body.locals()) {
                    if let Some(vtable_id) = self.resolve_unique_wrapped_dyn_vtable_id(arg_ty) {
                        debug!(
                            i,
                            vtable_id,
                            fn_name = %self.fn_name,
                            "fn_inline: recovered vtable from projected arg type (#4225)"
                        );
                        entry.insert(Expr::bitvec_const(vtable_id as u128, POINTER_WIDTH));
                    }
                }
            }
        }

        let direct_callee_path = dcx
            .callee_path
            .clone()
            .or_else(|| self.resolve_callee_path(dcx.func))
            .or_else(|| self.resolve_fn_def_name(dcx.func));
        let instance_callee_path = {
            let internal_def_id = rustc_internal::internal(self.tcx, instance.def.def_id());
            self.tcx.def_path_str(internal_def_id)
        };
        // Part of #3875: Try known-call fast paths BEFORE the body size limit.
        // Pure expression handlers (SpecArrayEq::spec_eq, float predicates, etc.)
        // don't need the body — they encode the result directly from the callee
        // path and translated args. Checking them after the size limit would
        // cause false fallbacks for stdlib functions with loop bodies.
        let pure_fast_path = if used_self_placeholder {
            None // placeholder can't be used by known-call fast paths
        } else {
            direct_callee_path
                .as_deref()
                .and_then(|path| {
                    inline_known_call_expr_for_callee_path(
                        self,
                        dcx.func,
                        path,
                        &params,
                        dcx.args.first(),
                        self.body.locals(),
                    )
                })
                .or_else(|| {
                    if direct_callee_path.as_deref() == Some(instance_callee_path.as_str()) {
                        None
                    } else {
                        inline_known_call_expr_for_callee_path(
                            self,
                            dcx.func,
                            &instance_callee_path,
                            &params,
                            dcx.args.first(),
                            self.body.locals(),
                        )
                    }
                })
        };
        let callee_path = direct_callee_path.or_else(|| Some(instance_callee_path.clone()));
        // Part of #3936 D4: Pre-resolve all arg target locals before inline
        // translation. The walker modifies `ref_resolution` for callee-local
        // bookkeeping, so resolving after the walk can lose caller-side
        // temp-ref mappings.
        let pre_resolved_args = pre_resolve_arg_target_locals(self, dcx);

        if let Some(ref path) = callee_path
            && is_raw_ptr_from_raw_parts_inline_path(path)
            && let Some(data_expr) = params.first().cloned()
            && let Some(inline_vtable) = raw_ptr_from_raw_parts_inline_vtable(
                self,
                dcx,
                dcx.destination.local,
                params.get(1).cloned(),
            )
        {
            propagate_raw_ptr_from_raw_parts_inline_identity(self, dcx, &data_expr);
            debug!(
                bb_idx = dcx.bb_idx,
                %path,
                "fn_inline: raw ptr from_raw_parts fast path"
            );
            return self.emit_translated_inline_call_result(
                dcx,
                *target,
                data_expr,
                Some(inline_vtable),
                BTreeMap::new(),
                Vec::new(),
                &pre_resolved_args,
                &caller_vtable_ids,
                callee_path.as_deref(),
                "codegen_call_fn_inline_raw_ptr_from_raw_parts",
                "fn_inline_raw_ptr_from_raw_parts_alias_update",
            );
        }

        // Part of #4053: Known-call fast paths (e.g., option_unwrap_value) may
        // produce DT field_select expressions for sorts not in state variables.
        // Declare both the result sort and receiver/arg sorts so the SMT preamble
        // includes the DT declarations needed by field_select accessors.
        if pure_fast_path.is_some() {
            for arg in &params {
                self.declare_datatype_sort_if_needed(arg.sort());
            }
        }
        let (result_expr, inline_vtable, alias_updates, deferred_checks, used_pure_fast_path) =
            if let Some(expr) = pure_fast_path {
                (expr, None, std::collections::BTreeMap::new(), Vec::new(), true)
            } else if let Some(expr) =
                try_inline_simple_bool_return_helper(self, &body, &params, callee_path.as_deref())
            {
                (expr, None, std::collections::BTreeMap::new(), Vec::new(), true)
            } else {
                // Part of #3875: Skip body inline for SpecArrayEq::spec_eq.
                // The body of spec_eq uses BinOp::Eq on arrays, which produces full
                // SMT extensional equality (forall i. select(a,i)==select(b,i)) including
                // uninitialized indices beyond N. Fall through to tail_dispatch which
                // does element-wise comparison over 0..N only.
                if let Some(ref path) = callee_path
                    && path.contains("SpecArrayEq")
                    && path.contains("spec_eq")
                {
                    self.inline_self_field_hints = None;
                    return false;
                }
                // Limit complexity: only inline functions with a manageable number of blocks.
                // Moved after known-call fast path (Part of #3875) — pure handlers
                // don't walk the body, so size doesn't matter for them.
                let effective = count_effective_blocks(&body);
                let limit = chc_inline_effective_block_limit(&body, effective);
                if effective > limit {
                    debug!(%callee_name, fn_name = %self.fn_name, effective, limit, "fn_inline: skip (size)");
                    self.inline_self_field_hints = None;
                    return false;
                }
                // Part of #3608: Mark type arrays read by the inline field map.
                self.mark_inline_field_reads(&body, &params, dcx.bb_idx);
                // Part of #4166: Seed subslice_len/offset into ref_resolution
                // for callee parameter locals before the inline walk. fn_inline
                // keeps this save/restore local instead of delegating to
                // translate_inline_body_with_metadata because it also needs to
                // read callee return-local metadata before restoring the caller
                // maps.
                let local_count = body.locals().len();
                let saved_lens: Vec<(usize, Option<Expr>)> = (0..local_count)
                    .map(|local| (local, self.ref_resolution.subslice_len.get(&local).cloned()))
                    .collect();
                let saved_offs: Vec<(usize, Option<Expr>)> = (0..local_count)
                    .map(|local| (local, self.ref_resolution.subslice_offset.get(&local).cloned()))
                    .collect();
                for (callee_local, len_expr) in &caller_subslice_lens {
                    self.ref_resolution.subslice_len.insert(*callee_local, len_expr.clone());
                }
                for (callee_local, off_expr) in &caller_subslice_offsets {
                    self.ref_resolution.subslice_offset.insert(*callee_local, off_expr.clone());
                }
                // Part of #4185: Snapshot heap state before speculative inline walk.
                // If the walk bails (returns None), orphaned heap mutations from
                // partial translation (build_memory_store, pending_updates) must be
                // rolled back to prevent false proofs from leaked constraints.
                let heap_snapshot = self.heap_state.snapshot_transient_rule_state();
                // Part of #4185 Fix 4: Snapshot modified_state_indices alongside heap.
                // On bail-out, leaked indices cause unconstrained state vars in output.
                let modified_snapshot = self.encode.modified_state_indices.clone();
                // Try inline translation.
                let result = translate_inline_body(
                    self,
                    &body,
                    &params,
                    dcx.bb_idx,
                    &caller_vtable_ids,
                    Some(instance),
                    0,
                );
                // Part of #4163: Propagate subslice_len from the inlined
                // function's return local (0) to the caller's destination.
                // The inline walker may have seeded subslice_len[0] via
                // nested call to slice_from_raw_parts and Copy/Cast chains.
                // Part of #4163 D0: Capture return-local metadata BEFORE restore,
                // but insert into caller dest AFTER restore. Without this ordering,
                // the restore loop wipes dest when dest < callee_local_count.
                let return_len = self.ref_resolution.subslice_len.get(&0).cloned();
                let return_offset = self.ref_resolution.subslice_offset.get(&0).cloned();
                // Part of #4166: Restore ref_resolution to pre-seed state.
                for (k, saved) in saved_lens {
                    match saved {
                        Some(v) => {
                            self.ref_resolution.subslice_len.insert(k, v);
                        }
                        None => {
                            self.ref_resolution.subslice_len.remove(&k);
                        }
                    }
                }
                for (k, saved) in saved_offs {
                    match saved {
                        Some(v) => {
                            self.ref_resolution.subslice_offset.insert(k, v);
                        }
                        None => {
                            self.ref_resolution.subslice_offset.remove(&k);
                        }
                    }
                }
                // Now insert captured return metadata into caller dest (survives restore).
                if let Some(ref len) = return_len {
                    let dest = dcx.destination.local;
                    self.ref_resolution.subslice_len.insert(dest, len.clone());
                    debug!(
                        dest,
                        "fn_inline: propagated subslice_len from return local to caller dest"
                    );
                }
                if let Some(offset) = return_offset {
                    let dest = dcx.destination.local;
                    self.ref_resolution.subslice_offset.insert(dest, offset);
                    debug!(
                        dest,
                        "fn_inline: propagated subslice_offset from return local to caller dest"
                    );
                }
                let Some(inline_result) = result else {
                    self.inline_self_field_hints = None;
                    // Part of #4185: Restore heap state after failed inline walk.
                    // The walk may have partially executed build_memory_store() or
                    // pushed to pending_updates/pending_checks before bailing.
                    self.heap_state.restore_transient_rule_state(&heap_snapshot);
                    // Part of #4185 Fix 4: Restore modified_state_indices to prevent
                    // unconstrained state vars leaking into CHC rule output signature.
                    self.encode.modified_state_indices = modified_snapshot;
                    // Raw-alloc route: a bailed `slice::from_raw_parts` inline
                    // skips the uninit-formation check emitted on the success
                    // path below — fail-close so a PROOF cannot rest on the
                    // missing check (whatever handler picks the call up next).
                    if self.uninit_checks
                        && callee_path.as_deref().is_some_and(
                            super::codegen_call_kani_model_mem_init::is_slice_from_raw_parts_ref_former,
                        )
                    {
                        self.record_sound_fallback_reason("from_raw_parts_uninit_inline_bail");
                    }
                    debug!(fn_name = %self.fn_name, %callee_name, effective, "fn_inline: skip (body)");
                    return false;
                };
                let InlineReturn { value, vtable, alias_updates, deferred_checks, .. } =
                    inline_result;
                (value, vtable, alias_updates, deferred_checks, false)
            };
        self.inline_self_field_hints = None;

        // Part of #4163: Seed subslice_len on the caller's destination local
        // when the inlined function is slice_from_raw_parts{_mut} or
        // from_raw_parts{_mut}. These functions produce fat pointers whose
        // length metadata (second arg) must be tracked for downstream
        // PtrMetadata / size_of_val resolution.
        if let Some(ref path) = callee_path {
            // Raw-alloc route: `slice::from_raw_parts{,_mut}` FORMS a
            // reference (`&*slice_from_raw_parts(data, len)`), which under
            // `-Z uninit-checks` reads all `len` elements — emit the
            // shadow-model uninit-formation check (fail-closed inside the
            // helper; untranslatable shapes demote). The raw-pointer
            // constructors (`ptr::slice_from_raw_parts`,
            // `ptr::from_raw_parts`) create a pointer without reading and
            // need no check.
            if self.uninit_checks
                && super::codegen_call_kani_model_mem_init::is_slice_from_raw_parts_ref_former(path)
            {
                if params.len() >= 2 {
                    let (data, len) = (params[0].clone(), params[1].clone());
                    self.emit_slice_from_raw_parts_uninit_check(dcx, &data, &len);
                } else {
                    self.record_sound_fallback_reason("from_raw_parts_uninit_args_untranslatable");
                }
            }
            let is_slice_from_raw = path.contains("slice_from_raw_parts")
                || (path.contains("from_raw_parts") && path.contains("ptr"));
            if is_slice_from_raw && params.len() >= 2 {
                let dest = dcx.destination.local;
                self.ref_resolution.subslice_len.insert(dest, params[1].clone());
                if let Some(src_local) = dcx.args.first().and_then(|arg| match arg {
                    Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                        Some(place.local)
                    }
                    _ => None,
                }) {
                    let resolved = self.resolve_provenance_local(src_local);
                    let stack_local = ChcCtx::try_extract_obj_id(&params[0])
                        .and_then(|obj_id| self.heap_state.local_idx_for_obj_id(obj_id));
                    let ref_target = self
                        .ref_resolution
                        .ref_targets
                        .get(&src_local)
                        .cloned()
                        .or_else(|| trace_pointer_identity_ref_target(self, src_local));
                    let backing_local = ref_target
                        .as_ref()
                        .map(|target| target.local)
                        .or(stack_local)
                        .unwrap_or(resolved);

                    let data = [
                        self.ref_resolution.const_ref_values.get(&backing_local),
                        self.ref_resolution.const_ref_values.get(&resolved),
                        self.ref_resolution.const_ref_values.get(&src_local),
                    ]
                    .into_iter()
                    .flatten()
                    .find(|expr| expr.sort().array_sort().is_some())
                    .or_else(|| {
                        [
                            self.ref_resolution.const_ref_values.get(&backing_local),
                            self.ref_resolution.const_ref_values.get(&resolved),
                            self.ref_resolution.const_ref_values.get(&src_local),
                        ]
                        .into_iter()
                        .flatten()
                        .next()
                    })
                    .cloned();
                    if let Some(data) = data {
                        self.ref_resolution.const_ref_values.insert(dest, data);
                    }
                    let existing_offset = self
                        .ref_resolution
                        .subslice_offset
                        .get(&src_local)
                        .or_else(|| self.ref_resolution.subslice_offset.get(&resolved))
                        .cloned();
                    if existing_offset
                        .as_ref()
                        .is_some_and(|offset| !ChcCtx::is_zero_pointer_width_bitvec(offset))
                    {
                        self.ref_resolution
                            .subslice_offset
                            .insert(dest, existing_offset.expect("checked Some above"));
                    } else if let Some(byte_offset) = pointer_constant_byte_delta(&params[0])
                        && let Some(elem_size) =
                            slice_from_raw_parts_elem_size(self, dcx, backing_local)
                        && elem_size != 0
                        && byte_offset % elem_size == 0
                    {
                        self.ref_resolution.subslice_offset.insert(
                            dest,
                            Expr::bitvec_const((byte_offset / elem_size) as u128, POINTER_WIDTH),
                        );
                    } else if let Some(delta) =
                        pointer_add_element_delta_for_local(self, src_local, dcx.modified_locals)
                    {
                        self.ref_resolution
                            .subslice_offset
                            .insert(dest, Expr::bitvec_const(delta as u128, POINTER_WIDTH));
                    } else if let Some(offset) = existing_offset {
                        self.ref_resolution.subslice_offset.insert(dest, offset);
                    }
                    if let Some(target) = ref_target {
                        self.ref_resolution.ref_targets.insert(dest, target);
                        self.ref_resolution.call_forwarded_raw_ptrs.insert(dest);
                    }
                }
                debug!(
                    dest,
                    %path,
                    "fn_inline: seeded subslice_len from slice_from_raw_parts length arg"
                );
            }
        }

        debug!(
            bb_idx = dcx.bb_idx,
            callee = callee_path.as_deref().unwrap_or("<unknown>"),
            pure_fast_path = used_pure_fast_path,
            "fn_inline: successfully handled function call"
        );
        // Task #69: an inlined callee that takes a `&mut` reference to a
        // sidecar-tracked collection mutates the collection through its real
        // MIR (raw memory / SetLenOnDrop) and never syncs the sidecar length
        // vars. Mark those collections' sidecars untrusted so slice-index
        // current-length guards do not fire against a stale/free sidecar
        // length (which would produce Genuine-misclassified counterexamples).
        self.mark_inline_bypassed_collections(dcx.args);
        self.emit_translated_inline_call_result(
            dcx,
            *target,
            result_expr,
            inline_vtable,
            alias_updates,
            deferred_checks,
            &pre_resolved_args,
            &caller_vtable_ids,
            callee_path.as_deref(),
            "codegen_call_fn_inline",
            "fn_inline_alias_update",
        )
    }
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Task #69: mark sidecar-tracked collections passed by `&mut`/`*mut` to
    /// an inlined callee as sidecar-untrusted (see call site above).
    fn mark_inline_bypassed_collections(&mut self, args: &[Operand]) {
        for arg in args {
            let (Operand::Copy(place) | Operand::Move(place)) = arg else { continue };
            if !place.projection.is_empty() {
                continue;
            }
            let Ok(ty) = arg.ty(self.body.locals()) else { continue };
            let mutable = matches!(
                self.resolve_body_ty(ty).kind(),
                TyKind::RigidTy(RigidTy::Ref(_, _, rustc_public::mir::Mutability::Mut))
                    | TyKind::RigidTy(RigidTy::RawPtr(_, rustc_public::mir::Mutability::Mut))
            );
            if !mutable {
                continue;
            }
            let mut candidates = vec![place.local];
            if let Some(rt) = self.ref_resolution.ref_targets.get(&place.local) {
                candidates.push(rt.local);
            }
            for local in candidates {
                if self.collections.len_state.get_len_var(local).is_some() {
                    debug!(
                        fn_name = %self.fn_name,
                        local,
                        "fn_inline: marking collection sidecar untrusted (#69)"
                    );
                    self.collections.len_state.mark_sidecar_untrusted(local);
                }
            }
        }
    }

    /// Translate a call argument for inline function translation.
    ///
    /// Resolves operand references, including promoted const refs, and uses
    /// the modified_locals set to pick up the latest values for locals that
    /// were updated earlier in the block.
    fn translate_call_arg_for_inline(
        &mut self,
        arg: &Operand,
        modified_locals: &std::collections::HashSet<usize>,
    ) -> Option<Expr> {
        // Part of #4030: by-value raw-pointer arguments must preserve the
        // pointer value when seeding inline callee locals. Routing them through
        // resolve_ref_or_const_referent can chase `ref_targets` metadata from
        // prior `&raw`/indexing steps and accidentally bind the callee param to
        // the pointee content (for example an Array(BV64,BV8) backing array)
        // instead of the raw pointer itself. Pointer-ordering helper bodies
        // like `compare_diff(*const u8, *const u8)` then compare selected bytes
        // rather than addresses, producing false SAT counterexamples.
        if matches!(
            arg.ty(self.body.locals()).ok().map(|ty| ty.kind()),
            Some(TyKind::RigidTy(RigidTy::RawPtr(..)))
        ) {
            return self
                .translate_operand_with_modified(arg, modified_locals)
                .or_else(|| self.resolve_ref_or_const_referent(arg, modified_locals));
        }
        self.resolve_ref_or_const_referent(arg, modified_locals)
    }
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Part of #55 piece 4: FAIL-CLOSED unique-definition constant evaluation
    /// of a call-argument operand over the HOST MIR body.
    ///
    /// Returns `Some(literal)` ONLY when the operand's value is decided by a
    /// unique chain of constant definitions: `Use(const)`, `Copy/Move` of a
    /// uniquely-defined local, a `Field(0)` read of a uniquely-defined
    /// `CheckedBinaryOp` result, or an unchecked `BinaryOp` — with every leaf
    /// a constant. ANY of the following fails closed to `None` (symbolic arg,
    /// exactly the pre-existing behavior): more than one whole-local assign,
    /// any projected (partial) write to the local, the local being a call
    /// destination, an unsupported rvalue/projection shape, or depth
    /// exhaustion. A single constant-operand assign inside a loop is sound
    /// (same value every iteration); loop-varying operands fail the recursive
    /// evaluation by construction.
    pub(in crate::codegen_ay::chc) fn unique_def_const_operand(
        &mut self,
        operand: &Operand,
        depth: usize,
    ) -> Option<Expr> {
        use rustc_public::mir::{ProjectionElem, Rvalue, StatementKind};
        use trust_mc_core::chc_const_prop::eval::try_eval_to_const;
        if depth == 0 {
            return None;
        }
        let place = match operand {
            Operand::Copy(p) | Operand::Move(p) => p,
            Operand::Constant(_) => {
                let lit = self.translate_call_arg_for_inline(operand, &HashSet::new())?;
                return try_eval_to_const(&lit);
            }
        };
        // Unique whole-local definition; fail closed on partial writes and
        // call destinations.
        let mut unique_def: Option<&Rvalue> = None;
        for block in &self.body.blocks {
            for stmt in &block.statements {
                if let StatementKind::Assign(p, rv) = &stmt.kind {
                    if p.local == place.local {
                        if !p.projection.is_empty() || unique_def.is_some() {
                            return None;
                        }
                        unique_def = Some(rv);
                    }
                }
            }
            if let TerminatorKind::Call { destination, .. } = &block.terminator.kind {
                if destination.local == place.local {
                    return None;
                }
            }
        }
        let rv = unique_def?;
        let field_idx: Option<usize> = match place.projection.as_slice() {
            [] => None,
            [ProjectionElem::Field(i, _)] => Some(*i),
            _ => return None,
        };
        match (rv, field_idx) {
            (Rvalue::Use(inner), None) => self.unique_def_const_operand(inner, depth - 1),
            (Rvalue::BinaryOp(op, a, b), None) => {
                let ca = self.unique_def_const_operand(a, depth - 1)?;
                let cb = self.unique_def_const_operand(b, depth - 1)?;
                let signed = a
                    .ty(self.body.locals())
                    .ok()
                    .and_then(crate::codegen_ay::shared::ty_signedness_shallow)
                    .unwrap_or(false);
                try_eval_to_const(&Self::raw_bits_binop_expr_signed(*op, ca, cb, signed)?)
            }
            // `.0` of a checked binop: the wrapped result — raw bits are
            // identical for signed/unsigned add/sub/mul, so the fold is exact.
            // `.1` (overflow flag) is deliberately not evaluated here.
            (Rvalue::CheckedBinaryOp(op, a, b), Some(0)) => {
                let ca = self.unique_def_const_operand(a, depth - 1)?;
                let cb = self.unique_def_const_operand(b, depth - 1)?;
                try_eval_to_const(&Self::raw_bits_binop_expr(*op, ca, cb)?)
            }
            _ => None,
        }
    }

    /// Wrapping-result expression for the binops whose raw-bits result is
    /// signedness-independent. Comparison/shift/div variants are refused —
    /// their semantics need the signedness context the callers don't carry.
    fn raw_bits_binop_expr(op: rustc_public::mir::BinOp, a: Expr, b: Expr) -> Option<Expr> {
        Self::raw_bits_binop_expr_signed(op, a, b, false)
    }

    /// Signedness-aware variant: Div/Rem take the operand type's signedness
    /// (the walk callers derive it from the MIR local's declared type).
    fn raw_bits_binop_expr_signed(
        op: rustc_public::mir::BinOp,
        a: Expr,
        b: Expr,
        signed: bool,
    ) -> Option<Expr> {
        use rustc_public::mir::BinOp;
        Some(match op {
            BinOp::Add => a.bvadd(b),
            BinOp::Sub => a.bvsub(b),
            BinOp::Mul => a.bvmul(b),
            BinOp::BitAnd => a.bvand(b),
            BinOp::BitOr => a.bvor(b),
            BinOp::BitXor => a.bvxor(b),
            BinOp::Div if signed => a.bvsdiv(b),
            BinOp::Div => a.bvudiv(b),
            BinOp::Rem if signed => a.bvsrem(b),
            BinOp::Rem => a.bvurem(b),
            _ => return None,
        })
    }
}

/// Does `instance` carry a contract WITHOUT `#[kani::recursion]` while its
/// body still contains a direct self-call?
///
/// Kani fails such harnesses via the contract reentry tracker; the CHC walk
/// applies replace-style semantics to inner self-calls unconditionally, which
/// erases that failure — callers demote (fail-closed) when this returns true.
/// Live probe: fail_missing_recursion_attr false-proved at the v24 gate.
pub(in crate::codegen_ay::chc) fn contract_recursion_unannotated(
    tcx: rustc_middle::ty::TyCtxt,
    instance: Instance,
    body: &rustc_public::mir::Body,
) -> bool {
    use crate::kani_middle::attributes::KaniAttributes;
    let def_id = rustc_internal::internal(tcx, instance.def.def_id());
    let attrs = KaniAttributes::for_item(tcx, def_id);
    if !attrs.has_contract() || attrs.has_recursion() {
        return false;
    }
    let self_def_id = instance.def.def_id();
    body.blocks.iter().any(|bb| {
        let TerminatorKind::Call { func, .. } = &bb.terminator.kind else {
            return false;
        };
        let Ok(func_ty) = func.ty(body.locals()) else {
            return false;
        };
        match func_ty.kind() {
            TyKind::RigidTy(RigidTy::FnDef(def, _)) => def.def_id() == self_def_id,
            _ => false,
        }
    })
}

#[cfg(test)]
mod tests {
    use super::callee_uses_special_arithmetic_handler;

    #[test]
    fn special_arithmetic_handler_guard_matches_primitive_impls_only() {
        assert!(callee_uses_special_arithmetic_handler(
            "core::num::<impl u32>::unchecked_mul",
            "unchecked_mul"
        ));
        assert!(!callee_uses_special_arithmetic_handler(
            "multiple_inherent_impls::num::AnyNumber::<num::even::EvenNumber<i32>>::unchecked_mul",
            "unchecked_mul"
        ));
    }
}
