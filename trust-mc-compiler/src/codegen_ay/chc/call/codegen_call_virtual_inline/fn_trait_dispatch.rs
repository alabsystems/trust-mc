// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Fn/FnMut/FnOnce virtual call short-circuit for nested dyn-callable dispatch.
//!
//! Part of #3980: When a nested virtual call targets `Fn::call`,
//! `FnMut::call_mut`, or `FnOnce::call_once`, the blanket impl shim body
//! (`<&fn as FnMut>::call_mut`) forwards to `(**self)(args)`, which the
//! inline walker can't fully translate at nested depths. This module provides
//! helpers to short-circuit through the shim to the direct fn-item body.

use super::super::ChcCtx;
use super::super::codegen_types::CodegenTypes;
use super::super::dyn_dispatch_scope::DynDispatchScope;
use super::super::inline_body::translate_closure_inline_result;
use super::super::inline_mut_ref_owner::{InlineMutRefArg, MUT_REF_OWNER_UNRESOLVED};
use super::InlineReturn;
use super::dispatch::merge_guarded_dispatch_results;
use super::walker::translate_virtual_body_inline;
use crate::callee_body::CalleeBody;
use ay_bindings::{Expr, ExprValue};
use rustc_public::mir::Mutability;
use rustc_public::mir::mono::Instance;
use rustc_public::ty::{ClosureKind, RigidTy, Ty, TyKind};
use std::collections::HashMap;
use tracing::debug;

use crate::codegen_ay::provenance::is_value_widened_into_address;
use crate::codegen_ay::types::POINTER_WIDTH;

/// Detect Fn/FnMut/FnOnce::call/call_mut/call_once calls by path suffix.
pub(in crate::codegen_ay::chc) fn is_fn_trait_call(callee_path: &str) -> bool {
    callee_path.ends_with("::call")
        || callee_path.ends_with("::call_mut")
        || callee_path.ends_with("::call_once")
}

/// Try to short-circuit a Fn-trait virtual call by resolving the direct fn-item
/// body from the dyn-coercion candidate concrete types, bypassing the blanket
/// impl shim.
///
/// For each candidate concrete type (e.g., `&fn(&mut i32)`), extract the FnDef,
/// resolve its body, and inline it directly. This avoids walking the shim body
/// which contains `(**self)(args)` — a pattern the inline walker can't translate
/// at nested depths.
///
/// `candidates` carries each concrete type with its dispatch id; callers pass
/// only the candidates whose `Fn*::call` resolved for THIS call's signature
/// (the dyn-dispatch bodies' ids), so a std type that implements `Fn` for some
/// other signature (`core::slice::ascii::EscapeByte`) is not one. A candidate
/// is walked unconditionally only when the harness's dyn-coercion universe
/// says it is the receiver's ONLY runtime type (`scope`, design 3:
/// `dyn_dispatch_scope.rs`; it used to be enough that the candidate list had
/// one entry, which misses a callable coerced in a callee). Otherwise each
/// candidate whose signature fits the call is walked and the results are
/// merged under `vtable_disc == id` ([`merge_guarded_dispatch_results`]), so
/// every candidate's checks reach the host under its own dispatch condition,
/// and the merge's default arm fails closed unless the arms cover every
/// runtime type.
///
/// Before 2026-09-23 the first candidate with a body was walked
/// unconditionally whatever the count: a `Box<dyn Fn>` holding the SECOND of
/// two closures verified SUCCESSFUL clean with that closure's `unchecked_add`
/// overflow (Kani FAILED), because only the first closure was ever walked.
/// When the guarded merge cannot be built (no discriminant, a candidate that is
/// not a direct callable, a failed walk, a `&mut` argument whose write-back the
/// merge does not guard), the old first-candidate walk is kept for the bug it
/// can still find, and the harness fails closed
/// (`fn_trait_dispatch_unguarded_candidate`).
#[allow(clippy::too_many_arguments)]
pub(in crate::codegen_ay::chc) fn try_fn_trait_direct_dispatch(
    ctx: &mut ChcCtx<'_, '_>,
    candidates: &[(Ty, u64)],
    scope: &DynDispatchScope,
    vtable_disc: Option<&Expr>,
    translated_args: &[Expr],
    receiver_origin: Option<&super::super::native_dyn_origin::NativeDynOrigin>,
    mut_ref_args: &[Option<InlineMutRefArg>],
    closure_captures: &[Expr],
    caller_vtable_ids: &HashMap<usize, Expr>,
    inline_depth: usize,
) -> Option<InlineReturn> {
    if candidates.is_empty() {
        return None;
    }
    if let Some(origin) = receiver_origin {
        if !origin.constant_callable {
            ctx.record_sound_fallback_reason("native_dyn_callable_payload_unmodeled");
            return None;
        }
        let receiver = translated_args.first()?.clone();
        let Some(checked) = ctx.checked_native_dyn_pointer(receiver, origin) else {
            ctx.record_sound_fallback_reason("native_dyn_box_validity_unmodeled");
            return None;
        };
        let Some(&(concrete, _)) =
            candidates.iter().find(|&&(ty, id)| ty == origin.concrete && id == origin.vtable)
        else {
            ctx.record_sound_fallback_reason("native_dyn_vtable_body_untracked");
            return None;
        };
        let write_mark = ctx.heap_state.write_mark();
        let Some(body) = extract_direct_callable_body(concrete) else {
            ctx.record_sound_fallback_reason("native_dyn_vtable_body_untracked");
            return None;
        };
        if !matches!(body, DirectCallableBody::FnItem(_)) {
            ctx.record_sound_fallback_reason("native_dyn_callable_payload_unmodeled");
            return None;
        }
        let result = walk_direct_callable_unconditionally(
            ctx,
            body,
            translated_args,
            mut_ref_args,
            closure_captures,
            caller_vtable_ids,
            inline_depth,
        );
        let Some(mut result) = result else {
            ctx.record_sound_fallback_reason("native_dyn_checked_body_unmodeled");
            return None;
        };
        result.deferred_checks.extend(checked.checks.into_iter().map(|check| {
            super::super::inline_body::DeferredInlineCheck {
                check,
                kind: trust_mc_core::violation::PropertyKind::MemorySafety,
                message: Some(
                    "dyn callable requires its authenticated live aligned pointee".to_owned(),
                ),
                write_mark,
                merge_key: None,
            }
        }));
        return Some(result);
    }

    if candidates.len() > 1 || !scope.is_sole_runtime(candidates[0].1) {
        if let Some(vtable_disc) = vtable_disc
            && let Some(merged) = try_guarded_fn_trait_dispatch(
                ctx,
                candidates,
                scope,
                vtable_disc,
                translated_args,
                mut_ref_args,
                closure_captures,
                caller_vtable_ids,
                inline_depth,
            )
        {
            return Some(merged);
        }
        debug!(
            candidates = candidates.len(),
            "fn_trait_dispatch: guarded multi-candidate merge unavailable; \
             walking the first candidate only, failing closed"
        );
        ctx.record_sound_fallback_reason("fn_trait_dispatch_unguarded_candidate");
    }
    for &(concrete_ty, _) in candidates {
        if let Some(body) = extract_direct_callable_body(concrete_ty) {
            return walk_direct_callable_unconditionally(
                ctx,
                body,
                translated_args,
                mut_ref_args,
                closure_captures,
                caller_vtable_ids,
                inline_depth,
            );
        }
    }
    None
}

/// The one-candidate walk (and the fail-closed fallback): the candidate's body
/// with its `&mut` write-backs bridged to the outer locals directly.
fn walk_direct_callable_unconditionally(
    ctx: &mut ChcCtx<'_, '_>,
    body: DirectCallableBody,
    translated_args: &[Expr],
    mut_ref_args: &[Option<InlineMutRefArg>],
    closure_captures: &[Expr],
    caller_vtable_ids: &HashMap<usize, Expr>,
    inline_depth: usize,
) -> Option<InlineReturn> {
    match body {
        DirectCallableBody::FnItem(body) => {
            let mut fn_args = unpack_fn_trait_call_args(translated_args, &body, false)?;
            // Part of #3980: For `&mut T` args, replace the address (bv64) with the
            // pointed-to VALUE (bv_T). The inline walker uses Deref-as-identity, so
            // the body local must hold the VALUE for `*_1` reads to work correctly.
            // After the body walk, alias_updates will contain the modified values,
            // which we bridge back to the outer target locals via pending_updates.
            let mut_targets =
                resolve_mut_ref_value_args(ctx, &mut fn_args, &body, false, mut_ref_args)?;
            ctx.mark_inline_field_reads(&body, &fn_args, 0);
            let heap_snapshot = ctx.heap_state.snapshot_transient_rule_state();
            let modified_snapshot = ctx.encode.modified_state_indices.clone();
            ctx.inline_walk_param_address_seeds =
                Some(fn_trait_address_seeds(ctx, &body, &fn_args, false, &mut_targets));
            ctx.inline_walk_param_referent_seeds =
                Some(mut_targets.iter().map(|&(local, _)| local).collect());
            ctx.inline_walk_param_mut_owner_seeds = Some(
                mut_ref_args
                    .iter()
                    .enumerate()
                    .filter_map(|(i, binding)| {
                        binding.as_ref().map(|binding| (i + 1, binding.owner.clone()))
                    })
                    .collect(),
            );
            let result = translate_virtual_body_inline(
                ctx,
                &body,
                &fn_args,
                0,
                caller_vtable_ids,
                None,
                inline_depth + 1,
            );
            ctx.inline_walk_param_address_seeds = None;
            ctx.inline_walk_param_referent_seeds = None;
            ctx.inline_walk_param_mut_owner_seeds = None;
            if let Some(mut result) = result {
                bridge_mut_ref_alias_updates(ctx, &result, &mut_targets);
                // Clear alias_updates — we've bridged them directly to outer locals.
                // If left in, the nested call propagation would try to write them to
                // shim-internal locals (wrong scope).
                for &(body_arg_idx, _) in &mut_targets {
                    result.alias_updates.remove(&body_arg_idx);
                }
                return Some(result);
            }
            ctx.heap_state.restore_transient_rule_state(&heap_snapshot);
            ctx.encode.modified_state_indices = modified_snapshot;
            None
        }
        DirectCallableBody::Closure(body) => {
            let mut closure_args = unpack_fn_trait_call_args(translated_args, &body, true)?;
            let mut_targets =
                resolve_mut_ref_value_args(ctx, &mut closure_args, &body, true, mut_ref_args)?;
            // Part of #4003: When closure_captures is empty (cross-boundary dispatch),
            // try to extract captures from translated_args[0] (the receiver).
            let effective_captures = if closure_captures.is_empty() {
                extract_captures_from_receiver(translated_args)
            } else {
                closure_captures.to_vec()
            };
            ctx.inline_walk_param_address_seeds =
                Some(fn_trait_address_seeds(ctx, &body, &closure_args, true, &mut_targets));
            ctx.inline_walk_param_referent_seeds =
                Some(mut_targets.iter().map(|&(local, _)| local).collect());
            ctx.inline_walk_param_mut_owner_seeds = Some(
                mut_ref_args
                    .iter()
                    .enumerate()
                    .filter_map(|(i, binding)| {
                        binding.as_ref().map(|binding| (i + 2, binding.owner.clone()))
                    })
                    .collect(),
            );
            let result = translate_closure_inline_result(
                ctx,
                &body,
                &closure_args,
                &effective_captures,
                0,
                inline_depth + 1,
            );
            ctx.inline_walk_param_address_seeds = None;
            ctx.inline_walk_param_referent_seeds = None;
            ctx.inline_walk_param_mut_owner_seeds = None;
            if let Some(mut result) = result {
                bridge_mut_ref_alias_updates(ctx, &result, &mut_targets);
                for &(body_arg_idx, _) in &mut_targets {
                    result.alias_updates.remove(&body_arg_idx);
                }
                return Some(result);
            }
            None
        }
    }
}

/// Walk every candidate whose signature fits the call and merge the results
/// under `vtable_disc == id`. `None` (with the transient state restored) when
/// any candidate cannot be walked as a pure, guardable result.
#[allow(clippy::too_many_arguments)]
fn try_guarded_fn_trait_dispatch(
    ctx: &mut ChcCtx<'_, '_>,
    candidates: &[(Ty, u64)],
    scope: &DynDispatchScope,
    vtable_disc: &Expr,
    translated_args: &[Expr],
    mut_ref_args: &[Option<InlineMutRefArg>],
    closure_captures: &[Expr],
    caller_vtable_ids: &HashMap<usize, Expr>,
    inline_depth: usize,
) -> Option<InlineReturn> {
    let heap_snapshot = ctx.heap_state.snapshot_transient_rule_state();
    let modified_snapshot = ctx.encode.modified_state_indices.clone();
    let mut walked: Vec<(u64, InlineReturn)> = Vec::new();
    let mut give_up = false;
    // Phase 0 (inline_walk_guard.rs): one write mark over every candidate
    // (their heap stores are kept between walks), and the branch-arm rule for
    // a candidate's memory effect.
    let saved_mark = ctx.inline_walk_write_mark;
    if saved_mark.is_none() {
        ctx.inline_walk_write_mark = Some(ctx.heap_state.write_mark());
    }
    for &(concrete_ty, vtable_id) in candidates {
        let effects_before = ctx.heap_state.effect_mark();
        let checks_before = ctx.heap_state.pending_checks.len();
        // A candidate that is not a direct callable could be the runtime type:
        // leaving it to the fresh default arm would drop its obligations.
        let Some(body) = extract_direct_callable_body(concrete_ty) else {
            debug!(
                ?concrete_ty,
                vtable_id, "fn_trait_dispatch: guarded merge gives up (no direct body)"
            );
            give_up = true;
            break;
        };
        let (body, is_closure) = match body {
            DirectCallableBody::FnItem(body) => (body, false),
            DirectCallableBody::Closure(body) => (body, true),
        };
        // An arity mismatch means a different `dyn Fn` signature: this
        // candidate can never be the target of THIS call.
        let Some(mut args) = unpack_fn_trait_call_args(translated_args, &body, is_closure) else {
            debug!(?concrete_ty, vtable_id, "fn_trait_dispatch: candidate signature does not fit");
            continue;
        };
        // `&mut` write-backs are bridged unconditionally by the one-candidate
        // walk; the merge has no guarded form of that bridge.
        let Some(mut_targets) =
            resolve_mut_ref_value_args(ctx, &mut args, &body, is_closure, mut_ref_args)
        else {
            give_up = true;
            break;
        };
        if !mut_targets.is_empty() {
            debug!(?concrete_ty, vtable_id, "fn_trait_dispatch: guarded merge gives up (&mut arg)");
            give_up = true;
            break;
        }
        ctx.inline_walk_param_address_seeds =
            Some(fn_trait_address_seeds(ctx, &body, &args, is_closure, &[]));
        let result = if is_closure {
            let captures = if closure_captures.is_empty() {
                extract_captures_from_receiver(translated_args)
            } else {
                closure_captures.to_vec()
            };
            translate_closure_inline_result(ctx, &body, &args, &captures, 0, inline_depth + 1)
        } else {
            ctx.mark_inline_field_reads(&body, &args, 0);
            translate_virtual_body_inline(
                ctx,
                &body,
                &args,
                0,
                caller_vtable_ids,
                None,
                inline_depth + 1,
            )
        };
        ctx.inline_walk_param_address_seeds = None;
        match result {
            // Alias updates are keyed by the DIRECT body's argument locals,
            // which the shim-level caller cannot place: not guardable here.
            Some(result) if result.alias_updates.is_empty() => {
                if candidates.len() > 1 {
                    ctx.note_inline_branch_arm_effects(effects_before);
                }
                super::dispatch::guard_dispatch_arm_pending_checks(
                    ctx,
                    checks_before,
                    vtable_disc,
                    vtable_id,
                );
                walked.push((vtable_id, result));
            }
            other => {
                debug!(
                    ?concrete_ty,
                    vtable_id,
                    walked = other.is_some(),
                    "fn_trait_dispatch: guarded merge gives up (walk failed or alias updates)"
                );
                give_up = true;
                break;
            }
        }
    }
    ctx.inline_walk_write_mark = saved_mark;
    if give_up || walked.is_empty() {
        ctx.heap_state.restore_transient_rule_state(&heap_snapshot);
        ctx.encode.modified_state_indices = modified_snapshot;
        return None;
    }
    debug!(
        candidates = candidates.len(),
        walked = walked.len(),
        "fn_trait_dispatch: guarded multi-candidate merge"
    );
    let walked_ids: Vec<u64> = walked.iter().map(|(id, _)| *id).collect();
    let default = scope.default_arm(&walked_ids, vtable_disc);
    Some(merge_guarded_dispatch_results(ctx, walked, vtable_disc, default))
}

/// F2 (inline_walk_guard.rs): address seeds for a Fn-trait walk. The call's
/// arguments are the dyn door's raw operand terms, except the `&mut T`
/// arguments `resolve_mut_ref_value_args` replaced with (or confirmed as) the
/// target's value (`mut_targets`). A closure body's argument `i` is local
/// `i + 2` (local 1 is its env).
fn fn_trait_address_seeds(
    ctx: &ChcCtx<'_, '_>,
    body: &rustc_public::mir::Body,
    args: &[Expr],
    is_closure: bool,
    mut_targets: &[(usize, usize)],
) -> Vec<usize> {
    let locals = body.locals();
    let first_local = if is_closure { 2 } else { 1 };
    args.iter()
        .enumerate()
        .map(|(i, arg)| (i + first_local, arg))
        .filter(|(local, arg)| {
            !mut_targets.iter().any(|&(body_local, _)| body_local == *local)
                && super::super::inline_walk_guard::local_is_reference(ctx, locals, *local)
                && super::super::dyn_coercion::extract_pointer_expr(arg).is_some()
        })
        .map(|(local, _)| local)
        .collect()
}

enum DirectCallableBody {
    FnItem(rustc_public::mir::Body),
    Closure(rustc_public::mir::Body),
}

/// Extract a direct callable body from a concrete type that was coerced to `dyn Fn*`.
///
/// Handles:
/// - `&fn(args) -> ret` → deref to `fn(args) -> ret` → resolve FnDef body
/// - `fn(args) -> ret` → directly resolve FnDef body
/// - `&closure` → deref to closure → resolve via Instance::resolve_closure
/// - `closure` → directly resolve via Instance::resolve_closure
///
/// Part of #4003: closures coerced to `&dyn Fn` were silently dropped because
/// only `RigidTy::FnDef` was handled. Mirrors `dyn_callable_resolver.rs:108-138`.
fn extract_direct_callable_body(ty: Ty) -> Option<DirectCallableBody> {
    let inner_ty = match ty.kind() {
        TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) => pointee,
        _ => ty,
    };
    match inner_ty.kind() {
        TyKind::RigidTy(RigidTy::FnDef(fn_def, fn_args)) => {
            let instance = Instance::resolve(fn_def, &fn_args).ok()?;
            debug!(?ty, "fn_trait_dispatch: resolved fn-item body from concrete type");
            instance.callee_body().map(DirectCallableBody::FnItem)
        }
        TyKind::RigidTy(RigidTy::Closure(def, args)) => {
            for kind in [ClosureKind::Fn, ClosureKind::FnMut, ClosureKind::FnOnce] {
                if let Ok(instance) = Instance::resolve_closure(def, &args, kind) {
                    if let Some(body) = instance.callee_body() {
                        debug!(?ty, "fn_trait_dispatch: resolved closure body (#4003)");
                        return Some(DirectCallableBody::Closure(body));
                    }
                }
            }
            None
        }
        _ => None,
    }
}

/// Convert only explicitly owned `&mut T` arguments to their current values.
/// The owner and representation come from the exact RustCall field's binder;
/// no value bits or sort uniqueness can establish a mutable cell's identity.
pub(in crate::codegen_ay::chc::call) fn resolve_mut_ref_value_args(
    ctx: &mut ChcCtx<'_, '_>,
    fn_args: &mut [Expr],
    body: &rustc_public::mir::Body,
    is_closure: bool,
    mut_ref_args: &[Option<InlineMutRefArg>],
) -> Option<Vec<(usize, usize)>> {
    let body_locals = body.locals();
    let mut targets = Vec::new();
    let first_local = if is_closure { 2 } else { 1 };
    if fn_args.len() != body.arg_locals().len().saturating_sub(first_local - 1) {
        ctx.record_sound_fallback_reason(MUT_REF_OWNER_UNRESOLVED);
        return None;
    }
    for (i, fn_arg) in fn_args.iter_mut().enumerate() {
        let body_arg_local = i + first_local;
        let Some(decl) = body_locals.get(body_arg_local) else { continue };
        let TyKind::RigidTy(RigidTy::Ref(_, pointee, Mutability::Mut)) =
            ctx.resolve_body_ty(decl.ty).kind()
        else {
            continue;
        };
        let pointee = ctx.resolve_body_ty(pointee);
        let resolved = (|| {
            let binding = mut_ref_args.get(i)?.as_ref()?;
            let target = binding.owner.local;
            if binding.owner.pointee != pointee
                || ctx.resolve_body_ty(ctx.body.locals().get(target)?.ty) != pointee
                || targets.iter().any(|&(_, previous)| previous == target)
            {
                return None;
            }
            let pointee_sort = ChcCtx::translate_ty(pointee)?;
            if binding.referent_value {
                // Retain the existing matching-width/address-shape refusal.
                // Ownership does not make pointer-shaped element bits a value.
                if binding.value_mark.is_none_or(|mark| ctx.heap_state.written_since(mark))
                    || fn_arg.sort() != &pointee_sort
                    || super::super::dyn_coercion::extract_pointer_expr(fn_arg).is_some()
                {
                    return None;
                }
            } else {
                if fn_arg.sort().bitvec_width() != Some(POINTER_WIDTH)
                    || pointee_sort.bitvec_width() == Some(POINTER_WIDTH)
                    || is_value_widened_into_address(fn_arg)
                {
                    return None;
                }
                // The exact RustCall-field binder proved a plain host borrow,
                // copy or reborrow of THIS owner. Recover its real storage
                // identity instead of losing it behind the copied reference's
                // symbolic term (and treating a stack read as an unknown heap
                // alias). Read current typed memory, not the owner's entry-time
                // register value. No referent bits or sort search supplies an
                // address, and a contradictory concrete argument still refuses.
                // Recovery needs the already recorded allocation identity;
                // never mint fresh storage/liveness for an untracked owner.
                if !ctx.heap_state.local_addresses.contains_key(&target) {
                    return None;
                }
                let address = ctx.get_or_create_local_address(target)?;
                let (object, offset) = ChcCtx::try_extract_constant_addr(&address)?;
                if offset != 0 || ctx.heap_state.local_idx_for_obj_id(object) != Some(target) {
                    return None;
                }
                if ChcCtx::try_extract_constant_addr(fn_arg)
                    .is_some_and(|actual| actual != (object, offset))
                {
                    return None;
                }
                let value = ctx
                    .load_from_memory(
                        crate::codegen_ay::provenance::Loc::of_address(address),
                        pointee,
                    )?
                    .into_expr();
                if value.sort() != &pointee_sort {
                    return None;
                }
                *fn_arg = value;
            }
            Some((body_arg_local, target))
        })();
        let Some(target) = resolved else {
            ctx.record_sound_fallback_reason(MUT_REF_OWNER_UNRESOLVED);
            return None;
        };
        targets.push(target);
    }
    Some(targets)
}

/// Bridge modified `&mut T` values from the fn-item body's alias_updates back
/// to the outer function's target locals via pending_updates.
///
/// Part of #3980: After the fn-item body walk with VALUE-based args, the body's
/// `collect_alias_updates` captures modified values. This function maps those
/// back to the outer target locals as CHC state variable constraints.
///
/// Part of #4000: At Mem track level, also issue a heap memory store so that
/// subsequent loads (e.g., `assert!(x == 2)`) read the updated value from the
/// heap memory model, not just the direct state variable.
pub(in crate::codegen_ay::chc::call) fn bridge_mut_ref_alias_updates(
    ctx: &mut ChcCtx<'_, '_>,
    result: &InlineReturn,
    mut_targets: &[(usize, usize)],
) {
    for &(body_arg_local, target_local) in mut_targets {
        let Some(updated_value) = result.alias_updates.get(&body_arg_local) else {
            continue;
        };
        if ctx
            .try_state_idx_for_local(target_local)
            .is_some_and(|idx| ctx.encode.modified_state_indices.contains(&idx))
        {
            ctx.record_sound_fallback_reason("fn_trait_mut_ref_owner_already_written");
            continue;
        }
        ctx.invalidate_inline_mut_ref_owner_values(target_local);
        if let Some(constraints) = ctx.build_local_update_constraints(
            target_local,
            updated_value.clone(),
            "fn_trait_deref_bridge",
        ) {
            debug!(
                body_arg_local,
                target_local, "fn_trait_dispatch: bridged alias update to state var (#3980)"
            );
            ctx.heap_state.pending_updates.extend(constraints);
            if let Some((idx, _)) = ctx.resolve_destination(target_local) {
                ctx.mark_state_var_modified(idx);
            }
        }
        // Part of #4000: At Mem level, the assertion reads `x` from the heap via
        // memory select. The state variable update above is insufficient — we must
        // also store the updated value into the heap memory so loads see it.
        if let Some(addr) = ctx.get_or_create_local_address(target_local) {
            let target_ty = ctx.body.locals().get(target_local).map(|d| d.ty);
            if let Some(ty) = target_ty {
                ctx.build_memory_store(
                    crate::codegen_ay::provenance::Loc::of_address(addr),
                    updated_value.clone(),
                    ty,
                );
                debug!(
                    body_arg_local,
                    target_local, "fn_trait_dispatch: also stored to heap memory (#4000)"
                );
            }
        }
    }
}

/// Unpack the tupled args for an Fn-trait call into individual arguments.
///
/// `Fn::call(self, (arg1, arg2, ...))` → the tuple is `translated_args[1]`.
fn unpack_fn_trait_call_args(
    translated_args: &[Expr],
    direct_body: &rustc_public::mir::Body,
    body_has_closure_env: bool,
) -> Option<Vec<Expr>> {
    if translated_args.len() < 2 {
        return None;
    }
    let body_arg_count =
        direct_body.arg_locals().len().saturating_sub(if body_has_closure_env { 1 } else { 0 });
    let tuple_expr = &translated_args[1];

    if body_arg_count == 0 {
        return Some(Vec::new());
    }

    // A one-element argument tuple reaches here unwrapped (`translate_tuple_aggregate`
    // unwraps single-element tuples): when its term already has the sort of the
    // body's one parameter, it IS that argument. Peeling a constructor off it
    // below would hand the body the payload of an `Option`/`Some(..)` (or the
    // field of a newtype) as the whole parameter: `f(Some(&x))` walked the
    // closure with `extract[7:0](address)` as `o`, the discriminant of which
    // folded to `None` (walker_agg_ref_read_dual.rs::bug_closure_option_arg_read).
    if body_arg_count == 1 {
        let param_local = if body_has_closure_env { 2 } else { 1 };
        let param_sort =
            direct_body.locals().get(param_local).and_then(|decl| ChcCtx::translate_ty(decl.ty));
        if param_sort.as_ref() == Some(tuple_expr.sort()) {
            return Some(vec![tuple_expr.clone()]);
        }
    }

    // Part of #3980: If the tuple is a DatatypeConstructor, extract args directly
    // to preserve constant addresses (e.g., BvConcat alloc-id patterns). Using
    // field_select wraps constants in DatatypeSelector nodes that break
    // try_extract_constant_addr and store-to-load forwarding.
    if let ExprValue::DatatypeConstructor { args, .. } = tuple_expr.value() {
        if args.len() == body_arg_count {
            return Some(args.clone());
        }
    }

    if let Some(dt) = tuple_expr.sort().datatype_sort() {
        if let Some(cons) = dt.constructors.first() {
            if cons.fields.len() == body_arg_count {
                let fields: Vec<Expr> = cons
                    .fields
                    .iter()
                    .map(|field| {
                        tuple_expr.clone().field_select(&dt.name, &field.name, field.sort.clone())
                    })
                    .collect();
                return Some(fields);
            }
        }
    }

    if body_arg_count == 1 {
        return Some(vec![tuple_expr.clone()]);
    }

    None
}

/// Part of #4003: Extract closure captures from the receiver expression.
///
/// When a closure is passed through a function boundary via `&dyn Fn`, the MIR body
/// scan in `extract_nested_closure_captures` cannot find the Aggregate(Closure) because
/// it was constructed in a different body. The receiver (`translated_args[0]`) is the
/// `self` arg to `Fn::call`, which for `&dyn Fn` is the fat pointer.
///
/// This function tries to find the closure value from the receiver expression:
/// 1. If the receiver is a DatatypeConstructor with a data component that is itself
///    a closure DT (has cap_N fields), extract the cap fields as captures.
/// 2. If the receiver is a datatype with `fld_ptr`/`fld_data` pointing to a closure,
///    extract via field_select.
fn extract_captures_from_receiver(translated_args: &[Expr]) -> Vec<Expr> {
    let receiver = match translated_args.first() {
        Some(r) => r,
        None => return Vec::new(),
    };

    // Case 1: Receiver IS the closure value (deref-as-identity resolved it).
    if let Some(caps) = try_extract_closure_caps(receiver) {
        return caps;
    }

    // Case 2: Receiver is a fat pointer DT — extract data component and check if
    // it's the closure value.
    if let ExprValue::DatatypeConstructor { args, .. } = receiver.value() {
        // Fat pointer: (data_ptr, vtable). data_ptr might be the closure value.
        if let Some(first) = args.first() {
            if let Some(caps) = try_extract_closure_caps(first) {
                return caps;
            }
        }
    }

    // Case 3: Receiver is a datatype-sorted expression — try fld_ptr field.
    if let ay_bindings::SortInner::Datatype(dt) = receiver.sort().inner() {
        if let Some(cons) = dt.constructors.first() {
            for field in &cons.fields {
                if field.name == "fld_ptr" || field.name == "fld_data" || field.name == "field_0" {
                    let data_expr =
                        receiver.clone().field_select(&dt.name, &field.name, field.sort.clone());
                    if let Some(caps) = try_extract_closure_caps(&data_expr) {
                        return caps;
                    }
                }
            }
        }
    }

    Vec::new()
}

fn try_extract_closure_caps(expr: &Expr) -> Option<Vec<Expr>> {
    // Case A: DatatypeConstructor with args — direct extraction.
    if let ExprValue::DatatypeConstructor { args, .. } = expr.value() {
        if datatype_has_closure_cap_fields(expr) && !args.is_empty() {
            return Some(args.clone());
        }
    }

    // Case B: Datatype-sorted — check if fields look like closure captures (cap_N naming).
    if let ay_bindings::SortInner::Datatype(dt) = expr.sort().inner() {
        if let Some(cons) = dt.constructors.first() {
            let has_cap_fields = cons.fields.iter().any(|f| f.name.starts_with("cap_"));
            if has_cap_fields && !cons.fields.is_empty() {
                let fields: Vec<Expr> = cons
                    .fields
                    .iter()
                    .map(|field| {
                        expr.clone().field_select(&dt.name, &field.name, field.sort.clone())
                    })
                    .collect();
                return Some(fields);
            }
        }
    }

    None
}

fn datatype_has_closure_cap_fields(expr: &Expr) -> bool {
    let ay_bindings::SortInner::Datatype(dt) = expr.sort().inner() else {
        return false;
    };
    dt.constructors
        .first()
        .is_some_and(|cons| cons.fields.iter().any(|field| field.name.starts_with("cap_")))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::codegen_ay::names::struct_sort;
    use crate::codegen_ay::types::POINTER_WIDTH;
    use ay_bindings::Sort;

    #[test]
    fn test_extract_captures_from_receiver_ignores_fat_pointer_constructor() {
        let fat_ptr_sort = struct_sort(
            "DynFnFatPtr",
            [("fld_ptr", Sort::bitvec(POINTER_WIDTH)), ("fld_vtable", Sort::bitvec(POINTER_WIDTH))],
        );
        let receiver = Expr::datatype_constructor(
            "DynFnFatPtr",
            "DynFnFatPtr_mk",
            vec![
                Expr::bitvec_const(0x1000u128, POINTER_WIDTH),
                Expr::bitvec_const(0x2000u128, POINTER_WIDTH),
            ],
            fat_ptr_sort,
        );

        assert!(
            extract_captures_from_receiver(&[receiver]).is_empty(),
            "fat pointer fields must not be misread as closure captures"
        );
    }

    /// `f(Some(7))` through `&dyn Fn(Option<u8>)`: the one-element argument
    /// tuple reaches the unpacker unwrapped, as the `Option` itself. It is the
    /// body's one argument whole, never the `Some` payload peeled off it
    /// (walker_agg_ref_read_dual.rs::bug_closure_option_arg_read: the payload
    /// bits taken as the `Option` folded its discriminant to `None`).
    #[cfg(feature = "compiler-corpus-tests")]
    #[test]
    fn test_unpack_keeps_a_one_field_constructor_argument_whole() {
        use crate::codegen_ay::context::with_test_ay_ctx_for_source;
        use crate::codegen_ay::test_fixtures::find_instance_by_suffix;
        let source = r#"
            pub fn take_opt(o: Option<u8>) -> u8 { match o { Some(v) => v, None => 0 } }
        "#;
        let ran = std::sync::atomic::AtomicBool::new(false);
        with_test_ay_ctx_for_source(source, |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "take_opt");
            let body = instance.body().expect("function body");
            let sort = ChcCtx::translate_ty(body.locals()[1].ty).expect("Option<u8> sort");
            let ay_bindings::SortInner::Datatype(dt) = sort.inner() else {
                panic!("Option<u8> is a datatype sort here: {sort:?}");
            };
            let some = dt
                .constructors
                .iter()
                .find(|ctor| ctor.fields.len() == 1)
                .expect("a one-field Some constructor");
            let width = some.fields[0].sort.bitvec_width().expect("a bitvector payload");
            let arg = Expr::datatype_constructor(
                &dt.name,
                &some.name,
                vec![Expr::bitvec_const(7u128, width)],
                sort.clone(),
            );
            let receiver = Expr::bitvec_const(0x1000u128, POINTER_WIDTH);
            let unpacked = unpack_fn_trait_call_args(&[receiver, arg.clone()], &body, false)
                .expect("one argument");
            assert_eq!(unpacked.len(), 1);
            assert_eq!(
                unpacked[0].sort(),
                &sort,
                "the argument keeps the Option's sort, not its payload's: {:?}",
                unpacked[0]
            );
            ran.store(true, std::sync::atomic::Ordering::SeqCst);
        });
        assert!(ran.load(std::sync::atomic::Ordering::SeqCst), "the probe crate compiled");
    }
}
