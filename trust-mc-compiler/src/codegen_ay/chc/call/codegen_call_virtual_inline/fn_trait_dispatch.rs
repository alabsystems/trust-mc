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
use super::super::inline_body::translate_closure_inline_result;
use super::InlineReturn;
use super::walker::translate_virtual_body_inline;
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
pub(in crate::codegen_ay::chc) fn try_fn_trait_direct_dispatch(
    ctx: &mut ChcCtx<'_, '_>,
    candidate_types: &[Ty],
    translated_args: &[Expr],
    closure_captures: &[Expr],
    caller_vtable_ids: &HashMap<usize, Expr>,
    inline_depth: usize,
) -> Option<InlineReturn> {
    for &concrete_ty in candidate_types {
        if let Some(body) = extract_direct_callable_body(concrete_ty) {
            match body {
                DirectCallableBody::FnItem(body) => {
                    let mut fn_args = unpack_fn_trait_call_args(translated_args, &body, false)?;
                    // Part of #3980: For `&mut T` args, replace the address (bv64) with the
                    // pointed-to VALUE (bv_T). The inline walker uses Deref-as-identity, so
                    // the body local must hold the VALUE for `*_1` reads to work correctly.
                    // After the body walk, alias_updates will contain the modified values,
                    // which we bridge back to the outer target locals via pending_updates.
                    let mut_targets = resolve_mut_ref_value_args(ctx, &mut fn_args, &body);
                    ctx.mark_inline_field_reads(&body, &fn_args, 0);
                    let heap_snapshot = ctx.heap_state.snapshot_transient_rule_state();
                    let modified_snapshot = ctx.encode.modified_state_indices.clone();
                    let result = translate_virtual_body_inline(
                        ctx,
                        &body,
                        &fn_args,
                        0,
                        caller_vtable_ids,
                        None,
                        inline_depth + 1,
                    );
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
                    return None;
                }
                DirectCallableBody::Closure(body) => {
                    let mut closure_args = unpack_fn_trait_call_args(translated_args, &body, true)?;
                    let mut_targets = resolve_mut_ref_value_args(ctx, &mut closure_args, &body);
                    // Part of #4003: When closure_captures is empty (cross-boundary dispatch),
                    // try to extract captures from translated_args[0] (the receiver).
                    let effective_captures = if closure_captures.is_empty() {
                        extract_captures_from_receiver(translated_args)
                    } else {
                        closure_captures.to_vec()
                    };
                    let result = translate_closure_inline_result(
                        ctx,
                        &body,
                        &closure_args,
                        &effective_captures,
                        0,
                        inline_depth + 1,
                    );
                    if let Some(mut result) = result {
                        bridge_mut_ref_alias_updates(ctx, &result, &mut_targets);
                        for &(body_arg_idx, _) in &mut_targets {
                            result.alias_updates.remove(&body_arg_idx);
                        }
                        return Some(result);
                    }
                    return None;
                }
            }
        }
    }
    None
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
            instance.body().map(DirectCallableBody::FnItem)
        }
        TyKind::RigidTy(RigidTy::Closure(def, args)) => {
            for kind in [ClosureKind::Fn, ClosureKind::FnMut, ClosureKind::FnOnce] {
                if let Ok(instance) = Instance::resolve_closure(def, &args, kind) {
                    if let Some(body) = instance.body() {
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

/// Replace `&mut T` fn_args (addresses) with pointed-to VALUES for the
/// transparent Deref-as-identity model used by the inline walker.
///
/// Part of #3980: The inline walker treats `Deref` as identity — `*_1` resolves
/// to `local_exprs[1]` directly. If the arg holds an ADDRESS (bv64), the body
/// would compute on the address instead of the pointee value. This function
/// replaces address args with the target local's state-variable value.
///
/// Returns `(body_arg_local, outer_target_local)` pairs for post-walk bridging.
pub(in crate::codegen_ay::chc::call) fn resolve_mut_ref_value_args(
    ctx: &ChcCtx<'_, '_>,
    fn_args: &mut [Expr],
    body: &rustc_public::mir::Body,
) -> Vec<(usize, usize)> {
    let body_locals = body.locals();
    let mut targets = Vec::new();
    for (i, fn_arg) in fn_args.iter_mut().enumerate() {
        let body_arg_local = i + 1;
        let Some(decl) = body_locals.get(body_arg_local) else { continue };
        let pointee_ty = match decl.ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(_, p, Mutability::Mut)) => p,
            _ => continue,
        };
        let pointee_ty = ctx.resolve_body_ty(pointee_ty);
        let pointee_sort = match ChcCtx::translate_ty(pointee_ty) {
            Some(s) => s,
            None => continue,
        };

        // Part of #3980: Two cases for fn_args passed through fn_trait_dispatch:
        // (a) fn_arg is bv64 (address) — the inline walker called with a raw
        //     pointer. Replace with the target local's VALUE so Deref-as-identity
        //     works correctly in the body walk.
        // (b) fn_arg already has the pointee sort — the outer fn_inline handler
        //     resolved `&mut T` to its target VALUE before passing it down. No
        //     replacement needed, but we still track the pair so alias_updates
        //     from the body walk get bridged to the outer state variable.
        //
        // KNOWN LIMITATION (Part of #3980): When pointee_sort is also bv64 (e.g.,
        // &mut i64, &mut usize, &mut fn_ptr), this heuristic cannot distinguish
        // address-from-value because both are the same width. In that case,
        // is_address=false and is_already_value=true, so the arg passes through
        // without replacement. This is SAFE (no false PROOF — the body reads the
        // address as a value, producing an overconstrained or UNKNOWN result) but
        // means dyn dispatch through &mut <bv64-sized-type> may fail to prove.
        //
        // ADDRESS-VS-VALUE: this guard is deliberately KEPT (see
        // `codegen_ay/provenance.rs`). It cannot be retired by threading a tag
        // from the producer, because there is no producer to thread it from:
        // `fn_args` arrives from `unpack_fn_trait_call_args`, which unpacks the
        // `Fn::call` argument tuple built by `translate_operand_with_modified` —
        // the one function in the encoder that serves every operand and reports
        // nothing about what it returned. That is the same wall the two
        // `#[deprecated]` `*_untyped` memory shims are parked against, and
        // typing this slot means typing that function's return, not this test.
        // Retagging the term here from the MIR `&mut T` alone would be a
        // FABRICATION of exactly the kind the campaign exists to remove: the
        // walker's own transparent-Deref model is why a `&mut T` local's term is
        // frequently the pointee's VALUE, which is the ambiguity above.
        //
        // What IS provable is narrowed off: a zero/sign-extended narrow datum is
        // never an address (its obj_id lane is forced to 0), so it can no longer
        // be replaced by an unrelated target local's state variable. The refusal
        // runs on the UNCOERCED arg — nothing widens `fn_arg` between the tuple
        // unpack and here — so it cannot be defeated by a coercion upstream of
        // the test.
        //
        // The `pointee_sort != POINTER_WIDTH` conjunct below is also what the
        // CONSUMER of this substitution now uses to discharge the same
        // ambiguity: `projected_assign::inline_deref_target_addr` takes the
        // pointee type from its callers and treats a non-pointer-width pointee
        // as proof that its root term cannot be a value substituted here. The
        // two halves of #3980 agree on one discriminator, deliberately — if this
        // condition is ever widened, that consumer's ESTABLISHED lane widens
        // with it and must be revisited in the same change.
        let is_address = fn_arg.sort().bitvec_width() == Some(POINTER_WIDTH)
            && pointee_sort.bitvec_width() != Some(POINTER_WIDTH)
            && !is_value_widened_into_address(fn_arg);
        let is_already_value = *fn_arg.sort() == pointee_sort;

        if !is_address && !is_already_value {
            continue;
        }

        // Find the unique outer target local whose state-var sort matches
        // the pointee sort. For the common case (one `&mut T` per type),
        // this uniquely identifies the target. Deduplicate because multiple
        // ref locals can point to the same target (Part of #4000).
        let candidates: Vec<usize> = {
            let mut raw: Vec<usize> = ctx
                .ref_resolution
                .ref_targets
                .iter()
                .filter(|(_, rt)| rt.projections.is_empty())
                .filter_map(|(_, rt)| {
                    let (_, out_sort) = ctx
                        .state_var_mgr
                        .output_state_vars
                        .get(ctx.try_state_idx_for_local(rt.local)?)?;
                    (out_sort == &pointee_sort).then_some(rt.local)
                })
                .collect();
            raw.sort_unstable();
            raw.dedup();
            raw
        };

        if candidates.len() != 1 {
            debug!(
                arg_idx = i,
                candidate_count = candidates.len(),
                "fn_trait_dispatch: mut ref resolve skipped (ambiguous or no target)"
            );
            continue;
        }
        let target_local = candidates[0];

        if is_address {
            // Case (a): replace address with value.
            let Some(state_idx) = ctx.try_state_idx_for_local(target_local) else { continue };
            let Some((in_name, in_sort)) = ctx.state_var_mgr.state_vars.get(state_idx) else {
                continue;
            };
            let target_value = Expr::var(&**in_name, in_sort.clone());
            debug!(
                body_arg_local,
                target_local, "fn_trait_dispatch: replaced address arg with value (#3980)"
            );
            *fn_arg = target_value;
        } else {
            // Case (b): already a value, just track for bridging.
            debug!(
                body_arg_local,
                target_local, "fn_trait_dispatch: arg already value, tracking for bridge (#3980)"
            );
        }
        targets.push((body_arg_local, target_local));
    }
    targets
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
                ctx.build_memory_store_untyped(addr, updated_value.clone(), ty);
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
}
