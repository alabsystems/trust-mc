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
//! - `codegen_call_fn_inline_specialization`: copy-swap body recognition
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
use super::inline_ref_arg_binding::InlineArgBinding;
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

    let interior =
        ChcCtx::try_extract_constant_addr(data_expr).is_some_and(|(_, offset)| offset != 0);
    let source = src_local.filter(|src| !ctx.local_has_multiple_whole_definitions(*src));
    let base_obj_id = if interior {
        None
    } else {
        source
            .and_then(|src| ctx.trace_deref_store_alloc_id(src))
            .or_else(|| ChcCtx::try_extract_base_obj_id(data_expr))
    };
    if let Some(obj_id) = base_obj_id {
        ctx.known_alloc_ids.insert(dest_local, obj_id);
    } else {
        ctx.known_alloc_ids.remove(&dest_local);
    }

    let ref_target = source
        .and_then(|src| ctx.ref_resolution.ref_targets.get(&src).cloned())
        .or_else(|| {
            base_obj_id
                .and_then(|_| source.and_then(|src| trace_pointer_identity_ref_target(ctx, src)))
        })
        .filter(|target| !interior || !target.projections.is_empty())
        .or_else(|| {
            ChcCtx::try_extract_base_obj_id(data_expr).and_then(|obj_id| {
                ctx.heap_state.local_idx_for_obj_id(obj_id).map(|local| {
                    super::codegen_ctx::types::RefTarget::with_projections(local, vec![])
                })
            })
        });
    if let Some(ref_target) = ref_target {
        ctx.ref_resolution.ref_targets.insert(dest_local, ref_target);
        ctx.ref_resolution.call_forwarded_raw_ptrs.insert(dest_local);
    } else {
        ctx.ref_resolution.ref_targets.remove(&dest_local);
        ctx.ref_resolution.call_forwarded_raw_ptrs.remove(&dest_local);
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
        // A renamed float intrinsic reaches its model, never Trust's fallback body
        // (`intrinsics::is_modelled_renamed_intrinsic`).
        if crate::intrinsics::is_modelled_renamed_intrinsic(&instance) {
            return false;
        }

        // Get the TRANSFORMED MIR body (contract mode dispatch, stubs,
        // rewrites) — raw `instance.body()` bypasses the kani_middle transform
        // pipeline and leaves walked contract checks vacuous (mode dummy 0).
        let callee_name =
            self.tcx.def_path_str(rustc_internal::internal(self.tcx, instance.def.def_id()));
        if matches!(
            crate::codegen_ay::shared::compare_loops::comparison_call(&callee_name),
            Some(crate::codegen_ay::shared::compare_loops::ComparisonCall::Eq { .. })
        ) && self.has_heterogeneous_sequence_elements(dcx.func, self.body.locals())
        {
            self.record_sound_fallback_reason("heterogeneous_sequence_comparison");
            return false;
        }
        // A comparison of a type holding references compares referents; the
        // walker compares the addresses it holds for them
        // (`inline_ref_arg_binding::comparison_referent_holds_reference`).
        // Against a constant fieldless variant (`first(&a) == None`) no
        // referent is compared, and the walk of the derived body is exact
        // (`comparison_against_fieldless_variant_constant`).
        if super::inline_ref_arg_binding::is_comparison_callee_path(&callee_name)
            && dcx.args.first().is_some_and(|arg| {
                super::inline_ref_arg_binding::comparison_referent_holds_reference(
                    self,
                    arg,
                    self.body.locals(),
                )
            })
            && !super::inline_ref_arg_binding::comparison_against_fieldless_variant_constant(
                self, &dcx.args,
            )
        {
            debug!(
                %callee_name,
                fn_name = %self.fn_name,
                "fn_inline: skip (comparison of a type holding references)"
            );
            self.note_gap_reason("inline_cmp_referent_holds_reference");
            return false;
        }
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
        // Unchecked arithmetic wrappers in core::num (unchecked_add/sub/mul/div/rem/
        // shl/shr) are not inlined here: they fall through to
        // codegen_wrapping_arithmetic (step_wrapping.rs), which emits the overflow
        // and shift-distance error rules at the call. Mirrors Kani's MIR-level
        // FunctionInlinePass::has_special_codegen_handler (inline/mod.rs:269).
        //
        // The wrapper's assert_unsafe_precondition! is NOT the obligation: its
        // branch is dead (check_language_ub() folds to false, as Kani compiles
        // RuntimeChecks). What Kani reports is the wrapper's own AddUnchecked /
        // ShlUnchecked / ... BinOp. A walk that reaches the wrapper another way (dyn
        // dispatch, a nested helper) records that BinOp's check itself
        // (inline_shared/rvalue_ub.rs); it records Assert terminators as real
        // deferred checks too, not only as ite guards. A walk that havocs the
        // wrapper instead books the lost effect (Rule D: the wrapper is not inert).
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
        if self.authenticated_spec_array_comparison_is_ne(instance.def.def_id()).is_some() {
            self.inline_self_field_hints = None;
            return false;
        }
        if self.try_dispatch_copy_swap_body(dcx, &body, &callee_name) {
            self.inline_self_field_hints = None;
            return true;
        }

        if self.try_inline_storage_address(dcx, &body, instance) {
            self.inline_self_field_hints = None;
            return true;
        }

        // Part of #3830: Pre-populate field hints before arg translation.
        populate_inline_self_field_hints(self, dcx);
        let comparison_callee =
            super::inline_ref_arg_binding::is_comparison_callee_path(&callee_name);
        // Translate arguments (needed by known-call fast path AND body walk).
        let mut params: Vec<Expr> = Vec::with_capacity(dcx.args.len());
        let mut used_self_placeholder = false;
        // F2 (inline_walk_guard.rs): parameters bound to an address the walker
        // would read as the referent.
        let mut address_seeds: Vec<usize> = Vec::new();
        let mut referent_seeds: Vec<usize> = Vec::new();
        let mut readonly_ref_seeds = Vec::new();
        let mut mut_owner_seeds = Vec::new();
        let mut rustcall_mut_owner_seeds = Vec::new();
        let mut native_dyn_seeds = Vec::new();
        let native_box_protocol =
            crate::codegen_ay::shared::native_box_call::native_global_dyn_box_call(
                self.tcx, &instance,
            );
        for (i, arg) in dcx.args.iter().enumerate() {
            let actual_ty = arg.ty(self.body.locals()).ok().map(|ty| self.resolve_body_ty(ty));
            let formal_ty = body.locals().get(i + 1).map(|decl| self.resolve_body_ty(decl.ty));
            let rustcall = i == 1
                && func_ty.kind().fn_sig().is_some_and(|signature| {
                    signature.skip_binder().abi == rustc_public::ty::Abi::RustCall
                });
            let reference_field = actual_ty.and_then(|actual| match actual.kind() {
                TyKind::RigidTy(RigidTy::Tuple(fields))
                    if fields.len() == 1 && self.readonly_scalar_pointee(fields[0]).is_some() =>
                {
                    Some(fields[0])
                }
                _ => None,
            });
            let spread_reference =
                rustcall && reference_field.is_some() && formal_ty == reference_field;
            let packed_reference = rustcall && reference_field.is_some() && formal_ty == actual_ty;
            if rustcall
                && !spread_reference
                && !packed_reference
                && actual_ty.is_some_and(|actual| {
                    matches!(actual.kind(), TyKind::RigidTy(RigidTy::Tuple(fields))
                    if fields.iter().any(|field| self.readonly_scalar_pointee(*field).is_some()))
                })
            {
                self.record_sound_fallback_reason("inline_rustcall_reference_binding_unmodeled");
                return false;
            }
            // A closed protocol borrow supplies the actual Box VALUE as the
            // shim receiver's referent. Its owner-storage address stays distinct.
            let native_receiver = (i == 0 && native_box_protocol.is_some())
                .then(|| self.host_native_dyn_callable_receiver(arg))
                .flatten();
            let binding = if let Some((owner, origin)) = &native_receiver {
                let Some(value) = self.translate_operand_with_modified(
                    &Operand::Copy(owner.clone()),
                    dcx.modified_locals,
                ) else {
                    return false;
                };
                native_dyn_seeds.push((i + 1, origin.clone()));
                InlineArgBinding::BoundReferent(value)
            } else if spread_reference || packed_reference {
                match self.bind_rustcall_single_reference(arg, dcx.modified_locals) {
                    Some((binding, read)) => {
                        // The real shim can retain the tuple formal rather
                        // than spread it. Its field is a logical scalar only
                        // when this actual typed host binding read the value.
                        if packed_reference && read.is_none() {
                            self.record_sound_fallback_reason(
                                "inline_rustcall_reference_tuple_value_unmodeled",
                            );
                            return false;
                        }
                        if let Some(mut read) = read {
                            let Some(formal) = formal_ty else { return false };
                            read.ty = formal;
                            readonly_ref_seeds.push((i + 1, read));
                        }
                        if packed_reference {
                            // Keep the actual tuple carrier intact. Its field
                            // read travels separately; it is not the tuple's
                            // pointer or native memory image.
                            let Some(carrier) =
                                self.translate_operand_with_modified(arg, dcx.modified_locals)
                            else {
                                self.record_sound_fallback_reason(
                                    "inline_rustcall_reference_tuple_carrier_unmodeled",
                                );
                                return false;
                            };
                            InlineArgBinding::Bound(carrier)
                        } else {
                            binding
                        }
                    }
                    None => {
                        self.record_sound_fallback_reason(
                            "inline_rustcall_reference_binding_unmodeled",
                        );
                        self.inline_self_field_hints = None;
                        return false;
                    }
                }
            } else {
                self.bind_call_arg_for_inline(arg, dcx.modified_locals, comparison_callee)
            };
            let bound = match binding {
                InlineArgBinding::Bound(expr) => Some(expr),
                InlineArgBinding::BoundReferent(expr) => {
                    referent_seeds.push(i + 1);
                    Some(expr)
                }
                InlineArgBinding::BoundAddress(expr) => {
                    address_seeds.push(i + 1);
                    Some(expr)
                }
                InlineArgBinding::ReadThrough(expr) => {
                    referent_seeds.push(i + 1);
                    // The referent was read through the reference's address.
                    // Receiver hints come from a pointer-identity trace of the
                    // SAME reference, the fact the cascade could not establish;
                    // the value just read is the whole receiver.
                    if i == 0 {
                        self.inline_self_field_hints = None;
                    }
                    Some(expr)
                }
                InlineArgBinding::Refused(reason) => {
                    // The reference's own term is an address the walker would
                    // decode as its referent, and no sound read replaces it
                    // (inline_ref_arg_binding.rs). Walking the body with it is
                    // how `!(a == b)` on a joined Option was proved.
                    debug!(
                        i,
                        fn_name = %self.fn_name,
                        %callee_name,
                        reason,
                        "fn_inline: skip (reference argument without a readable referent)"
                    );
                    self.note_gap_reason(reason);
                    self.inline_self_field_hints = None;
                    return false;
                }
                InlineArgBinding::Unresolved => None,
            };
            if let Some(expr) = bound {
                // A fresh typed host read supplies its own epoch-bearing
                // fact; a transported legacy tag cannot supply this.
                if referent_seeds.contains(&(i + 1))
                    && let Some(ty) = if spread_reference { formal_ty } else { actual_ty }
                    && let Some(seed) = self.readonly_ref_seed_for_value(ty, &expr)
                {
                    readonly_ref_seeds.push((i + 1, seed));
                }
                if let Some(seed) = self.host_readonly_capture_seed(arg, dcx.modified_locals) {
                    readonly_ref_seeds.push((i + 1, seed));
                }
                if let Some(origin) = self.host_native_dyn_origin(arg) {
                    native_dyn_seeds.push((i + 1, origin));
                }
                if let Some(owner) = self.host_mut_ref_owner(arg) {
                    mut_owner_seeds.push((i + 1, owner));
                }
                let owners = self.host_rustcall_mut_ref_args(arg);
                if !owners.is_empty() {
                    rustcall_mut_owner_seeds.push((i + 1, owners));
                }
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
                // Logical referents never enter this address recovery: u64
                // and f64 values can have the same sort as an address.
                let expr = if !referent_seeds.contains(&(i + 1))
                    && trust_mc_core::chc_const_prop::eval::try_eval_to_const(&expr).is_none()
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
                // A by-value flattened argument with no whole-value term (an
                // Int-lifted Range): remember its slots, so a body that returns
                // the placeholder unchanged returns them. Only the values this
                // block already holds for them: its `__out` variables are the
                // moved-out placeholder's after the call.
                if let Operand::Copy(place) | Operand::Move(place) = arg
                    && place.projection.is_empty()
                    && self.flatten.flattened_tuple_locals.contains(&place.local)
                    && let Some(slots) = (0..self.flattened_field_count(place.local))
                        .map(|slot| {
                            self.encode.flattened_field_env.get(&(place.local, slot)).cloned()
                        })
                        .collect::<Option<Vec<_>>>()
                {
                    self.inline_placeholder_slots.insert(placeholder_name.clone(), slots);
                }
                debug!(fn_name = %self.fn_name, %callee_name, %placeholder_name, "fn_inline: placeholder");
                used_self_placeholder = true;
                // A fresh bitvector, not the receiver: only the hint map may
                // answer a read through it.
                address_seeds.push(1);
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
                } else if arg.ty(self.body.locals()).ok().is_some_and(|ty| {
                    matches!(self.resolve_body_ty(ty).kind(),
                        TyKind::RigidTy(RigidTy::Ref(_, inner, _) | RigidTy::RawPtr(inner, _))
                            if matches!(inner.kind(), TyKind::RigidTy(RigidTy::Slice(_) | RigidTy::Str)))
                }) && let Some(len_expr) = self.resolve_ptr_metadata_known(arg, dcx.modified_locals)
                    && len_expr.sort().bitvec_width() == Some(POINTER_WIDTH)
                {
                    // A cleared historical side table does not erase the
                    // current wide pointer's metadata. Carry the same known
                    // value that PtrMetadata reads into the callee; never seed
                    // a fabricated or unconstrained length.
                    caller_subslice_lens.insert(i + 1, len_expr);
                } else if let Some(len_expr) = self.vec_as_slice_len(local_idx)
                    && len_expr.sort().bitvec_width() == Some(POINTER_WIDTH)
                {
                    // A `Vec`'s slice view (`v.contains(&x)` derefs `v`): the
                    // walked callee reads its length from the seed, as the host
                    // reads `PtrMetadata` of the view, where it read a fresh
                    // one and could not bound the `memchr` loop it havocs
                    // under a declared unwind (walker fail-closed repair round
                    // 5, `model_call_unwind_dual.rs` `u6`).
                    caller_subslice_lens.insert(i + 1, len_expr);
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
            crate::intrinsics::instance_path_model_spelling(
                self.tcx.def_path_str(internal_def_id),
                &instance,
            )
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
                        dcx.args,
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
                            dcx.args,
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
            } else if let Some(expr) = {
                self.inline_walk_param_address_seeds = Some(address_seeds.clone());
                self.inline_walk_param_referent_seeds = Some(referent_seeds.clone());
                self.inline_walk_param_mut_owner_seeds = Some(mut_owner_seeds.clone());
                self.inline_walk_param_rustcall_mut_owner_seeds =
                    Some(rustcall_mut_owner_seeds.clone());
                self.inline_walk_param_native_dyn_seeds = Some(native_dyn_seeds.clone());
                self.inline_walk_param_readonly_ref_seeds = Some(readonly_ref_seeds.clone());
                let expr = try_inline_simple_bool_return_helper(
                    self,
                    &body,
                    &params,
                    callee_path.as_deref(),
                );
                self.inline_walk_param_address_seeds = None;
                self.inline_walk_param_referent_seeds = None;
                self.inline_walk_param_mut_owner_seeds = None;
                self.inline_walk_param_rustcall_mut_owner_seeds = None;
                self.inline_walk_param_native_dyn_seeds = None;
                self.inline_walk_param_readonly_ref_seeds = None;
                expr
            } {
                (expr, None, std::collections::BTreeMap::new(), Vec::new(), true)
            } else {
                // Part of #3875: Skip body inline for SpecArrayEq::spec_eq.
                // The body of spec_eq uses BinOp::Eq on arrays, which produces full
                // SMT extensional equality (forall i. select(a,i)==select(b,i)) including
                // uninitialized indices beyond N. Fall through to tail_dispatch which
                // does element-wise comparison over 0..N only.
                if self.authenticated_spec_array_comparison_is_ne(instance.def.def_id()).is_some() {
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
                // The walk clears its body's entries on entry and applies
                // these to its argument locals (`walker.rs`,
                // `enter_body_subslice_scope`).
                self.ref_resolution.inline_arg_subslice_seeds =
                    Some((caller_subslice_lens.clone(), caller_subslice_offsets.clone()));
                self.ref_resolution.inline_return_subslice = (None, None);
                // Part of #4185: Snapshot heap state before speculative inline walk.
                // If the walk bails (returns None), orphaned heap mutations from
                // partial translation (build_memory_store, pending_updates) must be
                // rolled back to prevent false proofs from leaked constraints.
                let heap_snapshot = self.heap_state.snapshot_transient_rule_state();
                // Part of #4185 Fix 4: Snapshot modified_state_indices alongside heap.
                // On bail-out, leaked indices cause unconstrained state vars in output.
                let modified_snapshot = self.encode.modified_state_indices.clone();
                // Try inline translation.
                self.inline_walk_param_address_seeds = Some(address_seeds.clone());
                self.inline_walk_param_referent_seeds = Some(referent_seeds.clone());
                self.inline_walk_param_mut_owner_seeds = Some(mut_owner_seeds.clone());
                self.inline_walk_param_rustcall_mut_owner_seeds =
                    Some(rustcall_mut_owner_seeds.clone());
                self.inline_walk_param_native_dyn_seeds = Some(native_dyn_seeds.clone());
                self.inline_walk_param_readonly_ref_seeds = Some(readonly_ref_seeds.clone());
                let result = translate_inline_body(
                    self,
                    &body,
                    &params,
                    dcx.bb_idx,
                    &caller_vtable_ids,
                    Some(instance),
                    0,
                );
                self.inline_walk_param_address_seeds = None;
                self.inline_walk_param_referent_seeds = None;
                self.inline_walk_param_mut_owner_seeds = None;
                self.inline_walk_param_rustcall_mut_owner_seeds = None;
                self.inline_walk_param_native_dyn_seeds = None;
                self.inline_walk_param_readonly_ref_seeds = None;
                self.ref_resolution.inline_arg_subslice_seeds = None;
                // Part of #4163: Propagate subslice_len from the inlined
                // function's return local (0) to the caller's destination.
                // The inline walker may have seeded subslice_len[0] via
                // nested call to slice_from_raw_parts and Copy/Cast chains.
                // Part of #4163 D0: Capture return-local metadata BEFORE restore,
                // but insert into caller dest AFTER restore. Without this ordering,
                // the restore loop wipes dest when dest < callee_local_count.
                // The walk restores the caller's entries when it ends, so its
                // return local's entries are the ones it captured then.
                let (return_len, return_offset) =
                    std::mem::take(&mut self.ref_resolution.inline_return_subslice);
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
                    let interior = Self::try_extract_constant_addr(&params[0])
                        .is_some_and(|(_, offset)| offset != 0);
                    let base_known =
                        !interior && self.trace_deref_store_alloc_id(src_local).is_some();
                    let ref_target = (!self.local_has_multiple_whole_definitions(src_local))
                        .then(|| {
                            self.ref_resolution.ref_targets.get(&src_local).cloned().or_else(|| {
                                base_known
                                    .then(|| trace_pointer_identity_ref_target(self, src_local))
                                    .flatten()
                            })
                        })
                        .flatten()
                        .filter(|target| !interior || !target.projections.is_empty());
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
        // A known-call fast path or the simple bool-return helper is a model
        // of the callee, not a replay of its body: the dispatch spine states
        // Kani's unwinding assertion for a loop it skips
        // (`codegen_call.rs`, `model_call_unwinding_check`).
        self.call_replays_body = !used_pure_fast_path;
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
        match self.bind_call_arg_for_inline(arg, modified_locals, false) {
            InlineArgBinding::Bound(expr)
            | InlineArgBinding::BoundReferent(expr)
            | InlineArgBinding::BoundAddress(expr)
            | InlineArgBinding::ReadThrough(expr) => Some(expr),
            InlineArgBinding::Unresolved | InlineArgBinding::Refused(_) => None,
        }
    }

    /// Decide what the inline walker's parameter for `arg` binds to.
    ///
    /// Raw pointers keep their pointer value. Everything else goes through the
    /// referent cascade, and `bind_inline_referent_arg` decides what a
    /// reference whose referent the cascade did not resolve may bind to.
    pub(super) fn bind_call_arg_for_inline(
        &mut self,
        arg: &Operand,
        modified_locals: &std::collections::HashSet<usize>,
        comparison_callee: bool,
    ) -> InlineArgBinding {
        // A native selected reference FIELD is its own address. The legacy
        // ref-target cascade can report it as a Value after following a copy;
        // neither that tag nor matching scalar/address sorts is a fresh read.
        if arg.ty(self.body.locals()).ok().is_some_and(|ty| self.readonly_ref_seed(ty).is_some())
            && !self.closure_reference_producer_is_tracked(
                arg,
                &mut std::collections::HashSet::new(),
                &mut 16_384,
            )
        {
            self.record_sound_fallback_reason("inline_shared_ref_value_producer_unproven");
            return InlineArgBinding::Refused("inline_shared_ref_value_producer_unproven");
        }
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
                .or_else(|| self.resolve_ref_or_const_referent(arg, modified_locals))
                .map_or(InlineArgBinding::Unresolved, InlineArgBinding::Bound);
        }
        // A by-value `Option<&u64>`-like argument an aggregate built keeps the
        // reference's ADDRESS in its payload, which the walker would read as
        // the pointee's value (stmt/codegen_stmt_value_ref_payload.rs).
        if let Operand::Copy(place) | Operand::Move(place) = arg
            && place.projection.is_empty()
            && self.wide_ref_option_may_hold_address(place.local)
        {
            return InlineArgBinding::Refused("inline_option_ref_payload_holds_address");
        }
        match self.resolve_ref_or_const_referent_tagged(arg, modified_locals) {
            Some(referent) => self.bind_inline_referent_arg(arg, referent, comparison_callee),
            None => InlineArgBinding::Unresolved,
        }
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
            #[cfg(trust_toolchain)]
            Operand::RuntimeChecks(_) => {
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
            (Rvalue::Use(inner, ..), None) => self.unique_def_const_operand(inner, depth - 1),
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
