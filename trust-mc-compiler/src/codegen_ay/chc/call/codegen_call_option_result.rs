// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Option/Result predicate, unwrap, and combinator stubs.
//!
//! Extracted from include!() to proper module via extension trait pattern.
//! Part of #2306: include!() to proper module migration.
//! Part of #2381: Migrated to ChcCallContext to eliminate too_many_arguments.

use ay_bindings::Expr;
use rustc_public::ty::{GenericArgKind, RigidTy, Ty, TyKind};

use super::ChcCtx;
use super::chc_call_context::ChcCallContext;
use crate::args::ChcTrackLevel;
use crate::codegen_ay::types::ptr_sort;
use tracing::debug;

/// Extension trait for Option/Result predicate, unwrap, and combinator call handling on `ChcCtx`.
pub(in crate::codegen_ay::chc) trait CallOptionResult {
    /// Shared helper: constrain destination with `result_expr` and emit goto rule.
    /// Falls back to unconstrained goto when `result_expr` is None.
    fn emit_stub_call_result(&mut self, result_expr: Option<Expr>, cx: &ChcCallContext<'_>);

    fn codegen_call_collection_predicate(&mut self, cx: &ChcCallContext<'_>);
    fn codegen_call_option_predicate(&mut self, cx: &ChcCallContext<'_>);
    fn codegen_call_result_predicate(&mut self, cx: &ChcCallContext<'_>);
    fn codegen_call_unwrap_or(&mut self, cx: &ChcCallContext<'_>);
    fn codegen_call_unwrap_expect(&mut self, cx: &ChcCallContext<'_>);
    fn codegen_call_unwrap_or_else(&mut self, cx: &ChcCallContext<'_>);
    fn codegen_call_option_copied(&mut self, cx: &ChcCallContext<'_>);
    fn codegen_call_combinator(&mut self, cx: &ChcCallContext<'_>);
}

impl<'tcx, 'body> CallOptionResult for ChcCtx<'tcx, 'body> {
    fn emit_stub_call_result(&mut self, result_expr: Option<Expr>, cx: &ChcCallContext<'_>) {
        self.emit_stub_call_result_with_extra(result_expr, cx, Vec::new());
    }

    fn codegen_call_collection_predicate(&mut self, cx: &ChcCallContext<'_>) {
        debug!("collection_predicate_stub stub={:?} dest={}", cx.stub, cx.destination.local);
        let result = self.translate_collection_predicate_call(cx.stub, cx.args, cx.modified_locals);
        self.emit_stub_call_result(result, cx);
    }

    /// Handle Option::is_some/is_none predicate stubs (Part of #1739).
    fn codegen_call_option_predicate(&mut self, cx: &ChcCallContext<'_>) {
        debug!("option_predicate_stub stub={:?} dest={}", cx.stub, cx.destination.local);
        let result = self.translate_option_predicate_call(cx.stub, cx.args, cx.modified_locals);
        self.emit_stub_call_result(result, cx);
    }

    /// Handle Result::is_ok/is_err predicate stubs (Part of #2125).
    fn codegen_call_result_predicate(&mut self, cx: &ChcCallContext<'_>) {
        debug!("result_predicate_stub stub={:?} dest={}", cx.stub, cx.destination.local);
        let result = self.translate_result_predicate_call(cx.stub, cx.args, cx.modified_locals);
        self.emit_stub_call_result(result, cx);
    }

    /// Handle Option::unwrap_or / Result::unwrap_or stubs (Part of #1836).
    fn codegen_call_unwrap_or(&mut self, cx: &ChcCallContext<'_>) {
        debug!("unwrap_or_stub stub={:?} dest={}", cx.stub, cx.destination.local);
        let result = self.translate_unwrap_or_call(cx.stub, cx.args, cx.modified_locals);
        // Part of #3914: Propagate ref_targets through unwrap_or so downstream
        // pointer derefs can resolve the pointee when the Some branch is taken.
        propagate_ref_target_from_operand(self, &cx.args[0], cx.destination.local);
        self.emit_stub_call_result(result, cx);
    }

    /// Handle Option::unwrap / Option::expect / Result::unwrap / Result::expect stubs (Part of #1836).
    fn codegen_call_unwrap_expect(&mut self, cx: &ChcCallContext<'_>) {
        debug!("unwrap_expect stub={:?} dest={}", cx.stub, cx.destination.local);
        let result = self.translate_unwrap_expect_call(cx.stub, cx.args, cx.modified_locals);
        // Part of #3866: Propagate layout size cache unconditionally for Result
        // unwrap/expect, regardless of whether translation succeeded. Layout
        // propagation is metadata-level: it copies cached (size, align) from
        // the source Result<Layout, _> local to the destination Layout local.
        // Gating on result.is_some() skips propagation when the DT/flattened
        // extraction fails, leaving downstream alloc/dealloc without concrete
        // size info and causing false PROOF on size-mismatch checks.
        if matches!(
            cx.stub,
            crate::codegen_ay::stubs::StubKind::ResultUnwrap
                | crate::codegen_ay::stubs::StubKind::ResultExpect
        ) {
            self.propagate_known_layout_size_from_operand(&cx.args[0], cx.destination.local);
        }
        // Part of #3914 / #4163: Propagate the full ref metadata bundle
        // through unwrap/expect so downstream pointer derefs, `size_of_val`,
        // and string backing recovery can resolve through the unwrapped local.
        propagate_unwrapped_ref_metadata_from_operand(self, &cx.args[0], cx.destination.local);
        let vtable_constraint =
            propagate_unwrapped_vtable_from_operand(self, &cx.args[0], cx.destination.local);
        self.emit_stub_call_result_with_extra(result, cx, vtable_constraint.into_iter().collect());
    }

    /// Handle Option::unwrap_or_else / Result::unwrap_or_else stubs (Part of #1836).
    fn codegen_call_unwrap_or_else(&mut self, cx: &ChcCallContext<'_>) {
        debug!("unwrap_or_else stub={:?} dest={}", cx.stub, cx.destination.local);
        let result = self.translate_unwrap_or_else_call(cx.stub, cx.args, cx.modified_locals);
        // Part of #3914: Propagate ref_targets through unwrap_or_else so downstream
        // pointer derefs can resolve the pointee when the Some branch is taken.
        propagate_ref_target_from_operand(self, &cx.args[0], cx.destination.local);
        self.emit_stub_call_result(result, cx);
    }

    /// Handle Option::copied/cloned — identity pass-through (#3348).
    ///
    /// In CHC encoding, Option<&T> and Option<T> have the same representation
    /// (HashMap stubs return raw V, not &V), so copied() is a field-by-field copy.
    /// Flattened path: copy discriminant (fld0) and payload (fld1) directly.
    /// DT path: translate source operand and constrain destination.
    fn codegen_call_option_copied(&mut self, cx: &ChcCallContext<'_>) {
        let dest_local: usize = cx.destination.local;
        debug!("option_copied stub dest={}", dest_local);

        // Flattened path: copy discriminant + payload fields from source to destination.
        if let Some(discr) =
            self.resolve_flattened_enum_discr_by_value(&cx.args[0], cx.modified_locals)
        {
            if let Some(mut payload) =
                self.resolve_flattened_enum_payload(&cx.args[0], cx.modified_locals)
            {
                if self.flatten.flattened_tuple_locals.contains(&dest_local)
                    && let Some(vec_idx) = self.try_state_idx_for_local(dest_local)
                {
                    // Part of #3348: Use pre-promotion raw value if available.
                    // This handles the BTreeMap get→copied→unwrap_or chain by
                    // bypassing the memory deref and using the raw select() result
                    // that was stored during promote_value_to_ref.
                    let src_local = match &cx.args[0] {
                        rustc_public::mir::Operand::Copy(p)
                        | rustc_public::mir::Operand::Move(p) => Some(p.local),
                        _ => None,
                    };
                    if let Some(sl) = src_local {
                        if let Some(raw_val) =
                            self.ref_resolution.promoted_raw_values.get(&sl).cloned()
                        {
                            payload = raw_val;
                        } else if let Some(loaded) =
                            deref_promoted_payload(self, &cx.args[0], dest_local, vec_idx, &payload)
                        {
                            payload = loaded;
                        }
                    } else if let Some(loaded) =
                        deref_promoted_payload(self, &cx.args[0], dest_local, vec_idx, &payload)
                    {
                        payload = loaded;
                    }

                    // Part of #3631: use shared helper for flattened field emission.
                    // Replaces manual fld0/fld1 constraint construction that was
                    // missing flattened_field_env Array-sort guard and sound_fallback
                    // recording on sort mismatch.
                    let field_values = vec![Some(discr), Some(payload)];
                    if self.emit_flattened_call_fields(
                        dest_local,
                        &field_values,
                        cx.from_app,
                        cx.target,
                        cx.modified_locals,
                        cx.stmt_constraints,
                    ) {
                        return;
                    }
                }
            }
        }

        // DT path or fallback: translate source operand and use standard result emission.
        let result = self.translate_operand_with_modified(&cx.args[0], cx.modified_locals);
        self.emit_stub_call_result(result, cx);
    }

    /// Handle Option::and_then / Option::ok_or_else / Result::map stubs (Part of #1836).
    fn codegen_call_combinator(&mut self, cx: &ChcCallContext<'_>) {
        let dest_local: usize = cx.destination.local;
        let Some(dest_vec_idx) = self.try_state_idx_for_local(dest_local) else {
            debug!(dest_local, "CHC: combinator dest not in state map — sound over-approx");
            self.record_sound_fallback_reason("state_idx_missing_combinator_dest");
            self.emit_stub_call_result(None, cx);
            return;
        };
        debug!("combinator_stub stub={:?} dest={}", cx.stub, dest_local);
        // Combinator needs dest_sort before translation, so we inline the
        // lookup rather than using emit_stub_call_result directly.
        let result = self
            .state_var_mgr
            .output_state_vars
            .get(dest_vec_idx)
            .map(|(_, sort)| sort.clone())
            .and_then(|out_sort| {
                self.translate_combinator_call(cx.stub, cx.args, cx.modified_locals, &out_sort)
            });
        self.emit_stub_call_result(result, cx);
    }
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Part of #3641: checked layout constructors cache `(size, align)` on the
    /// `Result<Layout, LayoutError>` local before `unwrap()` produces the bare
    /// `Layout` local later consumed by alloc/realloc. Preserve that concrete
    /// layout knowledge across the unwrap call terminator so downstream layout
    /// recovery can hit the direct cache instead of falling back.
    fn propagate_known_layout_size_from_operand(
        &mut self,
        operand: &rustc_public::mir::Operand,
        dest_local: usize,
    ) {
        if let rustc_public::mir::Operand::Copy(place) | rustc_public::mir::Operand::Move(place) =
            operand
            && let Some(pair) = self.known_layout_sizes.get(&place.local).copied()
        {
            self.known_layout_sizes.insert(dest_local, pair);
        }
    }
}

/// Part of #3914: Propagate ref_targets from an Option/Result operand to the
/// unwrapped destination. Follows the same pattern as `propagate_ref_target` in
/// `codegen_call_ptr_identity.rs:34-52` but takes an operand instead of a
/// pre-resolved local, since unwrap stubs receive `self` as args[0].
pub(in crate::codegen_ay::chc) fn propagate_ref_target_from_operand(
    ctx: &mut ChcCtx<'_, '_>,
    operand: &rustc_public::mir::Operand,
    dest_local: usize,
) {
    let src_local = match operand {
        rustc_public::mir::Operand::Copy(place) | rustc_public::mir::Operand::Move(place)
            if place.projection.is_empty() =>
        {
            place.local
        }
        _ => return,
    };
    if let Some(ref_target) = ctx.ref_resolution.ref_targets.get(&src_local).cloned() {
        ctx.ref_resolution.ref_targets.insert(dest_local, ref_target);
        ctx.ref_resolution.call_forwarded_raw_ptrs.insert(dest_local);
    }
}

/// Part of #4163: unwrap/expect on `Option<&mut str>` and similar reference
/// payloads must preserve the source local's ref metadata side tables on the
/// unwrapped destination. Mirror the statement path here so checked extraction
/// from `get_mut(..)` keeps backing and length data.
pub(in crate::codegen_ay::chc) fn propagate_unwrapped_ref_metadata_from_operand(
    ctx: &mut ChcCtx<'_, '_>,
    operand: &rustc_public::mir::Operand,
    dest_local: usize,
) {
    let src_local = match operand {
        rustc_public::mir::Operand::Copy(place) | rustc_public::mir::Operand::Move(place)
            if place.projection.is_empty() =>
        {
            place.local
        }
        _ => {
            clear_unwrapped_ref_metadata(ctx, dest_local);
            return;
        }
    };

    if let Some(ref_target) = ctx.ref_resolution.ref_targets.get(&src_local).cloned() {
        ctx.ref_resolution.ref_targets.insert(dest_local, ref_target);
        ctx.ref_resolution.call_forwarded_raw_ptrs.insert(dest_local);
    } else {
        ctx.ref_resolution.ref_targets.remove(&dest_local);
        ctx.ref_resolution.call_forwarded_raw_ptrs.remove(&dest_local);
    }

    copy_or_clear_expr(
        &ctx.ref_resolution.const_ref_values.get(&src_local).cloned(),
        &mut ctx.ref_resolution.const_ref_values,
        dest_local,
    );
    copy_or_clear_copy(
        &ctx.ref_resolution.const_ref_discriminants.get(&src_local).copied(),
        &mut ctx.ref_resolution.const_ref_discriminants,
        dest_local,
    );
    copy_or_clear_copy(
        &ctx.ref_resolution.const_ref_promoted_obj_ids.get(&src_local).copied(),
        &mut ctx.ref_resolution.const_ref_promoted_obj_ids,
        dest_local,
    );
    copy_or_clear_expr(
        &ctx.ref_resolution.const_ref_slice_views.get(&src_local).cloned(),
        &mut ctx.ref_resolution.const_ref_slice_views,
        dest_local,
    );
    copy_or_clear_expr(
        &ctx.ref_resolution.subslice_len.get(&src_local).cloned(),
        &mut ctx.ref_resolution.subslice_len,
        dest_local,
    );
    copy_or_clear_expr(
        &ctx.ref_resolution.subslice_offset.get(&src_local).cloned(),
        &mut ctx.ref_resolution.subslice_offset,
        dest_local,
    );
}

/// Propagate vtable side metadata from an Option/Result wrapper local to the
/// local produced by unwrap/expect, but only for dyn-bearing destinations.
///
/// Raw pointer `as_ref()` stores the dyn vtable on the `Option<&dyn T>` result
/// as side metadata; unwrap must move that metadata to the `&dyn T` local so the
/// following virtual call can devirtualize without falling back to an unknown
/// vtable. Prefer the compile-time side table over `known_vtable_expr_for_local`
/// so late vtable state created for the wrapper local does not shadow the
/// concrete vtable expression already captured by the raw-pointer call.
fn propagate_unwrapped_vtable_from_operand(
    ctx: &mut ChcCtx<'_, '_>,
    operand: &rustc_public::mir::Operand,
    dest_local: usize,
) -> Option<Expr> {
    if !local_ty_involves_dyn_trait(ctx, dest_local) {
        clear_unwrapped_vtable_metadata(ctx, dest_local);
        return None;
    }

    let src_local = match operand {
        rustc_public::mir::Operand::Copy(place) | rustc_public::mir::Operand::Move(place)
            if place.projection.is_empty() =>
        {
            place.local
        }
        _ => {
            clear_unwrapped_vtable_metadata(ctx, dest_local);
            return None;
        }
    };

    let Some(vtable_expr) = ctx
        .dyn_vtable_ids
        .get(&src_local)
        .cloned()
        .or_else(|| ctx.known_vtable_expr_for_local(src_local))
    else {
        clear_unwrapped_vtable_metadata(ctx, dest_local);
        return None;
    };

    ctx.dyn_vtable_ids.insert(dest_local, vtable_expr.clone());
    if ctx.vtable_state_vars.contains_key(&dest_local) {
        ctx.capture_known_vtable_discriminant(dest_local, vtable_expr)
    } else {
        None
    }
}

fn clear_unwrapped_vtable_metadata(ctx: &mut ChcCtx<'_, '_>, dest_local: usize) {
    ctx.dyn_vtable_ids.remove(&dest_local);
    if ctx.vtable_state_vars.contains_key(&dest_local) {
        ctx.clear_known_vtable_discriminant(dest_local);
    }
}

fn local_ty_involves_dyn_trait(ctx: &ChcCtx<'_, '_>, local_idx: usize) -> bool {
    ctx.body.locals().get(local_idx).is_some_and(|decl| ty_involves_dyn_trait(decl.ty))
}

fn ty_involves_dyn_trait(ty: Ty) -> bool {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Dynamic(..)) => true,
        TyKind::RigidTy(
            RigidTy::Ref(_, inner, _)
            | RigidTy::RawPtr(inner, _)
            | RigidTy::Slice(inner)
            | RigidTy::Pat(inner, _),
        ) => ty_involves_dyn_trait(inner),
        TyKind::RigidTy(RigidTy::Array(inner, _)) => ty_involves_dyn_trait(inner),
        TyKind::RigidTy(RigidTy::Tuple(fields)) => {
            fields.iter().copied().any(ty_involves_dyn_trait)
        }
        TyKind::RigidTy(
            RigidTy::Adt(_, args)
            | RigidTy::FnDef(_, args)
            | RigidTy::Closure(_, args)
            | RigidTy::Coroutine(_, args)
            | RigidTy::CoroutineClosure(_, args)
            | RigidTy::CoroutineWitness(_, args),
        ) => args
            .0
            .iter()
            .any(|arg| matches!(arg, GenericArgKind::Type(inner) if ty_involves_dyn_trait(*inner))),
        _ => false,
    }
}

fn clear_unwrapped_ref_metadata(ctx: &mut ChcCtx<'_, '_>, dest_local: usize) {
    ctx.ref_resolution.ref_targets.remove(&dest_local);
    ctx.ref_resolution.call_forwarded_raw_ptrs.remove(&dest_local);
    ctx.ref_resolution.const_ref_values.remove(&dest_local);
    ctx.ref_resolution.const_ref_discriminants.remove(&dest_local);
    ctx.ref_resolution.const_ref_promoted_obj_ids.remove(&dest_local);
    ctx.ref_resolution.const_ref_slice_views.remove(&dest_local);
    ctx.ref_resolution.subslice_len.remove(&dest_local);
    ctx.ref_resolution.subslice_offset.remove(&dest_local);
}

fn copy_or_clear_expr(
    value: &Option<Expr>,
    map: &mut std::collections::HashMap<usize, Expr>,
    dest_local: usize,
) {
    if let Some(expr) = value {
        map.insert(dest_local, expr.clone());
    } else {
        map.remove(&dest_local);
    }
}

fn copy_or_clear_copy<T: Copy>(
    value: &Option<T>,
    map: &mut std::collections::HashMap<usize, T>,
    dest_local: usize,
) {
    if let Some(value) = value {
        map.insert(dest_local, *value);
    } else {
        map.remove(&dest_local);
    }
}

/// Part of #3348: Extract the pointee type V from Option<&V>.
///
/// Used by `codegen_call_option_copied` to dereference promoted pointers.
/// Returns None if the type is not `Option<&V>`.
fn extract_option_ref_pointee(ty: rustc_public::ty::Ty) -> Option<rustc_public::ty::Ty> {
    use rustc_public::CrateDef;
    use rustc_public::ty::{GenericArgKind, RigidTy, TyKind};
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Adt(def, args)) if def.trimmed_name() == "Option" => {
            let inner_ty = match args.0.first() {
                Some(GenericArgKind::Type(ty)) => *ty,
                _ => return None,
            };
            match inner_ty.kind() {
                TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) => Some(pointee),
                _ => None,
            }
        }
        _ => None,
    }
}

/// Part of #3348: When payload is a promoted pointer (bv64) and destination expects
/// a non-pointer value (e.g. bv32 for Option<u32>), load through typed memory.
/// Without this, BV width coercion truncates the pointer address, losing the value.
fn deref_promoted_payload(
    ctx: &mut ChcCtx<'_, '_>,
    src_arg: &rustc_public::mir::Operand,
    dest_local: usize,
    vec_idx: usize,
    payload: &Expr,
) -> Option<Expr> {
    if ctx.track_level < ChcTrackLevel::Mem || *payload.sort() != ptr_sort() {
        return None;
    }
    let (_, out_sort) = ctx.state_var_mgr.output_state_vars.get(vec_idx + 1)?;
    if *out_sort == ptr_sort() {
        return None;
    }
    let src_local = match src_arg {
        rustc_public::mir::Operand::Copy(p) | rustc_public::mir::Operand::Move(p) => p.local,
        _ => dest_local,
    };
    let src_ty = ctx.body.locals()[src_local].ty;
    let pointee_ty = extract_option_ref_pointee(src_ty)?;
    let loaded = ctx.load_from_memory_untyped(payload.clone(), pointee_ty)?;
    debug!(
        "option_copied_deref: dest={} payload_sort={:?} loaded_sort={:?}",
        dest_local,
        payload.sort(),
        loaded.sort(),
    );
    Some(loaded)
}
