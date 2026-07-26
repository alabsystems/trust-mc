// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Pointer identity/passthrough stubs: ptr.cast, Box::into_raw, NonNull passthrough,
//! and NonNull::dangling.
//!
//! Split from codegen_call_ptr.rs per #3199.
//! ptr.cast and NonNull passthrough are identity operations (output = input).
//! NonNull::dangling is a non-null pointer constructor (output > 0).

use ay_bindings::Expr;
use tracing::{debug, warn};

use super::ChcCtx;
use super::chc_call_context::ChcCallContext;
use super::codegen_call_coerce::{CallCoerce, emit_sound_fallback_goto};
use super::codegen_call_ptr_identity_cast::codegen_call_ptr_cast_impl;
pub(super) use super::codegen_call_ptr_identity_ref_target::propagate_ref_target;
pub(in crate::codegen_ay::chc) use super::codegen_call_ptr_identity_ref_target::trace_pointer_identity_ref_target;
use super::codegen_call_ptr_nonnull::{nonnull_new_option_wrap, try_emit_nonnull_new_flattened};
use super::codegen_rules::CodegenRules;
use crate::codegen_ay::stubs::StubKind;

/// Extension trait for pointer identity/passthrough call handling on `ChcCtx`.
pub(in crate::codegen_ay::chc) trait CallPtrIdentity {
    fn codegen_call_ptr_cast(&mut self, cx: &ChcCallContext<'_>);
    fn codegen_call_box_into_raw(&mut self, cx: &ChcCallContext<'_>);
    fn codegen_call_box_from_raw_in(&mut self, cx: &ChcCallContext<'_>);
    fn codegen_call_rc_arc_into_raw(&mut self, cx: &ChcCallContext<'_>);
    fn codegen_call_rc_arc_from_raw(&mut self, cx: &ChcCallContext<'_>);
    fn codegen_call_nonnull_passthrough(&mut self, cx: &ChcCallContext<'_>);
    fn codegen_call_nonnull_dangling(&mut self, cx: &ChcCallContext<'_>);
}

/// Shared `into_raw` identity: extract pointer storage, propagate alloc+ref_target.
/// Used by Box::into_raw and Rc/Arc::into_raw (Part of #4139).
fn codegen_into_raw_shared(ctx: &mut ChcCtx<'_, '_>, cx: &ChcCallContext<'_>, label: &'static str) {
    let dest_local: usize = cx.destination.local;
    debug!("{label} dest={dest_local}");

    let ptr_expr = cx
        .args
        .first()
        .and_then(|arg| ctx.translate_operand_with_modified(arg, cx.modified_locals))
        .and_then(|expr| ctx.extract_pointer_storage_expr(&expr));
    let src_local = extract_src_local(cx);

    if let Some(ptr_expr) = ptr_expr
        && let Some((_, dest_var)) = ctx.resolve_destination(dest_local)
    {
        let ptr_obj_id = try_extract_data_obj_id(&ptr_expr);
        if let Some(eq) =
            ctx.make_coerced_eq_constraint(&dest_var, ptr_expr, dest_var.sort(), dest_local, label)
        {
            propagate_alloc_id_with_obj(ctx, dest_local, src_local, ptr_obj_id);
            propagate_ref_target(ctx, dest_local, src_local, ptr_obj_id);
            ctx.clear_known_vtable_discriminant(dest_local);
            let new_output_args = ctx.build_output_args(cx.modified_locals, &[dest_local]);
            ctx.emit_goto_rule_extra(
                cx.from_app,
                cx.target,
                &new_output_args,
                cx.stmt_constraints,
                [eq],
            );
            return;
        }
    }

    ctx.known_alloc_ids.remove(&dest_local);
    ctx.clear_known_vtable_discriminant(dest_local);
    warn!(fn_name = %ctx.fn_name, "CHC: {label} unresolved; emitting unconstrained transition");
    emit_sound_fallback_goto(
        ctx,
        cx.from_app,
        cx.target,
        cx.modified_locals,
        &[dest_local],
        cx.stmt_constraints,
    );
}

/// Shared `from_raw` identity: wrap raw pointer, propagate alloc+ref_target+vtable.
/// Used by Box::from_raw_in and Rc/Arc::from_raw (Part of #4139).
fn codegen_from_raw_shared(ctx: &mut ChcCtx<'_, '_>, cx: &ChcCallContext<'_>, label: &'static str) {
    let dest_local: usize = cx.destination.local;
    debug!("{label} dest={dest_local}");

    let raw_arg_expr = cx.args.first().and_then(|arg| {
        ctx.translate_operand_with_modified(arg, cx.modified_locals)
            .or_else(|| ctx.resolve_ref_operand(arg, cx.modified_locals))
    });
    let src_local = extract_src_local(cx);

    if let Some(raw_arg_expr) = raw_arg_expr
        && let Some((_, dest_var)) = ctx.resolve_destination(dest_local)
    {
        if let Some(eq) = ctx.make_coerced_eq_constraint(
            &dest_var,
            raw_arg_expr.clone(),
            dest_var.sort(),
            dest_local,
            label,
        ) {
            let mut extra = vec![eq];
            let ptr_obj_id = try_extract_data_obj_id(&raw_arg_expr);
            propagate_alloc_id_with_obj(ctx, dest_local, src_local, ptr_obj_id);
            propagate_ref_target(ctx, dest_local, src_local, ptr_obj_id);
            let vtable = from_raw_vtable_constraint(ctx, dest_local, src_local, &raw_arg_expr);
            if let Some(vtable_constraint) = vtable {
                extra.push(vtable_constraint);
            } else {
                ctx.clear_known_vtable_discriminant(dest_local);
            }
            let new_output_args = ctx.build_output_args(cx.modified_locals, &[dest_local]);
            ctx.emit_goto_rule_extra(
                cx.from_app,
                cx.target,
                &new_output_args,
                cx.stmt_constraints,
                extra,
            );
            return;
        }
    }

    ctx.known_alloc_ids.remove(&dest_local);
    ctx.clear_known_vtable_discriminant(dest_local);
    warn!(fn_name = %ctx.fn_name, "CHC: {label} unresolved; emitting unconstrained transition");
    emit_sound_fallback_goto(
        ctx,
        cx.from_app,
        cx.target,
        cx.modified_locals,
        &[dest_local],
        cx.stmt_constraints,
    );
}

fn extract_src_local(cx: &ChcCallContext<'_>) -> Option<usize> {
    cx.args.first().and_then(|arg| match arg {
        rustc_public::mir::Operand::Copy(place) | rustc_public::mir::Operand::Move(place)
            if place.projection.is_empty() =>
        {
            Some(place.local)
        }
        _ => None,
    })
}

pub(super) fn propagate_alloc_id(
    ctx: &mut ChcCtx<'_, '_>,
    dest_local: usize,
    src_local: Option<usize>,
) {
    propagate_alloc_id_with_obj(ctx, dest_local, src_local, None);
}

pub(super) fn propagate_alloc_id_with_obj(
    ctx: &mut ChcCtx<'_, '_>,
    dest_local: usize,
    src_local: Option<usize>,
    ptr_obj_id: Option<u32>,
) {
    if let Some(obj_id) = src_local
        .and_then(|sl| ctx.known_alloc_ids.get(&sl).copied())
        .or_else(|| src_local.and_then(|sl| ctx.trace_deref_store_alloc_id(sl)))
        .or(ptr_obj_id)
    {
        ctx.known_alloc_ids.insert(dest_local, obj_id);
        ctx.ref_resolution.alloc_result_locals.insert(dest_local);
    } else {
        ctx.known_alloc_ids.remove(&dest_local);
    }
}

pub(super) fn try_extract_data_obj_id(ptr_expr: &Expr) -> Option<u32> {
    // obj_id 0 is the null/invalid sentinel: allocations use obj_id >= 2 and
    // the promoted-const region uses obj_id == 1. Refuse to propagate obj_id 0
    // as a "known allocation" — otherwise `propagate_alloc_id_with_obj` records
    // null-pointer-derived locals in `alloc_result_locals`, which makes the
    // `NullPointerDereference` MIR assert suppression (#3094) silently elide
    // the check, producing a false PROOF for `unsafe { *ptr::null::<T>() }`.
    ChcCtx::try_extract_obj_id(ptr_expr)
        .or_else(|| {
            let width = ptr_expr.sort().bitvec_width()?;
            let ptr_width = crate::codegen_ay::types::POINTER_WIDTH;
            (width == 2 * ptr_width).then(|| {
                let data_ptr = ptr_expr.clone().extract(ptr_width - 1, 0);
                ChcCtx::try_extract_obj_id(&data_ptr)
            })?
        })
        .filter(|&obj_id| obj_id != 0)
}

impl<'tcx, 'body> CallPtrIdentity for ChcCtx<'tcx, 'body> {
    fn codegen_call_box_into_raw(&mut self, cx: &ChcCallContext<'_>) {
        codegen_into_raw_shared(self, cx, "box_into_raw");
    }

    fn codegen_call_box_from_raw_in(&mut self, cx: &ChcCallContext<'_>) {
        codegen_from_raw_shared(self, cx, "box_from_raw_in");
    }

    /// Part of #4139: Rc/Arc::into_raw — same identity as Box::into_raw.
    fn codegen_call_rc_arc_into_raw(&mut self, cx: &ChcCallContext<'_>) {
        codegen_into_raw_shared(self, cx, "rc_arc_into_raw");
    }

    /// Part of #4139: Rc/Arc::from_raw — same identity as Box::from_raw_in.
    fn codegen_call_rc_arc_from_raw(&mut self, cx: &ChcCallContext<'_>) {
        codegen_from_raw_shared(self, cx, "rc_arc_from_raw");
    }

    /// Handle pointer cast stubs (Part of #2196).
    ///
    /// `ptr.cast::<U>()` and `ptr.cast_const()` are identity operations at
    /// the SMT level — the pointer bitvector representation doesn't change.
    fn codegen_call_ptr_cast(&mut self, cx: &ChcCallContext<'_>) {
        codegen_call_ptr_cast_impl(self, cx);
    }

    /// NonNull pointer identity passthrough (CHC port of BMC alloc_ptr.rs:130).
    ///
    /// Handles NonNullAsNonNullPtr, NonNullNew (new/new_unchecked), and NonNullCast.
    /// For new_unchecked/AsNonNullPtr/Cast these are identity operations at the SMT
    /// level — the pointer bitvector representation doesn't change.
    /// For NonNull::new (which returns Option<NonNull<T>>), the pointer is wrapped
    /// in Some(ptr) when the destination sort is an Option-like datatype, or the
    /// flattened is_some+payload fields are set when the destination is flattened.
    /// Part of #3184: fixes 9 box_alloc CTREX regressions.
    /// Part of #3589: routes NonNullNew/NonNullCast here instead of unconstrained
    /// catch-all, preserving allocation identity for Rc store-to-load forwarding.
    fn codegen_call_nonnull_passthrough(&mut self, cx: &ChcCallContext<'_>) {
        let dest_local: usize = cx.destination.local;
        debug!("nonnull_passthrough stub={:?} dest={}", cx.stub, dest_local);

        let ptr_expr = cx.args.first().and_then(|arg| {
            self.translate_operand_with_modified(arg, cx.modified_locals)
                .or_else(|| self.resolve_ref_operand(arg, cx.modified_locals))
        });
        let src_local = extract_src_local(cx);

        // NonNull::new flattened Option path (is_some Bool + payload BV).
        if matches!(cx.stub, StubKind::NonNullNew) {
            if let Some(ref ptr) = ptr_expr {
                let ptr_obj_id = try_extract_data_obj_id(ptr);
                if try_emit_nonnull_new_flattened(self, cx, ptr.clone(), src_local, ptr_obj_id) {
                    debug!(dest_local, "nonnull_passthrough: emitted flattened Option");
                    return;
                }
            }
        }

        if let Some(ptr) = ptr_expr
            && let Some((_, dest_var)) = self.resolve_destination(dest_local)
        {
            let ptr_obj_id = try_extract_data_obj_id(&ptr);
            let value_expr =
                nonnull_new_option_wrap(self, cx.stub, ptr, dest_var.sort(), dest_local);
            if let Some(eq) = self.make_coerced_eq_constraint(
                &dest_var,
                value_expr,
                dest_var.sort(),
                dest_local,
                "codegen_call_nonnull_passthrough",
            ) {
                propagate_alloc_id_with_obj(self, dest_local, src_local, ptr_obj_id);
                propagate_ref_target(self, dest_local, src_local, ptr_obj_id);
                let mut extra = vec![eq];
                if let Some(src) = src_local
                    && let Some(vc) =
                        self.propagate_vtable_discriminant(src, dest_local).or_else(|| {
                            self.known_vtable_expr_for_local(src).and_then(|vtable| {
                                self.capture_known_vtable_constraint(dest_local, vtable)
                            })
                        })
                {
                    extra.push(vc);
                }
                let new_output_args = self.build_output_args(cx.modified_locals, &[dest_local]);
                self.emit_goto_rule_extra(
                    cx.from_app,
                    cx.target,
                    &new_output_args,
                    cx.stmt_constraints,
                    extra,
                );
                return;
            }
        }
        // Fallback: leave unconstrained (same as current behavior).
        self.known_alloc_ids.remove(&dest_local);
        warn!(
            fn_name = %self.fn_name,
            "CHC: nonnull passthrough unresolved; emitting unconstrained transition"
        );
        emit_sound_fallback_goto(
            self,
            cx.from_app,
            cx.target,
            cx.modified_locals,
            &[dest_local],
            cx.stmt_constraints,
        );
    }

    /// NonNull::dangling(): constrain destination to be non-zero.
    ///
    /// CHC equivalent of BMC's `codegen_nonnull_dangling_stub` which sets
    /// dest = alignment. The CHC version uses a weaker constraint (> 0)
    /// because exact alignment is not needed for safety verification —
    /// only the non-null property matters for `is_null()` checks.
    ///
    /// Without this handler, NonNullDangling falls through to the
    /// `is_nonnull_extra` catch-all which leaves the destination fully
    /// unconstrained, allowing the solver to pick null (0) and produce
    /// a spurious CTREX. Part of #3136: encoding gap fix.
    fn codegen_call_nonnull_dangling(&mut self, cx: &ChcCallContext<'_>) {
        let dest_local: usize = cx.destination.local;
        debug!("nonnull_dangling stub dest={}", dest_local);

        if let Some((_, dest_var)) = self.resolve_destination(dest_local) {
            if let Some(width) = dest_var.sort().bitvec_width() {
                let zero = Expr::bitvec_const(0u64, width);
                let nonzero = dest_var.clone().bvugt(zero);

                // Part of #3176: when extra_pointer_checks is on, mark the
                // dangling pointer as provenance-invalid so pointer arithmetic
                // checks can detect use of never-allocated addresses.
                let mut extra: Vec<Expr> = vec![nonzero];
                if self.extra_pointer_checks && !self.int_lift {
                    if let Some((obj_id, _offset)) = self.split_pointer(&dest_var) {
                        let current_valid = self.current_obj_valid_array();
                        let invalidated = current_valid.store(obj_id, Expr::bool_const(false));
                        extra.push(super::codegen_expr_heap::obj_valid_out().eq(invalidated));
                        self.mark_heap_metadata_modified();
                        debug!(
                            "#3176: invalidated obj_valid for NonNull::dangling (extra_pointer_checks)"
                        );
                    }
                }

                let new_output_args = self.build_output_args(cx.modified_locals, &[dest_local]);
                self.emit_goto_rule_extra(
                    cx.from_app,
                    cx.target,
                    &new_output_args,
                    cx.stmt_constraints,
                    extra,
                );
                return;
            }
        }
        // Fallback: leave unconstrained (sound over-approximation).
        warn!(
            fn_name = %self.fn_name,
            "CHC: nonnull_dangling: cannot constrain (dest unresolved or non-BV sort)"
        );
        let new_output_args = self.build_output_args(cx.modified_locals, &[dest_local]);
        self.emit_goto_rule(cx.from_app, cx.target, &new_output_args, cx.stmt_constraints);
    }
}

/// Shared vtable constraint propagation for Box/Rc/Arc::from_raw (Part of #4139).
///
/// Tries three strategies in order:
/// 1. Direct vtable lookup from source local's `dyn_vtable_ids`
/// 2. Extract vtable from fat pointer BV upper half
/// 3. Resolve unique wrapped dyn vtable from destination type
fn from_raw_vtable_constraint(
    ctx: &mut ChcCtx<'_, '_>,
    dest_local: usize,
    src_local: Option<usize>,
    raw_arg_expr: &Expr,
) -> Option<Expr> {
    src_local
        .and_then(|sl| ctx.dyn_vtable_ids.get(&sl).cloned())
        .and_then(|vtable_expr| ctx.capture_known_vtable_constraint(dest_local, vtable_expr))
        .or_else(|| {
            let width = raw_arg_expr.sort().bitvec_width()?;
            if width != 2 * crate::codegen_ay::types::POINTER_WIDTH {
                return None;
            }
            let ptr_width = crate::codegen_ay::types::POINTER_WIDTH;
            let vtable_expr = raw_arg_expr.clone().extract(2 * ptr_width - 1, ptr_width);
            ctx.capture_known_vtable_constraint(dest_local, vtable_expr)
        })
        .or_else(|| {
            let dest_ty = ctx.body.locals()[dest_local].ty;
            let vtable_id = ctx.resolve_unique_wrapped_dyn_vtable_id(dest_ty)?;
            let vtable_expr =
                Expr::bitvec_const(vtable_id as u128, crate::codegen_ay::types::POINTER_WIDTH);
            ctx.capture_known_vtable_constraint(dest_local, vtable_expr)
        })
}
