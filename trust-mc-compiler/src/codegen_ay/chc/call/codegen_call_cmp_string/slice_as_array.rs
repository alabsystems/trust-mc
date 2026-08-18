// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! `core::slice::<impl [T]>::as_array::<N>()` stub for CHC codegen.
//!
//! Intercepts `as_array` calls and constrains the `Option<&[T; N]>` result:
//! - If `slice.len() == N`: return `Some(...)` (discriminant = 1)
//! - If `slice.len() != N`: return `None` (discriminant = 0)
//!
//! Without this handler, `as_array` falls through to `is_known_stdlib_unconstrained`
//! (which matches `slice::`), leaving the Option discriminant opaque. PDR
//! freely picks `None`, creating a spurious error path that blocks PROOF for
//! any harness using `assert_eq!` on slices (the macro expansion calls
//! `as_array()` to convert `&[T]` → `Option<&[T; N]>`).
//!
//! Part of #3620: blocks `&[T]` assert_eq! PROOF when as_array returns opaque None.

use ay_bindings::Expr;
use rustc_public::mir::BasicBlockIdx;
use rustc_public::ty::{GenericArgKind, RigidTy, TyKind};
use tracing::debug;

use super::super::ChcCtx;
use super::super::chc_call_context::DispatchCallContext;
use super::super::codegen_call_coerce::emit_sound_fallback_goto;

/// Detect if a callee path is a `slice::as_array` call.
///
/// Matches paths containing `as_array` on slice types:
/// - `core::slice::<impl [T]>::as_array`
/// - monomorphized `as_array::<N>` variants
pub(in crate::codegen_ay::chc) fn detect_slice_as_array(path: &str) -> bool {
    path.contains("as_array") && (path.contains("slice::") || path.contains("<["))
}

/// Try to codegen `<[T]>::as_array::<N>(&self) -> Option<&[T; N]>`.
///
/// Constrains the Option discriminant based on whether the slice length
/// equals the const generic N. Returns `true` if handled, `false` to
/// fall through.
pub(in crate::codegen_ay::chc) fn try_codegen_slice_as_array(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    target: BasicBlockIdx,
) -> bool {
    debug!(bb_idx = dcx.bb_idx, args = dcx.args.len(), "slice_as_array: entry");
    if dcx.args.is_empty() {
        return false;
    }

    let dest_local: usize = dcx.destination.local;

    // Step 1: Extract const generic N from the callee's FnDef generic args.
    let n = match extract_const_generic_n(ctx, dcx) {
        Some(n) => n,
        None => {
            debug!(bb_idx = dcx.bb_idx, "slice_as_array: could not extract const generic N");
            return false;
        }
    };
    debug!(bb_idx = dcx.bb_idx, n, "slice_as_array: extracted N");

    // Step 2: Resolve the slice length via translate_ptr_metadata.
    // `&[T]` fat pointers are encoded as single BV64 state vars (the pointer),
    // with the length tracked out-of-band in subslice_len, collections.len_state,
    // or MIR backward tracing. translate_ptr_metadata uses all these strategies.
    let slice_arg = &dcx.args[0];
    let len = ctx.translate_ptr_metadata(slice_arg, dcx.modified_locals).map(|len| len.into_expr());
    let len = match len {
        Some(expr) if expr.sort().is_bitvec() => expr,
        _ => {
            debug!(bb_idx = dcx.bb_idx, "slice_as_array: could not resolve slice length");
            return false;
        }
    };
    debug!(bb_idx = dcx.bb_idx, len_sort = ?len.sort(), "slice_as_array: resolved slice length");

    // Build the length comparison: len == N
    let len_width = len.sort().bitvec_width().unwrap_or(64);
    let n_expr = Expr::bitvec_const(n as u64, len_width);
    let len_eq_n = len.eq(n_expr);

    // Step 3: Emit the result via flattened Option fields.
    // Option<&[T; N]> is flattened to (discriminant, payload...) in state vars.
    // The discriminant is the key constraint: 1 if len == N, 0 if len != N.
    // The payload fields are unconstrained (PDR will infer appropriate values
    // when the discriminant is 1; they're irrelevant when discriminant is 0).
    emit_as_array_result(ctx, dcx, target, dest_local, len_eq_n)
}

/// Extract the const generic `N` from `as_array::<N>()` via the FnDef generic args.
///
/// Direction 3a: inspect `dcx.func.ty(ctx.body.locals())`, match
/// `RigidTy::FnDef(_, args)`, and pull the trailing `GenericArgKind::Const`.
fn extract_const_generic_n(ctx: &ChcCtx<'_, '_>, dcx: &DispatchCallContext<'_>) -> Option<usize> {
    let func_ty = dcx.func.ty(ctx.body.locals()).ok()?;
    let (_fn_def, fn_args) = match func_ty.kind() {
        TyKind::RigidTy(RigidTy::FnDef(def, args)) => (def, args),
        _ => return None,
    };

    // Find the const generic N — it's the last (or only) const generic arg.
    // For `as_array::<N>`, the generic args are [T, N] where T is the element
    // type and N is the const generic.
    for arg in fn_args.0.iter().rev() {
        if let GenericArgKind::Const(len_const) = arg {
            return len_const.eval_target_usize().ok().map(|v| v as usize);
        }
    }

    None
}

/// Emit the Option-shaped result constraint for as_array.
///
/// Constrains both the discriminant and payload of the flattened Option:
/// - discriminant (fld0): `ite(len == N, true, false)`
/// - payload (fld1): the input slice address (as_array returns a pointer to the
///   same underlying data as the slice, so `&[T; N]` == `&[T]`'s data ptr)
fn emit_as_array_result(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    target: BasicBlockIdx,
    dest_local: usize,
    len_eq_n: Expr,
) -> bool {
    if !ctx.flatten.flattened_tuple_locals.contains(&dest_local) {
        return false;
    }
    let Some(payload_expr) = resolve_payload_expr(ctx, dcx) else {
        emit_sound_fallback_goto(
            ctx,
            dcx.from_app,
            target,
            dcx.modified_locals,
            &[dest_local],
            dcx.stmt_constraints,
        );
        debug!(
            bb_idx = dcx.bb_idx,
            dest_local, "slice_as_array: payload unresolved, sound fallback"
        );
        return true;
    };

    let field_values = [
        Some(ctx.reshape_flattened_bool_field_for_call(dest_local, 0, len_eq_n)),
        Some(payload_expr),
    ];
    if !ctx.emit_flattened_call_fields(
        dest_local,
        &field_values,
        dcx.from_app,
        target,
        dcx.modified_locals,
        dcx.stmt_constraints,
    ) {
        return false;
    }
    debug!(
        bb_idx = dcx.bb_idx,
        dest_local, "slice_as_array: emitted discriminant + payload constraint"
    );
    true
}

/// Resolve the payload expression for `as_array`: the returned array reference
/// shares the same data pointer as the input slice.
fn resolve_payload_expr(ctx: &ChcCtx<'_, '_>, dcx: &DispatchCallContext<'_>) -> Option<Expr> {
    // Extract the slice argument's local index.
    let arg_local = match &dcx.args[0] {
        rustc_public::mir::Operand::Copy(place) | rustc_public::mir::Operand::Move(place)
            if place.projection.is_empty() =>
        {
            place.local
        }
        _ => return None,
    };

    // Get the slice argument's state variable expression.
    let arg_idx = ctx.state_var_mgr.try_state_idx_for_local(arg_local)?;
    let (arg_name, arg_sort) = if dcx.modified_locals.contains(&arg_local) {
        let out = ctx.state_var_mgr.output_state_vars.get(arg_idx)?;
        (&out.0, &out.1)
    } else {
        let sv = ctx.state_var_mgr.state_vars.get(arg_idx)?;
        (&sv.0, &sv.1)
    };
    Some(Expr::var(&**arg_name, arg_sort.clone()))
}
