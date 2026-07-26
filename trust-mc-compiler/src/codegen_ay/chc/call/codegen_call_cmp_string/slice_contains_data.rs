// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Slice data resolution for `[T]::contains` — backing array + length extraction.
//!
//! Extracted from `slice_contains.rs` — Part of #4206.

use ay_bindings::Expr;
use tracing::debug;

use super::super::ChcCtx;
use super::super::chc_call_context::DispatchCallContext;
use super::super::codegen_call_misc::CallMisc;

/// Try to resolve the slice argument to (data_array, length) expressions.
///
/// For a `&[T]` argument, traces through references to find the underlying
/// array state variable (from a static array, Vec data, or allocated array)
/// and the slice length.
pub(in crate::codegen_ay::chc) fn resolve_slice_data(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
) -> Option<(Expr, Expr)> {
    let slice_arg = &dcx.args[0];
    let modified_locals = dcx.modified_locals;

    // Strategy 1: Resolve through ref_targets to find the underlying local.
    // For &STATIC_ARRAY[..], the slice ref points to a local that holds the
    // array data. We need to find the data array and length state vars.
    if let Some(slice_local) = resolve_ref_local(slice_arg, ctx) {
        // Check if the referenced local has array-typed state variables.
        // A slice is typically (data: Array, len: BV64) in state vars.
        if let Some(base_idx) = ctx.state_var_mgr.try_state_idx_for_local(slice_local) {
            let state_vars = &ctx.state_var_mgr.state_vars;
            // Look for an array sort at base_idx (data) and a BV sort at base_idx+1 (len).
            if base_idx + 1 < state_vars.len() {
                let data_sort = &state_vars[base_idx].1;
                let len_sort = &state_vars[base_idx + 1].1;

                if data_sort.array_sort().is_some() && len_sort.is_bitvec() {
                    let data_var = if modified_locals.contains(&slice_local) {
                        let out = &ctx.state_var_mgr.output_state_vars[base_idx];
                        Expr::var(&*out.0, out.1.clone())
                    } else {
                        Expr::var(&*state_vars[base_idx].0, data_sort.clone())
                    };
                    let len_var = if modified_locals.contains(&slice_local) {
                        let out = &ctx.state_var_mgr.output_state_vars[base_idx + 1];
                        Expr::var(&*out.0, out.1.clone())
                    } else {
                        Expr::var(&*state_vars[base_idx + 1].0, len_sort.clone())
                    };
                    debug!(
                        slice_local,
                        base_idx, "slice_contains: resolved slice data via ref_targets"
                    );
                    return Some((data_var, len_var));
                }
            }
        }
    }

    // Strategy 2: Try resolve_ref_or_const_referent for the slice argument.
    // This handles cases where the slice comes from a const or inline reference.
    if let Some(slice_expr) = ctx.resolve_ref_or_const_referent(slice_arg, modified_locals) {
        if slice_expr.sort().array_sort().is_some() {
            // The expression itself is an array — no separate length available.
            // Check if the array type has a known length from the MIR type.
            if let Some(len) = extract_slice_arg_type_len(slice_arg, ctx) {
                let len_expr = Expr::bitvec_const(len as u64, 64);
                return Some((slice_expr, len_expr));
            }
            debug!(bb_idx = dcx.bb_idx, "slice_contains: array expr found but length unknown");
        }
    }

    // Strategy 3: Trace through unsized coercion to find the underlying array.
    // When &[T] is created from &[T; N] via unsize coercion, ref_targets may not
    // propagate through the Cast(Unsize) (representation change from thin to fat
    // pointer). Scan MIR for the Cast statement, follow its source through
    // ref_targets to the array local, and read the Array-sort state var.
    // Modeled after try_resolve_len_from_unsize in codegen_stmt_rvalue.rs.
    if let Some(pair) = resolve_slice_via_unsize_trace(ctx, dcx) {
        return Some(pair);
    }

    None
}

/// Strategy 3: Trace through unsized coercion to find the underlying array.
///
/// For `&[T]` created from `&[T; N]` via unsize coercion, the MIR has:
///   `_slice = Cast(PointerCoercion(Unsize), _ref, &[T])`
///   `_ref = &_array_local`  (captured in ref_targets)
///   `_array_local = Aggregate(Array, [...])`
///
/// Scans MIR for the Cast(Unsize) statement, traces the source through
/// ref_targets to find the array local, and reads its Array-sort state var.
fn resolve_slice_via_unsize_trace(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
) -> Option<(Expr, Expr)> {
    use rustc_public::mir::{
        CastKind, Operand as MirOperand, PointerCoercion, Rvalue, StatementKind,
    };
    use rustc_public::ty::{RigidTy, TyKind};

    let slice_local = match &dcx.args[0] {
        MirOperand::Copy(place) | MirOperand::Move(place) if place.projection.is_empty() => {
            place.local
        }
        _ => return None,
    };

    for bb_data in &ctx.body.blocks {
        for stmt in &bb_data.statements {
            let StatementKind::Assign(lhs, rhs) = &stmt.kind else { continue };
            if lhs.local != slice_local || !lhs.projection.is_empty() {
                continue;
            }
            if let Rvalue::Cast(
                CastKind::PointerCoercion(PointerCoercion::Unsize),
                src_operand,
                _,
            ) = rhs
            {
                // Extract array length from source type (&[T; N] → N).
                let src_ty = src_operand.ty(ctx.body.locals()).ok()?;
                let array_len = {
                    let inner = match src_ty.kind() {
                        TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => inner,
                        _ => src_ty,
                    };
                    match inner.kind() {
                        TyKind::RigidTy(RigidTy::Array(_, len_const)) => {
                            len_const.eval_target_usize().ok()? as usize
                        }
                        _ => return None,
                    }
                };

                // Get source local from the operand.
                let src_local = match src_operand {
                    MirOperand::Copy(place) | MirOperand::Move(place)
                        if place.projection.is_empty() =>
                    {
                        place.local
                    }
                    _ => return None,
                };

                // Trace through ref_targets: src_local (&[T;N]) → array local ([T;N]).
                let array_local =
                    if let Some(ref_target) = ctx.ref_resolution.ref_targets.get(&src_local) {
                        ref_target.local
                    } else {
                        // ref_targets doesn't have an entry for src_local.
                        // Scan MIR for the Ref assignment: _src_local = &_array_local.
                        find_ref_source(ctx, src_local).unwrap_or(src_local)
                    };

                // Path A: Get state vars for the array local — expect Array sort.
                if let Some(base_idx) = ctx.state_var_mgr.try_state_idx_for_local(array_local) {
                    let state_vars = &ctx.state_var_mgr.state_vars;
                    if base_idx < state_vars.len() {
                        let data_sort = &state_vars[base_idx].1;
                        if data_sort.array_sort().is_some() {
                            let modified_locals = dcx.modified_locals;
                            let data_var = if modified_locals.contains(&array_local) {
                                let out = &ctx.state_var_mgr.output_state_vars[base_idx];
                                Expr::var(&*out.0, out.1.clone())
                            } else {
                                Expr::var(&*state_vars[base_idx].0, data_sort.clone())
                            };
                            let len_expr = Expr::bitvec_const(array_len as u64, 64);
                            debug!(
                                slice_local,
                                src_local,
                                array_local,
                                array_len,
                                "slice_contains: resolved via unsize trace (Strategy 3a)"
                            );
                            return Some((data_var, len_expr));
                        }
                    }
                }

                // Path B: Source is a promoted constant (&[T; N]). Try
                // resolve_ref_or_const_referent which checks const_ref_values.
                // This handles `_12 = const &['s','m','t','w','f']` where the
                // array data is in a compiler-allocated constant, not a local.
                if let Some(array_expr) =
                    ctx.resolve_ref_or_const_referent(src_operand, dcx.modified_locals)
                {
                    if array_expr.sort().array_sort().is_some() {
                        let len_expr = Expr::bitvec_const(array_len as u64, 64);
                        debug!(
                            slice_local,
                            src_local,
                            array_len,
                            "slice_contains: resolved via const_ref_values (Strategy 3b)"
                        );
                        return Some((array_expr, len_expr));
                    }
                }
            }
        }
    }
    None
}

/// Scan MIR for a `Rvalue::Ref` assignment to `target_local`, returning the
/// referenced local. For `_target = &_source`, returns `_source.local`.
fn find_ref_source(ctx: &ChcCtx<'_, '_>, target_local: usize) -> Option<usize> {
    use rustc_public::mir::{Rvalue, StatementKind};

    for bb_data in &ctx.body.blocks {
        for stmt in &bb_data.statements {
            let StatementKind::Assign(lhs, rhs) = &stmt.kind else { continue };
            if lhs.local != target_local || !lhs.projection.is_empty() {
                continue;
            }
            match rhs {
                Rvalue::Ref(_, _, place) if place.projection.is_empty() => {
                    return Some(place.local);
                }
                Rvalue::AddressOf(_, place) if place.projection.is_empty() => {
                    return Some(place.local);
                }
                _ => {}
            }
        }
    }
    None
}

/// Resolve a reference operand to the underlying MIR local index.
fn resolve_ref_local(arg: &rustc_public::mir::Operand, ctx: &ChcCtx<'_, '_>) -> Option<usize> {
    match arg {
        rustc_public::mir::Operand::Copy(place) | rustc_public::mir::Operand::Move(place)
            if place.projection.is_empty() =>
        {
            ctx.ref_resolution.ref_targets.get(&place.local).map(|t| t.local)
        }
        _ => None,
    }
}

/// Extract the array length from the MIR type of a slice argument.
/// For `&[T; N]` or `[T; N]`, returns N.
fn extract_slice_arg_type_len(
    arg: &rustc_public::mir::Operand,
    ctx: &ChcCtx<'_, '_>,
) -> Option<usize> {
    use rustc_public::ty::{RigidTy, TyKind};

    let ty = arg.ty(ctx.body.locals()).ok()?;
    // Peel references: &[T; N] -> [T; N]
    let inner = match ty.kind() {
        TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => inner,
        _ => ty,
    };
    // Check for array type [T; N]
    match inner.kind() {
        TyKind::RigidTy(RigidTy::Array(_, len_const)) => {
            len_const.eval_target_usize().ok().map(|n| n as usize)
        }
        _ => None,
    }
}

/// Extract a concrete usize from a BV constant expression.
pub(in crate::codegen_ay::chc) fn extract_const_usize(expr: &Expr) -> Option<usize> {
    use ay_bindings::ExprValue;
    if let ExprValue::BitVecConst { value, .. } = expr.value() {
        u64::try_from(value).ok().map(|v| v as usize)
    } else {
        None
    }
}
