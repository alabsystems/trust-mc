// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! `[T]::contains` stub for CHC codegen.
//!
//! Intercepts `core::slice::<impl [T]>::contains` calls and builds a
//! disjunction over array elements: `select(data, 0) == target || ... ||
//! select(data, len-1) == target`. Without this, the call falls through to
//! `is_known_stdlib_unconstrained` which leaves the result opaque, causing
//! UNKNOWN when PDR cannot infer the function semantics.
//!
//! Part of #3607 Direction D2: [T]::contains stub for Wave2 Phase 1.

use ay_bindings::Expr;
use rustc_public::mir::BasicBlockIdx;
use tracing::debug;

use super::super::ChcCtx;
use super::super::chc_call_context::DispatchCallContext;
use super::super::codegen_call_coerce::CallCoerce;
use super::super::codegen_call_misc::CallMisc;
use super::super::codegen_rules::CodegenRules;
use super::slice_contains_data::{extract_const_usize, resolve_slice_data};

/// Maximum slice length for unrolled disjunction. Longer slices fall through
/// to the generic handler.
const MAX_UNROLL_LENGTH: usize = 64;

/// Detect if a callee path is a `slice::contains` call (NOT `contains_key`).
pub(in crate::codegen_ay::chc) fn detect_slice_contains(path: &str) -> bool {
    // Must end with "::contains" and NOT "::contains_key"
    if !path.ends_with("::contains") {
        return false;
    }
    // Must be on a slice type, not HashMap/BTreeMap/Vec/etc.
    // Patterns: "core::slice::<impl [T]>::contains", "<[T]>::contains"
    (path.contains("slice::") || path.contains("<["))
        && !path.contains("HashMap")
        && !path.contains("BTreeMap")
        && !path.contains("BTreeSet")
        && !path.contains("HashSet")
        && !path.contains("Vec")
        && !path.contains("String")
}

/// Try to codegen `[T]::contains(&self, &T) -> bool` as a disjunction
/// of array element comparisons.
///
/// Returns `true` if the call was handled, `false` to fall through.
pub(in crate::codegen_ay::chc) fn try_codegen_slice_contains(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    target: BasicBlockIdx,
) -> bool {
    debug!(bb_idx = dcx.bb_idx, args = dcx.args.len(), "slice_contains: entry");
    if dcx.args.len() < 2 {
        return false;
    }

    let dest_local: usize = dcx.destination.local;

    // Resolve the target element value. `contains(&self, x: &T) -> bool` takes
    // args[1] as `&T`. We need the T value, not the pointer. Dereference through
    // ref_targets first, then fall back to resolve_ref_or_const_referent.
    let target_expr = resolve_target_value(ctx, dcx);
    let target_expr = match target_expr {
        Some(expr) => expr,
        None => {
            debug!(bb_idx = dcx.bb_idx, "slice_contains: target not resolvable");
            return false;
        }
    };
    debug!(bb_idx = dcx.bb_idx, target_sort = ?target_expr.sort(), "slice_contains: resolved target");

    // Resolve the slice data array.
    // The slice is args[0] (&[T]) — a fat pointer reference. We need to find
    // the underlying array state variable and length.
    let (data_array, len) = match resolve_slice_data(ctx, dcx) {
        Some(pair) => pair,
        None => {
            debug!(bb_idx = dcx.bb_idx, "slice_contains: could not resolve slice data");
            return false;
        }
    };
    debug!(
        bb_idx = dcx.bb_idx,
        data_sort = ?data_array.sort(),
        len_sort = ?len.sort(),
        "slice_contains: resolved slice data"
    );

    // Length must be a known constant for unrolled disjunction.
    let concrete_len = match extract_const_usize(&len) {
        Some(n) if n <= MAX_UNROLL_LENGTH => n,
        Some(n) => {
            debug!(
                bb_idx = dcx.bb_idx,
                len = n,
                "slice_contains: length too large for unrolled disjunction"
            );
            return false;
        }
        None => {
            debug!(bb_idx = dcx.bb_idx, "slice_contains: length not constant");
            return false;
        }
    };

    if concrete_len == 0 {
        // Empty slice: contains always returns false.
        return emit_contains_result(ctx, dcx, target, dest_local, Expr::bool_const(false));
    }

    // Build disjunction: select(data, 0) == target || ... || select(data, len-1) == target
    let target_sort = target_expr.sort().clone();
    let index_width = data_array
        .sort()
        .array_sort()
        .map(|a| a.index_sort.bitvec_width().unwrap_or(64))
        .unwrap_or(64);

    let mut disjuncts: Vec<Expr> = Vec::with_capacity(concrete_len);
    for i in 0..concrete_len {
        let idx = Expr::bitvec_const(i as u64, index_width);
        let elem = data_array.clone().select(idx);
        // Coerce element sort to match target sort if needed.
        let eq = if elem.sort() == &target_sort {
            elem.eq(target_expr.clone())
        } else if elem.sort().is_bitvec() && target_sort.is_bitvec() {
            let ew = elem.sort().bitvec_width().unwrap_or(0);
            let tw = target_sort.bitvec_width().unwrap_or(0);
            if ew > tw {
                elem.extract((tw - 1) as u32, 0).eq(target_expr.clone())
            } else if ew < tw {
                target_expr.clone().extract(ew - 1, 0).eq(elem)
            } else {
                elem.eq(target_expr.clone())
            }
        } else {
            // Sort mismatch — can't compare.
            debug!(
                bb_idx = dcx.bb_idx,
                elem_sort = ?elem.sort(),
                target_sort = ?target_sort,
                "slice_contains: element/target sort mismatch"
            );
            return false;
        };
        disjuncts.push(eq);
    }

    let result =
        disjuncts.into_iter().reduce(|a, b| a.or(b)).unwrap_or_else(|| Expr::bool_const(false));

    debug!(
        bb_idx = dcx.bb_idx,
        concrete_len, "slice_contains: emitting {}-way disjunction", concrete_len
    );

    emit_contains_result(ctx, dcx, target, dest_local, result)
}

/// Emit the contains result constraint and transition rule.
fn emit_contains_result(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    target: BasicBlockIdx,
    dest_local: usize,
    result: Expr,
) -> bool {
    if let Some((_, dest_var)) = ctx.resolve_destination(dest_local) {
        let eq = ctx.make_coerced_eq_constraint(
            &dest_var,
            result,
            dest_var.sort(),
            dest_local,
            "slice_contains",
        );
        let extra: Vec<Expr> = eq.into_iter().collect();
        let new_output_args = ctx.build_output_args(dcx.modified_locals, &[dest_local]);
        ctx.emit_goto_rule_extra(
            dcx.from_app,
            target,
            &new_output_args,
            dcx.stmt_constraints,
            extra,
        );
        true
    } else {
        false
    }
}

/// Resolve `args[1]` (`&T`) to the underlying `T` value expression.
///
/// `contains(&self, x: &T)` takes a reference. We need the actual value for
/// element-wise comparison. Traces through `ref_targets` to find the referent
/// local and reads its state var. Falls back to `resolve_ref_or_const_referent`
/// then `translate_operand_with_modified`.
fn resolve_target_value(ctx: &mut ChcCtx<'_, '_>, dcx: &DispatchCallContext<'_>) -> Option<Expr> {
    use rustc_public::mir::Operand as MirOperand;

    let modified_locals = dcx.modified_locals;
    let arg = &dcx.args[1];

    // Step 1: Get the local for args[1].
    let ref_local = match arg {
        MirOperand::Copy(place) | MirOperand::Move(place) => {
            if place.projection.is_empty() {
                Some(place.local)
            } else {
                None
            }
        }
        MirOperand::Constant(_) => None,
    };

    // Step 2: Dereference through ref_targets to find the T value.
    if let Some(ref_local) = ref_local {
        if let Some(resolved) = resolve_via_ref_targets(ctx, ref_local, modified_locals) {
            return Some(resolved);
        }
    }

    // Step 2b: Scan MIR for the Ref assignment to the local.
    // If _13 = &_M or _13 = &_N[_day], trace to the referent.
    if let Some(ref_local) = ref_local {
        if let Some(expr) = scan_mir_for_ref_value(ctx, ref_local, modified_locals) {
            debug!(ref_local, sort = ?expr.sort(), "slice_contains: resolved via MIR ref scan");
            return Some(expr);
        }
    }

    // Step 3: Try resolve_ref_or_const_referent.
    if let Some(expr) = ctx.resolve_ref_or_const_referent(arg, modified_locals) {
        // Only use if it looks like a value (not a pointer sort).
        // Char/bool/small-int are ≤32 bits; pointers are 64 bits.
        if expr.sort().is_bool() || expr.sort().array_sort().is_some() {
            return Some(expr);
        }
        // Check if it's a small bitvec (value, not pointer).
        if let Some(w) = expr.sort().bitvec_width() {
            if w <= 32 {
                return Some(expr);
            }
        }
        debug!(sort = ?expr.sort(), "slice_contains: resolve_ref_or_const_referent skipped (likely pointer)");
    }

    // Step 4: Fallback — translate operand directly.
    if let Some(expr) = ctx.translate_operand_with_modified(arg, modified_locals) {
        return Some(expr);
    }

    None
}

/// Scan MIR for the `Ref` or `Index` assignment to `target_local` and resolve
/// to the underlying value expression.
///
/// Handles two cases:
/// 1. `_target = &_value_local` → return state var for `_value_local`
/// 2. `_target = &_array[_index]` → return `select(array_data, index_bv)`
fn scan_mir_for_ref_value(
    ctx: &ChcCtx<'_, '_>,
    target_local: usize,
    modified_locals: &std::collections::HashSet<usize>,
) -> Option<Expr> {
    use rustc_public::mir::{Rvalue, StatementKind};

    for bb_data in &ctx.body.blocks {
        for stmt in &bb_data.statements {
            let StatementKind::Assign(lhs, rhs) = &stmt.kind else { continue };
            if lhs.local != target_local || !lhs.projection.is_empty() {
                continue;
            }
            if let Rvalue::Ref(_, _, place) = rhs {
                if place.projection.is_empty() {
                    // Simple ref: _target = &_value
                    // Return the state var for _value.local.
                    let val_local = place.local;
                    if let Some(base_idx) = ctx.state_var_mgr.try_state_idx_for_local(val_local) {
                        let state_vars = &ctx.state_var_mgr.state_vars;
                        if base_idx < state_vars.len() {
                            let (name, sort) = &state_vars[base_idx];
                            let var = if modified_locals.contains(&val_local) {
                                let out = &ctx.state_var_mgr.output_state_vars[base_idx];
                                Expr::var(&*out.0, out.1.clone())
                            } else {
                                Expr::var(&**name, sort.clone())
                            };
                            return Some(var);
                        }
                    }
                } else {
                    // Handle projected refs: &base[idx] or &(*base)[idx].
                    if let Some(expr) = resolve_ref_projected_value(ctx, place, modified_locals) {
                        return Some(expr);
                    }
                }
            }
        }
    }
    None
}

/// Resolve a projected reference place to a value expression.
///
/// Handles:
/// - `[Index(idx)]`: direct array index → `select(base_data, idx_bv)`
/// - `[Deref, Index(idx)]`: deref-then-index → trace through ref_targets/
///   const_ref_values to find the underlying array, then select at idx.
fn resolve_ref_projected_value(
    ctx: &ChcCtx<'_, '_>,
    place: &rustc_public::mir::Place,
    modified_locals: &std::collections::HashSet<usize>,
) -> Option<Expr> {
    use rustc_public::mir::ProjectionElem;

    let proj = &place.projection;

    // Find the Index projection and the array-providing local.
    let (array_local, idx_local) = match proj.as_slice() {
        [ProjectionElem::Index(idx)] => {
            // [Index(idx)]: base is the array local directly.
            (place.local, *idx)
        }
        [ProjectionElem::Deref, ProjectionElem::Index(idx)] => {
            // [Deref, Index(idx)]: base is a reference to the array.
            // Deref the base local through ref_targets to find the array local.
            let deref_local = ctx
                .ref_resolution
                .ref_targets
                .get(&place.local)
                .map(|t| t.local)
                .unwrap_or(place.local);
            (deref_local, *idx)
        }
        _ => return None,
    };

    // Get the index value expression.
    let idx_expr = {
        let idx_base = ctx.state_var_mgr.try_state_idx_for_local(idx_local)?;
        let state_vars = &ctx.state_var_mgr.state_vars;
        let idx_sv = &state_vars[idx_base];
        if modified_locals.contains(&idx_local) {
            let out = &ctx.state_var_mgr.output_state_vars[idx_base];
            Expr::var(&*out.0, out.1.clone())
        } else {
            Expr::var(&*idx_sv.0, idx_sv.1.clone())
        }
    };

    // Priority 1: static_ref_to_state_idx — for `&(*_static_ptr)[idx]`.
    // When the base local is a pointer to a pub static array (DAYS_OF_WEEK),
    // the static's dedicated Array state var is at the mapped index.
    //
    // Part of #3496: Prefer the concrete initializer literal for immutable
    // statics. The static state variable may be pruned from the current block's
    // relation signature by liveness analysis (and thus not propagated by
    // constant propagation). When that happens, the variable becomes a free
    // universally-quantified term in the CHC rule, making Z3 PDR unable to
    // reliably discover the array invariant. `static mut` must keep state-var
    // semantics so prior stores remain visible.
    for local_to_try in [place.local, array_local] {
        if let Some(&static_sv_idx) = ctx.ref_resolution.static_ref_to_state_idx.get(&local_to_try)
        {
            let state_vars = &ctx.state_var_mgr.state_vars;
            if static_sv_idx < state_vars.len()
                && state_vars[static_sv_idx].1.array_sort().is_some()
            {
                // Prefer the concrete initial value only for immutable statics.
                if !ctx.ref_resolution.mutable_static_state_idxs.contains(&static_sv_idx)
                    && let Some(init_expr) =
                        ctx.ref_resolution.static_initial_values.get(&static_sv_idx)
                {
                    if init_expr.sort().array_sort().is_some() {
                        debug!(
                            local_to_try,
                            static_sv_idx,
                            "slice_contains: resolved via static initial value (concrete literal)"
                        );
                        return Some(init_expr.clone().select(idx_expr));
                    }
                }
                // Fallback: use state variable (may be free if not in live set).
                let (name, sort) = &state_vars[static_sv_idx];
                let array_var = Expr::var(&**name, sort.clone());
                debug!(
                    local_to_try,
                    static_sv_idx, "slice_contains: resolved via static_ref_to_state_idx"
                );
                return Some(array_var.select(idx_expr));
            }
        }
    }

    // Priority 2: array_local's own state var (direct Array sort).
    if let Some(base_idx) = ctx.state_var_mgr.try_state_idx_for_local(array_local) {
        let state_vars = &ctx.state_var_mgr.state_vars;
        if base_idx < state_vars.len() && state_vars[base_idx].1.array_sort().is_some() {
            let array_var = if modified_locals.contains(&array_local) {
                let out = &ctx.state_var_mgr.output_state_vars[base_idx];
                Expr::var(&*out.0, out.1.clone())
            } else {
                Expr::var(&*state_vars[base_idx].0, state_vars[base_idx].1.clone())
            };
            return Some(array_var.select(idx_expr));
        }
    }

    // Priority 3: const_ref_values for promoted const arrays.
    for local_to_try in [array_local, place.local] {
        if let Some(array_expr) = ctx.ref_resolution.const_ref_values.get(&local_to_try) {
            if array_expr.sort().array_sort().is_some() {
                return Some(array_expr.clone().select(idx_expr));
            }
        }
    }

    None
}

/// Resolve the needle value by tracing through `ref_targets`.
///
/// Handles two cases:
/// 1. Projected refs (e.g. `&(*static_ptr)[idx]`) — delegates to
///    `resolve_ref_target_with_projections` (Part of #4072).
/// 2. Simple refs to a tracked local — returns the state variable.
fn resolve_via_ref_targets(
    ctx: &ChcCtx<'_, '_>,
    ref_local: usize,
    modified_locals: &std::collections::HashSet<usize>,
) -> Option<Expr> {
    let ref_target = ctx.ref_resolution.ref_targets.get(&ref_local)?;
    let target_local = ref_target.local;
    debug!(ref_local, target_local, "slice_contains: ref_targets dereference");

    // Part of #4072: projected ref_target (e.g. [Deref, Index(idx)] on a static).
    if let Some(resolved) = resolve_ref_target_with_projections(ctx, ref_target, modified_locals) {
        return Some(resolved);
    }

    // Simple ref to a tracked local — return its state variable.
    let base_idx = ctx.state_var_mgr.try_state_idx_for_local(target_local)?;
    let state_vars = &ctx.state_var_mgr.state_vars;
    if base_idx < state_vars.len() {
        let (name, sort) = &state_vars[base_idx];
        let var = if modified_locals.contains(&target_local) {
            let out = &ctx.state_var_mgr.output_state_vars[base_idx];
            Expr::var(&*out.0, out.1.clone())
        } else {
            Expr::var(&**name, sort.clone())
        };
        return Some(var);
    }
    None
}

/// Resolve a `RefTarget` with projections to a value expression.
///
/// Part of #4072: When `ref_targets` maps a local to `RefTarget { local: N,
/// projections: [Deref, Index(idx)] }` and `N` is a static pointer, the raw
/// state var for `N` is a BV64 address — not the array element value. This
/// function resolves through the static's concrete array data to produce
/// `select(STATIC_ARRAY, idx)`.
fn resolve_ref_target_with_projections(
    ctx: &ChcCtx<'_, '_>,
    ref_target: &super::super::codegen_ctx::types::RefTarget,
    modified_locals: &std::collections::HashSet<usize>,
) -> Option<Expr> {
    use crate::codegen_ay::types::{POINTER_WIDTH, SignExtension, coerce_bitvec_width_safe};
    use rustc_public::mir::ProjectionElem;

    let projs = &ref_target.projections;

    // Match [Deref, Index(idx)] — the common pattern for &(*static_ref)[day].
    let idx_local = match projs.as_slice() {
        [ProjectionElem::Deref, ProjectionElem::Index(idx)] => *idx,
        _ => return None,
    };

    let target_local = ref_target.local;

    // Resolve the index expression.
    let idx_base = ctx.state_var_mgr.try_state_idx_for_local(idx_local)?;
    let state_vars = &ctx.state_var_mgr.state_vars;
    let idx_expr = if modified_locals.contains(&idx_local) {
        let out = &ctx.state_var_mgr.output_state_vars[idx_base];
        Expr::var(&*out.0, out.1.clone())
    } else {
        let sv = &state_vars[idx_base];
        Expr::var(&*sv.0, sv.1.clone())
    };
    let idx_expr = coerce_bitvec_width_safe(idx_expr, POINTER_WIDTH, SignExtension::ZeroExtend);

    // Check if target_local is a static pointer.
    if let Some(&static_sv_idx) = ctx.ref_resolution.static_ref_to_state_idx.get(&target_local) {
        if static_sv_idx < state_vars.len() && state_vars[static_sv_idx].1.array_sort().is_some() {
            // Prefer concrete initial value for immutable statics (#4072).
            if !ctx.ref_resolution.mutable_static_state_idxs.contains(&static_sv_idx) {
                if let Some(init_expr) =
                    ctx.ref_resolution.static_initial_values.get(&static_sv_idx)
                {
                    if init_expr.sort().array_sort().is_some() {
                        debug!(
                            target_local,
                            static_sv_idx,
                            "slice_contains: resolve_ref_target via concrete static initial value (#4072)"
                        );
                        return Some(init_expr.clone().select(idx_expr));
                    }
                }
            }
            // Fallback: use state variable.
            let (name, sort) = &state_vars[static_sv_idx];
            let array_var = Expr::var(&**name, sort.clone());
            debug!(
                target_local,
                static_sv_idx, "slice_contains: resolve_ref_target via static state var (#4072)"
            );
            return Some(array_var.select(idx_expr));
        }
    }

    None
}
