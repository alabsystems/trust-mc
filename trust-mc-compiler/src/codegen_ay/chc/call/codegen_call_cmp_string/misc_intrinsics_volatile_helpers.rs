// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Helper functions for volatile_load CHC codegen.
//!
//! Extracted from `misc_intrinsics_volatile.rs` per file size limit (#3348).
//! Contains Vec element extraction and ptr.add resolution for volatile_load.
//!
//! Part of #3485: volatile_load Vec pointer element extraction.

use ay_bindings::{Expr, SortInner};
use rustc_public::CrateDef;
use rustc_public::mir::{BinOp, Operand, Place, Rvalue, StatementKind, TerminatorKind};
use rustc_public::ty::{RigidTy, TyKind};
use tracing::debug;

use super::super::ChcCtx;
use super::super::codegen_call_misc::CallMisc;

/// Maximum depth for backward Copy/Move chain tracing.
const MAX_TRACE_DEPTH: usize = 16;

/// Walk backward through Copy/Move assignment chains to find a Vec-typed source local.
///
/// After Kani's InlinePass inlines `Vec::as_ptr()`, the Call terminator is gone and
/// `PointerMaterialization` never creates a `ref_target` for the pointer result.
/// Instead, the MIR contains a chain of field projections and Copy/Move assignments
/// from the Vec local down to a raw pointer. This function traces that chain backward
/// from the pointer local to find the Vec source.
///
/// Part of #4074: post-inline volatile_load Vec resolution.
fn trace_to_vec_local(body: &rustc_public::mir::Body, start_local: usize) -> Option<usize> {
    let mut current = start_local;
    for _ in 0..MAX_TRACE_DEPTH {
        let mut found_source = None;
        for bb_data in &body.blocks {
            for stmt in &bb_data.statements {
                let StatementKind::Assign(dest, rhs) = &stmt.kind else {
                    continue;
                };
                if dest.local != current || !dest.projection.is_empty() {
                    continue;
                }
                if let Rvalue::Use(Operand::Copy(place) | Operand::Move(place))
                | Rvalue::CopyForDeref(place) = rhs
                {
                    let src_local = place.local;
                    if let Some(decl) = body.locals().get(src_local) {
                        if is_vec_ty(decl.ty) {
                            return Some(src_local);
                        }
                    }
                    found_source = Some(src_local);
                }
            }
        }
        current = found_source?;
    }
    None
}

fn is_vec_ty(ty: rustc_public::ty::Ty) -> bool {
    matches!(ty.kind(), TyKind::RigidTy(RigidTy::Adt(def, _)) if def.trimmed_name() == "Vec")
}

/// P4-3: a resolved projected-Vec data array — the state-var slot index (for
/// output-var write-through) plus the current data Array expression.
pub(in crate::codegen_ay::chc) struct ProjectedVecDataSlot {
    pub(in crate::codegen_ay::chc) data_idx: usize,
    pub(in crate::codegen_ay::chc) data_expr: Expr,
    /// The projected Vec local backing this slot (write-through paths must
    /// refuse a `data_out = store(data_out, ...)` circularity when the local
    /// is already in `modified_locals`).
    pub(in crate::codegen_ay::chc) coll_local: usize,
}

/// P4-3: resolve a projected Vec local to its data-array slot + expression.
fn projected_vec_data_slot_for_vec_local(
    ctx: &ChcCtx<'_, '_>,
    coll_local: usize,
    modified_locals: &std::collections::HashSet<usize>,
) -> Option<ProjectedVecDataSlot> {
    use crate::codegen_ay::chc::codegen_ctx::types::CollectionProjectionKind;

    if ctx.collections.projection_locals.get(&coll_local).copied()
        != Some(CollectionProjectionKind::Vec)
    {
        return None;
    }
    let base_idx = ctx.try_state_idx_for_local(coll_local)?;
    let data_idx = base_idx + 3;
    let vars = if modified_locals.contains(&coll_local) {
        &ctx.state_var_mgr.output_state_vars
    } else {
        &ctx.state_var_mgr.state_vars
    };
    let (name, sort) = vars.get(data_idx)?;
    sort.array_sort()?;
    Some(ProjectedVecDataSlot { data_idx, data_expr: Expr::var(&**name, sort.clone()), coll_local })
}

/// P4-3: resolve a POINTER local to a projected Vec's data-array slot.
///
/// Two lanes:
/// 1. `ref_targets[ptr_local]` → Vec local (pre-inline `as_ptr`/`as_mut_ptr`,
///    materialized by PointerMaterialization);
/// 2. post-inline backward MIR trace (`trace_to_vec_local`) when the
///    InlinePass flattened `as_ptr` and no ref_target exists — the base
///    then carries the projected-Vec state through Copy/field chains.
pub(in crate::codegen_ay::chc) fn projected_vec_data_slot_for_ptr(
    ctx: &ChcCtx<'_, '_>,
    ptr_local: usize,
    modified_locals: &std::collections::HashSet<usize>,
) -> Option<ProjectedVecDataSlot> {
    if let Some(ref_target) = ctx.ref_resolution.ref_targets.get(&ptr_local) {
        if !ref_target.projections.is_empty() {
            return None;
        }
        return projected_vec_data_slot_for_vec_local(ctx, ref_target.local, modified_locals);
    }
    // Post-inline: no ref_target — trace Copy/field chains back to the Vec.
    let vec_local = trace_to_vec_local(&ctx.body, ptr_local)?;
    projected_vec_data_slot_for_vec_local(ctx, vec_local, modified_locals)
}

/// Resolve a pointer local's ref_target to a projected Vec data Array state variable.
///
/// Follows `ref_targets[ptr_local]` → Vec local, then reads the data field
/// (offset +3) from the projected state variables. Returns the Array expression
/// directly, NOT wrapped in a Datatype — this matches the path used by
/// `codegen_call_slice_index::try_resolve_projected_vec_data_array`.
///
/// Part of #4074: projected Vec data array for volatile_load ptr.add.
/// P4-3: extended with the post-inline backward-trace lane via
/// `projected_vec_data_slot_for_ptr`.
fn resolve_projected_vec_data_for_ptr(
    ctx: &ChcCtx<'_, '_>,
    ptr_local: usize,
    modified_locals: &std::collections::HashSet<usize>,
) -> Option<Expr> {
    projected_vec_data_slot_for_ptr(ctx, ptr_local, modified_locals).map(|slot| slot.data_expr)
}

/// Resolve a Vec local into its Datatype expression via `translate_place_with_modified`.
fn resolve_vec_datatype(
    ctx: &ChcCtx<'_, '_>,
    vec_local: usize,
    modified_locals: &std::collections::HashSet<usize>,
) -> Option<Expr> {
    let place = Place { local: vec_local, projection: vec![] };
    let expr = ctx.translate_place_with_modified(&place, modified_locals)?;
    if expr.sort().is_datatype() { Some(expr) } else { None }
}

/// Resolve volatile_load pointer to Vec Datatype via backward MIR tracing.
///
/// When Kani's InlinePass inlines `Vec::as_ptr()`, the Call terminator disappears
/// and `PointerMaterialization` never fires — no `ref_target` exists for the pointer.
/// This function traces backward through Copy/Move chains in the MIR to find the
/// Vec source local, then reconstructs its Datatype expression.
///
/// Only used as a fallback when both `resolve_ref_or_const_referent` and
/// `try_volatile_load_via_ptr_add` fail to resolve the pointer.
///
/// Part of #4074: post-inline volatile_load Vec resolution.
pub(in crate::codegen_ay::chc) fn try_volatile_load_via_vec_trace(
    ctx: &ChcCtx<'_, '_>,
    arg: &Operand,
    modified_locals: &std::collections::HashSet<usize>,
) -> Option<Expr> {
    let arg_local = match arg {
        Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => p.local,
        _ => return None,
    };
    if ctx.ref_resolution.ref_targets.contains_key(&arg_local) {
        return None;
    }
    let vec_local = trace_to_vec_local(&ctx.body, arg_local)?;
    let vec_expr = resolve_vec_datatype(ctx, vec_local, modified_locals)?;
    debug!(arg_local, vec_local, "volatile_load: traced pointer to Vec local (Part of #4074)");
    Some(vec_expr)
}

/// Resolve volatile_load pointer to a projected Vec data array element.
///
/// Uses the same projected-Vec resolution path as `codegen_call_slice_index`
/// (`try_resolve_projected_vec_data_array`), which reads the data Array state
/// variable directly. This ensures the data array reflects push/store updates,
/// matching the `vec[idx]` path that reaches PROOF.
///
/// For `volatile_load(vec.as_ptr())`, returns `data_var.select(0)`.
/// For `volatile_load(vec.as_ptr().add(n))`, the caller should use
/// `try_volatile_load_via_ptr_add` instead (handles offset).
///
/// Part of #4074: volatile_load via projected Vec data array.
pub(in crate::codegen_ay::chc) fn try_volatile_load_via_projected_vec(
    ctx: &ChcCtx<'_, '_>,
    arg: &Operand,
    modified_locals: &std::collections::HashSet<usize>,
) -> Option<Expr> {
    let arg_local = match arg {
        Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => p.local,
        _ => return None,
    };
    // Follow ref_target to the Vec local.
    let ref_target = ctx.ref_resolution.ref_targets.get(&arg_local)?;
    if !ref_target.projections.is_empty() {
        return None; // Has projections — not a bare Vec reference.
    }
    let coll_local = ref_target.local;
    // Check if this is a projected Vec.
    use crate::codegen_ay::chc::codegen_ctx::types::CollectionProjectionKind;
    if ctx.collections.projection_locals.get(&coll_local).copied()
        != Some(CollectionProjectionKind::Vec)
    {
        return None;
    }
    // Projected Vec: base_state_idx + 3 = data field (Array<BV64, elem_sort>)
    let base_idx = ctx.try_state_idx_for_local(coll_local)?;
    let data_idx = base_idx + 3;
    let vars = if modified_locals.contains(&coll_local) {
        &ctx.state_var_mgr.output_state_vars
    } else {
        &ctx.state_var_mgr.state_vars
    };
    let (name, sort) = vars.get(data_idx)?;
    sort.array_sort()?;
    let data_var = Expr::var(&**name, sort.clone());
    // volatile_load(vec.as_ptr()) reads element 0.
    let zero = Expr::bitvec_const(0u64, crate::codegen_ay::types::POINTER_WIDTH);
    debug!(
        coll_local,
        data_idx, "volatile_load: resolved via projected Vec data array[0] (Part of #4074)"
    );
    Some(data_var.select(zero))
}

/// Extract a Vec element from a Datatype when volatile_load resolves to a whole Vec.
///
/// When `volatile_load(vec.as_ptr())` is called, `resolve_ref_or_const_referent`
/// follows `ref_targets` from the pointer to the Vec local (due to
/// `PointerMaterialization`), returning the entire Vec Datatype expression.
/// Since `make_coerced_eq_constraint` cannot coerce `Datatype(Vec_T)` to `T`,
/// the destination would be left unconstrained.
///
/// This function detects the mismatch and extracts `fld_data[0]` — the first
/// element (logical index 0) — giving PDR a concrete constraint.
///
/// Returns the original value unchanged if not a Vec-like Datatype or if the
/// destination sort already matches.
///
/// Part of #3485: volatile_load Vec pointer element extraction.
pub(in crate::codegen_ay::chc) fn try_extract_vec_element_for_load(
    val: Expr,
    dest_sort: &ay_bindings::Sort,
) -> Expr {
    // Only extract when value is a Datatype but dest expects something else.
    if !val.sort().is_datatype() || dest_sort.is_datatype() {
        return val;
    }
    let sort_ref = val.sort().clone();
    let SortInner::Datatype(dt) = sort_ref.inner() else {
        return val;
    };
    let Some(ctor) = dt.constructors.first() else {
        return val;
    };
    let data_field = ctor.fields.iter().find(|f| f.name == "fld_data");
    let has_ptr = ctor.fields.iter().any(|f| f.name == "fld_ptr");
    let Some(data_field) = data_field else {
        return val;
    };
    if !has_ptr {
        return val;
    }
    // Verify fld_data is an Array sort (backing data store).
    if !data_field.sort.is_array() {
        return val;
    }
    let dt_name = &dt.name;
    let data = val.field_select(dt_name, "fld_data", data_field.sort.clone());
    // Part of #3485: fld_data uses LOGICAL indices (0, 1, 2, ...) from
    // build_into_vec_data_array, NOT heap addresses. volatile_load(vec.as_ptr())
    // reads element 0, so index with constant 0.
    let zero = Expr::bitvec_const(0u64, crate::codegen_ay::types::POINTER_WIDTH);
    debug!(%dt_name, "volatile_load: extracted Vec element fld_data[0] (Part of #3485)");
    data.select(zero)
}

/// Resolve volatile_load through a ptr.add chain to extract Vec element (Case B).
///
/// When `volatile_load(ptr.add(count))` is called, the ptr.add result has no
/// `ref_targets` entry, so `resolve_ref_or_const_referent` returns a raw BV64
/// pointer (not a Datatype). This function scans the MIR to find the ptr.add
/// call, traces the base pointer through `ref_targets` to the Vec local, and
/// extracts `fld_data[count]` from the Vec Datatype state variable (logical index).
///
/// MIR pattern:
/// ```text
///   _ptr = Vec::as_ptr(_vec)     // PointerMaterialization: ref_targets[_ptr] -> Vec
///   _offset = ptr.add(_ptr, _N)  // No ref_target for _offset
///   _result = volatile_load(_offset)
/// ```
///
/// Returns an element expression `fld_data[count]` if the pattern matches,
/// None otherwise. Count is the logical element offset from ptr.add.
///
/// Part of #3485 Case B: volatile_load through ptr.add offsets.
pub(in crate::codegen_ay::chc) fn try_volatile_load_via_ptr_add(
    ctx: &mut ChcCtx<'_, '_>,
    arg: &rustc_public::mir::Operand,
    modified_locals: &std::collections::HashSet<usize>,
) -> Option<Expr> {
    use rustc_public::mir::Operand;

    // Get argument local.
    let arg_local = match arg {
        Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => p.local,
        _ => return None,
    };

    let (base_ptr_local, count_operand) = find_ptr_add_base_and_count(ctx, arg_local)?;

    // Phase 2: Resolve the Vec data array through the base pointer.
    // Prefer the projected Vec data array state variable (same path as slice_index)
    // to ensure the data array reflects push/store updates. Fall back to Datatype
    // extraction only if the projected path is unavailable.
    // Part of #4074. P4-3: the projected lane also covers the post-inline
    // `vec.as_ptr().add(k)` shape (backward trace, no ref_target).
    let fld_data = resolve_projected_vec_data_for_ptr(ctx, base_ptr_local, modified_locals)
        .or_else(|| {
            // Fallback: Datatype extraction (for non-projected Vecs).
            let base_ptr_place =
                rustc_public::mir::Place { local: base_ptr_local, projection: vec![] };
            let base_ptr_op = Operand::Copy(base_ptr_place);
            let vec_expr = ctx
                .resolve_ref_or_const_referent(&base_ptr_op, modified_locals)
                .filter(|e| e.sort().is_datatype())
                .or_else(|| {
                    let vec_local = trace_to_vec_local(&ctx.body, base_ptr_local)?;
                    resolve_vec_datatype(ctx, vec_local, modified_locals)
                })?;
            let sort_ref = vec_expr.sort().clone();
            let SortInner::Datatype(dt) = sort_ref.inner() else {
                return None;
            };
            let ctor = dt.constructors.first()?;
            let data_field = ctor.fields.iter().find(|f| f.name == "fld_data")?;
            if !data_field.sort.is_array() {
                return None;
            }
            Some(vec_expr.field_select(&dt.name, "fld_data", data_field.sort.clone()))
        })?;

    // Translate count operand using the standard operand translator.
    // This handles Copy/Move (state variable lookup) and Constant (literal
    // evaluation) uniformly.
    let count_expr = ctx.translate_operand_with_modified(&count_operand, modified_locals)?;
    let count_expr = ctx.coerce_to_pointer_width(count_expr)?;

    // Part of #3485: fld_data uses LOGICAL indices (0, 1, 2, ...) from
    // build_into_vec_data_array. ptr.add(count) adds `count` elements, so
    // the logical index IS the count directly — no fld_ptr addition needed.
    debug!(
        arg_local,
        base_ptr_local,
        "volatile_load: resolved ptr.add -> fld_data[count] (Part of #3485, #4074 Case B)"
    );
    Some(fld_data.select(count_expr))
}

/// P4-3: scan MIR for the ptr.add / `BinOp::Offset` that produced `arg_local`,
/// returning the base pointer local and the (cloned) count operand.
///
/// Two patterns are checked:
///   (a) Pre-inline: a Call terminator to ptr.add/offset/wrapping_add/wrapping_offset
///   (b) Post-inline: a BinOp::Offset Assign statement (the InlinePass flattens
///       ptr.add into `_dest = Offset(_base, _count)`)
/// Part of #4074: post-inline volatile_load resolution. Extracted from
/// `try_volatile_load_via_ptr_add` so the volatile_store write-through can
/// reuse the same scan.
pub(in crate::codegen_ay::chc) fn find_ptr_add_base_and_count(
    ctx: &ChcCtx<'_, '_>,
    arg_local: usize,
) -> Option<(usize, rustc_public::mir::Operand)> {
    use rustc_public::mir::Operand;

    let mut base_ptr_local: Option<usize> = None;
    let mut count_operand: Option<Operand> = None;

    'scan: for bb_data in &ctx.body.blocks {
        // (a) Pre-inline: ptr.add Call terminator.
        if let TerminatorKind::Call { func, args, destination, .. } = &bb_data.terminator.kind {
            if destination.local == arg_local && args.len() >= 2 {
                if let Some(callee_path) = ctx.resolve_callee_path(func) {
                    let last_seg = callee_path.rsplit("::").next().unwrap_or("");
                    let is_ptr_method = callee_path.contains("const_ptr")
                        || callee_path.contains("mut_ptr")
                        || callee_path.contains("NonNull")
                        || callee_path.contains("rustc_intrinsics");
                    if is_ptr_method
                        && matches!(last_seg, "add" | "offset" | "wrapping_add" | "wrapping_offset")
                    {
                        if let Operand::Copy(p) | Operand::Move(p) = &args[0] {
                            if p.projection.is_empty() {
                                base_ptr_local = Some(p.local);
                            }
                        }
                        count_operand = Some(args[1].clone());
                        break 'scan;
                    }
                }
            }
        }

        // (b) Post-inline: BinOp::Offset in Assign statement.
        // After the InlinePass flattens ptr.add, the offset is a direct
        // `_dest = BinaryOp(Offset, base_ptr, count)` statement.
        // Part of #4074.
        for stmt in &bb_data.statements {
            let StatementKind::Assign(dest, rhs) = &stmt.kind else {
                continue;
            };
            if dest.local != arg_local || !dest.projection.is_empty() {
                continue;
            }
            if let Rvalue::BinaryOp(BinOp::Offset, base_op, count_op)
            | Rvalue::CheckedBinaryOp(BinOp::Offset, base_op, count_op) = rhs
            {
                if let Operand::Copy(p) | Operand::Move(p) = base_op {
                    if p.projection.is_empty() {
                        base_ptr_local = Some(p.local);
                    }
                }
                count_operand = Some(count_op.clone());
                break 'scan;
            }
        }
    }

    Some((base_ptr_local?, count_operand?))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::codegen_ay::test_fixtures::{vec_expr, vec_sort};
    use crate::codegen_ay::types::ptr_sort;
    use ay_bindings::Sort;

    #[test]
    fn test_extract_vec_element_returns_select_for_vec_datatype() {
        let elem_sort = Sort::bitvec(32);
        let vs = vec_sort(elem_sort.clone());
        let data = Expr::const_array(ptr_sort(), Expr::bitvec_const(0u64, 32));
        let vec_val = vec_expr(
            Expr::bitvec_const(0x1000u64, 64),
            Expr::bitvec_const(2u64, 64),
            Expr::bitvec_const(4u64, 64),
            data,
            vs,
        );
        let result = try_extract_vec_element_for_load(vec_val, &elem_sort);
        // Result should be a Select expression (fld_data[0]), not a Datatype.
        assert!(!result.sort().is_datatype(), "should extract element, not return Vec");
        assert_eq!(result.sort().bitvec_width(), Some(32), "element should be BV32");
    }

    #[test]
    fn test_extract_vec_element_passthrough_non_datatype() {
        let bv = Expr::bitvec_const(42u64, 32);
        let dest_sort = Sort::bitvec(32);
        let result = try_extract_vec_element_for_load(bv, &dest_sort);
        // Non-Datatype value should pass through unchanged.
        assert_eq!(result.sort().bitvec_width(), Some(32));
    }

    #[test]
    fn test_extract_vec_element_passthrough_when_dest_is_datatype() {
        let elem_sort = Sort::bitvec(32);
        let vs = vec_sort(elem_sort);
        let data = Expr::const_array(ptr_sort(), Expr::bitvec_const(0u64, 32));
        let vec_val = vec_expr(
            Expr::bitvec_const(0x1000u64, 64),
            Expr::bitvec_const(2u64, 64),
            Expr::bitvec_const(4u64, 64),
            data,
            vs.clone(),
        );
        // When dest also expects a Datatype, no extraction should occur.
        let result = try_extract_vec_element_for_load(vec_val, &vs);
        assert!(result.sort().is_datatype(), "should not extract when dest is Datatype");
    }

    #[test]
    fn test_extract_vec_element_passthrough_non_vec_datatype() {
        // A struct with no fld_data/fld_ptr should pass through.
        let point_sort = crate::codegen_ay::test_fixtures::point_sort();
        let point = Expr::datatype_constructor(
            "Point",
            "Point_mk",
            vec![Expr::bitvec_const(1u64, 32), Expr::bitvec_const(2u64, 32)],
            point_sort,
        );
        let dest = Sort::bitvec(32);
        let result = try_extract_vec_element_for_load(point, &dest);
        // Point has no fld_data/fld_ptr, should pass through as Datatype.
        assert!(result.sort().is_datatype(), "non-Vec Datatype should pass through");
    }
}
