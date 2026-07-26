// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Shared field-map helpers for inline body translation.
//!
//! Provides memory-backed self-field resolution and scalar type-key lookup
//! used by virtual, closure, fn-inline, and fn-ptr inline translators.
//!
//! Part of #3241: neutral home for generic inline infrastructure extracted
//! from `codegen_call_virtual_inline`.

use ay_bindings::{Expr, Sort};
use rustc_public::mir::{Operand, ProjectionElem};
use rustc_public::ty::{RigidTy, TyKind};
use std::collections::{HashMap, HashSet};
use tracing::debug;

use super::ChcCtx;
use super::chc_call_context::DispatchCallContext;
use super::codegen_call_ptr_identity::trace_pointer_identity_ref_target;
use super::codegen_decl_flatten::collect_leaf_sorts;
use super::codegen_types::CodegenTypes;
use super::inline_field_map_reconstruct::try_reconstruct_adt_from_scalar_loads;
use crate::codegen_ay::chc::{UNDEF_COUNTER, declare_pending_var};
use crate::codegen_ay::types::POINTER_WIDTH;

// Re-export for external consumers.
pub(in crate::codegen_ay::chc) use super::inline_field_map_reconstruct::scalar_type_key;

fn cast_source_local(body: &rustc_public::mir::Body, dest_local: usize) -> Option<usize> {
    body.blocks.iter().find_map(|block| {
        block.statements.iter().find_map(|stmt| {
            let rustc_public::mir::StatementKind::Assign(
                lhs,
                rustc_public::mir::Rvalue::Cast(_, Operand::Copy(place) | Operand::Move(place), _),
            ) = &stmt.kind
            else {
                return None;
            };
            (lhs.local == dest_local && place.projection.is_empty()).then_some(place.local)
        })
    })
}

fn resolve_flattened_self_source_local<'tcx, 'body>(
    ctx: &ChcCtx<'tcx, 'body>,
    arg_local: usize,
) -> Option<usize> {
    let field_sources = ctx.collect_aggregate_field_sources();
    let mut current_local = arg_local;

    for _ in 0..6 {
        let resolved_local =
            ctx.ref_resolution.ref_targets.get(&current_local).map_or(current_local, |rt| rt.local);
        if ctx.flatten.flattened_tuple_locals.contains(&resolved_local) {
            return Some(resolved_local);
        }

        if let Some(ref_target) = trace_pointer_identity_ref_target(ctx, current_local)
            && ref_target.projections.is_empty()
            && ctx.flatten.flattened_tuple_locals.contains(&ref_target.local)
        {
            debug!(
                arg_local,
                current_local,
                target_local = ref_target.local,
                "inline self field hints: resolved traced pointer identity target"
            );
            return Some(ref_target.local);
        }

        let next_local = field_sources
            .get(&(resolved_local, 0))
            .copied()
            .or_else(|| cast_source_local(ctx.body, resolved_local))?;
        if next_local == current_local {
            return None;
        }
        current_local = next_local;
    }

    None
}

/// Sentinel field index for direct scalar deref via self_field_map.
///
/// Used when the pointee type is a primitive scalar (u8, i32, etc.),
/// not a struct/tuple with named fields. A bare `[Deref]` projection
/// on a scalar-typed pointer loads the value from memory rather than
/// treating the pointer as the value.
///
/// Part of #3159: Fixes Box<dyn Trait> dispatch for primitive implementors.
pub(in crate::codegen_ay::chc) const DIRECT_DEREF_FIELD: usize = usize::MAX;

/// Build a map of (self_local, field_idx) → Expr for memory-backed field access.
///
/// When the self parameter (local 1) is BV64 (a pointer), the method body
/// accesses fields via `(*_1).field_idx`. This function pre-computes those
/// field values by building `select(mem_array, self_ptr + field_offset)`
/// expressions using the heap's type-indexed memory arrays.
///
/// Part of #3159: Enables virtual dispatch inlining for methods that access
/// struct fields through pointer dereferences.
pub(in crate::codegen_ay::chc) fn build_self_field_map<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    body: &rustc_public::mir::Body,
    params: &[Expr],
) -> HashMap<(usize, usize), Expr> {
    let mut map = ctx.inline_self_field_hints.take().unwrap_or_default();
    if !map.is_empty() {
        debug!(
            field_count = map.len(),
            "build_self_field_map: using pre-populated flattened hints (#3830)"
        );
    }

    // Part of #4132: Only build memory-backed field map for param[0] (self/receiver).
    // The all-params generalization from #3994 causes AsyncAwait/coroutine regressions
    // because multi-param field entries interfere with Downcast projections in
    // field_map_projection.rs. Enum PartialEq (the motivation for #3994) works
    // through virtual dispatch where self is the only param needing field resolution.
    if let Some(self_expr) = params.first() {
        let local_idx = 1;
        if !map.keys().any(|(mapped_local, _)| *mapped_local == local_idx) {
            extend_field_map_for_param(ctx, body, local_idx, self_expr, &mut map);
        }
    }

    if !map.is_empty() {
        debug!(
            field_count = map.len(),
            "virtual inline: built memory-backed field map for inline params"
        );
    }

    debug!(entries = map.len(), "build_self_field_map: complete");

    map
}

fn extend_field_map_for_param<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    body: &rustc_public::mir::Body,
    local_idx: usize,
    param_expr: &Expr,
    map: &mut HashMap<(usize, usize), Expr>,
) {
    let pointer_expr = match pointer_storage_expr(ctx, param_expr) {
        Some(expr) => expr,
        None => return,
    };

    let locals = body.locals();
    let local_ty = match locals.get(local_idx) {
        Some(local_decl) => ctx.resolve_body_ty(local_decl.ty),
        None => return,
    };
    let pointee_ty = match local_ty.kind() {
        TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => ctx.resolve_body_ty(inner),
        TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => ctx.resolve_body_ty(inner),
        _ => return,
    };

    // Fix A (UnsizedCoercion basic_inner): only reuse a flattened local's whole
    // layout when its type actually matches the callee's `self` pointee type.
    // For a re-rooted receiver like `&outer.inner`, the displaced pointer still
    // resolves (via try_extract_obj_id) to the base flattened local `outer`
    // (type `Outer`), but the callee's `self` is `&Inner`. Mapping `Inner`'s
    // fields against `Outer`'s flattened slots drops the `.inner` offset and
    // reads `Outer.field0` (= outer_id). The sort-equality gate blocks that and
    // lets the per-field scalar loads below compute the correct sub-field value.
    let self_pointee_sort = ChcCtx::translate_ty(pointee_ty);
    // Residual Fix B (UnsizedCoercion same-sort re-root): the flattened fast
    // path below reuses `target_local`'s WHOLE layout, which is sound ONLY when
    // the receiver points at that local's base (byte offset 0). A re-rooted
    // receiver (`&outer.inner`) carries a NONZERO sub-field byte offset in its
    // split-pointer address (`(obj_id, offset)`); `try_extract_obj_id` drops the
    // offset, resolving back to the base `outer`, and mapping `Inner`'s fields
    // against `outer`'s flattened slots reads the wrong scalar. Fix A blocked
    // this on a *type* mismatch, but that misses a SAME-SORT re-root — a
    // sub-field whose Rust type differs from the base yet translates to the same
    // SMT sort (`translate_ty` names sorts nominally + by generic args, so
    // distinct types CAN collide). The precise, type-independent discriminator
    // is the offset itself: only fast-path a receiver that points at the base
    // (offset == 0); for any offset != 0 fall through to the per-field
    // memory-load path, which recomputes `pointer_expr + field_offset` exactly.
    if !map.keys().any(|(mapped_local, _)| *mapped_local == local_idx)
        && let Some((obj_id, offset)) = ChcCtx::try_extract_constant_addr(&pointer_expr)
        && offset == 0
        && let Some(target_local) = ctx.heap_state.local_idx_for_obj_id(obj_id)
        && flattened_target_matches_pointee(ctx, target_local, self_pointee_sort.as_ref())
        && let Some(hints) = flattened_self_field_hints_for_target(ctx, target_local, local_idx)
    {
        let field_count = hints.len();
        map.extend(hints);
        debug!(
            local_idx,
            target_local,
            field_count,
            "build_self_field_map: resolved stack pointer to flattened local"
        );
        return;
    }

    if !matches!(
        pointee_ty.kind(),
        TyKind::RigidTy(RigidTy::Adt(..)) | TyKind::RigidTy(RigidTy::Tuple(..))
    ) {
        let type_key = ctx.type_key_for_body_ty(pointee_ty).into_owned();
        // Part of #4075 D2: spawn-stubbed types should return fresh symbolics
        // instead of creating/reading type arrays. Without this check, the
        // field map builder bypasses load_from_memory's stub gate and marks
        // arrays as read, preventing the pruner from eliminating them.
        if ctx.should_stub_spawn_type_array(&type_key) {
            let elem_sort = ctx.elem_sort_for_memory_array(pointee_ty);
            let sym = declare_pending_var(
                format!(
                    "__spawn_stub_field_{}",
                    UNDEF_COUNTER.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
                ),
                elem_sort,
            );
            map.insert((local_idx, DIRECT_DEREF_FIELD), sym);
            return;
        }
        let elem_sort = ctx.elem_sort_for_memory_array(pointee_ty);
        let (arr_name, arr_out_name, declared_elem_sort, is_new) =
            ctx.heap_state.get_or_create_type_array(&type_key, elem_sort, &ctx.fn_name);
        if is_new {
            let arr_sort = Sort::array(Sort::bitvec(POINTER_WIDTH), declared_elem_sort.clone());
            ctx.push_late_state_var_pair(std::sync::Arc::clone(&arr_name), &arr_out_name, arr_sort);
        }
        ctx.heap_state.mark_type_array_read(&arr_name, ctx.current_encode_bb);
        let arr_sort = Sort::array(Sort::bitvec(POINTER_WIDTH), declared_elem_sort);
        let arr_expr = if let Some(chain_expr) = ctx.heap_state.get_store_chain(&type_key) {
            chain_expr.clone()
        } else {
            Expr::var(&*arr_name, arr_sort)
        };
        map.insert((local_idx, DIRECT_DEREF_FIELD), arr_expr.select(pointer_expr));
        return;
    }

    let field_types = match pointee_ty.kind() {
        TyKind::RigidTy(RigidTy::Adt(def, args)) => {
            let variants = def.variants();
            if variants.is_empty() {
                return;
            }
            // Part of #4132: Do NOT add DIRECT_DEREF_FIELD for ADTs via
            // load_from_memory. The loaded value may contain ITE branches
            // that cause datatype_field_select to fail for some branches,
            // producing unconstrained field_select free variables. The
            // per-field loads below are sufficient and more precise.
            // The old code (pre-9ef17cceb1) did not have this insertion.
            variants[0]
                .fields()
                .iter()
                .map(|field| ctx.resolve_body_ty(field.ty_with_args(&args)))
                .collect::<Vec<_>>()
        }
        TyKind::RigidTy(RigidTy::Tuple(elems)) => {
            // Part of #4132: Do NOT add DIRECT_DEREF_FIELD for Tuples via
            // load_from_memory, same rationale as ADTs above. Per-field loads
            // below are sufficient and more precise. The old code (pre-9ef17cceb1)
            // did not have this insertion.
            elems.iter().map(|ty| ctx.resolve_body_ty(*ty)).collect::<Vec<_>>()
        }
        _ => return,
    };

    // For DSTs like `Wrapper<dyn DummyTrait>`, layout() fails because the
    // unsized tail has no compile-time size. Normalize the dyn tail to its
    // unique concrete implementation (e.g., `Wrapper<DummyImpl>`) which has a
    // known layout. The field offsets of the sized prefix are identical in
    // both the DST and its concrete surrogate. Without this fallback, the
    // field map is empty and the inline walker can't resolve field accesses
    // inside custom Drop impls for Rc/Arc-wrapped DST structs.
    // Part of #4207.
    let offsets = if let Ok(layout) = pointee_ty.layout() {
        if let rustc_public::abi::FieldsShape::Arbitrary { offsets } = layout.shape().fields {
            offsets
        } else {
            return;
        }
    } else {
        // Only attempt normalization for types that actually contain a dyn
        // tail. Without this guard, sized types whose layout() fails for
        // other reasons (e.g., recursive types) would needlessly enter the
        // normalization path and may cause cascading inline walk failures.
        let concrete_ty = ctx.normalize_unique_dyn_tail_ty(pointee_ty);
        if concrete_ty == pointee_ty {
            return;
        }
        let Ok(concrete_layout) = concrete_ty.layout() else {
            return;
        };
        if let rustc_public::abi::FieldsShape::Arbitrary { offsets } =
            concrete_layout.shape().fields
        {
            offsets
        } else {
            return;
        }
    };

    for (field_idx, field_ty) in field_types.iter().enumerate() {
        let Some(byte_offset) = offsets.get(field_idx).map(|offset| offset.bytes() as u64) else {
            continue;
        };

        let addr = if byte_offset > 0 {
            pointer_expr.clone().bvadd(Expr::bitvec_const(byte_offset as i64, POINTER_WIDTH))
        } else {
            pointer_expr.clone()
        };

        if matches!(
            field_ty.kind(),
            TyKind::RigidTy(
                RigidTy::Array(..)
                    | RigidTy::Adt(..)
                    | RigidTy::Tuple(..)
                    | RigidTy::Ref(..)
                    | RigidTy::RawPtr(..)
                    | RigidTy::Dynamic(..)
            )
        ) {
            // Part of #1739: For single-constructor ADTs with all-scalar fields,
            // reconstruct from per-scalar memory loads instead of load_from_memory.
            // try_decompose_struct_store writes to per-scalar arrays (e.g., mem_u128),
            // but load_from_memory reads from the struct's typed array (e.g.,
            // mem_defs_DummyImpl) which was never written. Reconstruct the struct
            // from scalar loads to match the store decomposition path.
            // Also handles Dynamic types by normalizing to concrete first.
            let reconstruct_ty = if matches!(field_ty.kind(), TyKind::RigidTy(RigidTy::Dynamic(..)))
            {
                ctx.normalize_unique_dyn_tail_ty(*field_ty)
            } else {
                *field_ty
            };
            if let Some(reconstructed) =
                try_reconstruct_adt_from_scalar_loads(ctx, &addr, reconstruct_ty)
            {
                map.insert((local_idx, field_idx), reconstructed);
                continue;
            }
            if let Some(loaded) = ctx.load_from_memory(addr.clone(), *field_ty) {
                map.insert((local_idx, field_idx), loaded);
                continue;
            }
            map.insert((local_idx, field_idx), addr);
            continue;
        }

        let Some(type_key) = scalar_type_key(*field_ty) else {
            map.insert((local_idx, field_idx), addr);
            continue;
        };
        let elem_sort = ctx.elem_sort_for_memory_array(*field_ty);
        let (arr_name, arr_out_name, declared_elem_sort, is_new) =
            ctx.heap_state.get_or_create_type_array(&type_key, elem_sort, &ctx.fn_name);
        if is_new {
            let arr_sort = Sort::array(Sort::bitvec(POINTER_WIDTH), declared_elem_sort.clone());
            ctx.push_late_state_var_pair(std::sync::Arc::clone(&arr_name), &arr_out_name, arr_sort);
        }
        ctx.heap_state.mark_type_array_read(&arr_name, ctx.current_encode_bb);
        let arr_sort = Sort::array(Sort::bitvec(POINTER_WIDTH), declared_elem_sort.clone());
        let arr_expr = if let Some(chain_expr) = ctx.heap_state.get_store_chain(&type_key) {
            chain_expr.clone()
        } else {
            Expr::var(&*arr_name, arr_sort)
        };

        map.insert((local_idx, field_idx), arr_expr.select(addr));
    }
}

fn pointer_storage_expr<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    param_expr: &Expr,
) -> Option<Expr> {
    if *param_expr.sort() == Sort::bitvec(POINTER_WIDTH) {
        Some(param_expr.clone())
    } else {
        ctx.extract_pointer_storage_expr(param_expr)
            .filter(|ptr| *ptr.sort() == Sort::bitvec(POINTER_WIDTH))
    }
}

/// Pre-populate `inline_self_field_hints` when the first call argument
/// references a flattened local.
///
/// Part of #3830: The inline walker's `build_self_field_map` receives a
/// BV64 pointer expression for `self` and tries to load fields from heap
/// memory. When the underlying local is flattened, the data lives in scalar
/// state vars, not heap arrays. This function detects that case and provides
/// the field expressions directly so the inline walker can use them.
pub(in crate::codegen_ay::chc) fn populate_inline_self_field_hints<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    dcx: &DispatchCallContext<'_>,
) {
    let first_arg = match dcx.args.first() {
        Some(arg) => arg,
        None => return,
    };
    populate_inline_self_field_hints_for_arg(ctx, first_arg, Some(dcx));
}

pub(in crate::codegen_ay::chc) fn populate_inline_self_field_hints_for_arg<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    first_arg: &Operand,
    dcx: Option<&DispatchCallContext<'_>>,
) {
    let arg_local = match first_arg {
        Operand::Copy(p) | Operand::Move(p)
            if p.projection.is_empty()
                || p.projection.iter().all(|proj| matches!(proj, ProjectionElem::Deref)) =>
        {
            p.local
        }
        _ => return,
    };
    if let Some(owner_local) =
        dcx.and_then(|dcx| ctx.resolve_coroutine_call_arg_owner_local(dcx, 1))
        && let Some(root_expr) = ctx.resolve_local_expr(owner_local, &HashSet::new())
    {
        let Some(local_decl) = ctx.body.locals().get(arg_local) else {
            return;
        };
        let Some(sort) = ChcCtx::translate_ty(local_decl.ty) else {
            return;
        };
        let Some(dt) = sort.datatype_sort() else {
            return;
        };
        if dt.constructors.len() == 1 && !dt.constructors[0].fields.is_empty() {
            let mut hints = HashMap::new();
            hints.insert((1, DIRECT_DEREF_FIELD), root_expr.clone());
            hints.insert((1, 0), root_expr);
            debug!(
                arg_local,
                owner_local,
                field_count = hints.len(),
                "fn_inline: populated coroutine self field hint"
            );
            ctx.inline_self_field_hints = Some(hints);
            return;
        }
    }
    // Fix A (UnsizedCoercion basic_inner): when the receiver re-roots into a
    // sub-field (e.g. `&outer.inner`), the flattened self-field-hint fast path
    // maps the callee's `self` fields against the WHOLE flattened local
    // (`outer`), dropping the `.inner` sub-field offset — so `Inner::id`'s
    // `self.id` (field 0) reads `Outer.field0` (= outer_id) instead of
    // `outer.inner.id`. Skip the flattened fast path and let
    // `build_self_field_map` fall through to the memory-load path
    // (`extend_field_map_for_param`), exactly what the passing
    // box_inner_coercion.rs already does.
    if receiver_reroots_into_field(ctx, arg_local) {
        debug!(
            arg_local,
            "fn_inline: receiver re-roots into sub-field; skipping flattened self hints (Fix A)"
        );
        return;
    }
    let Some(target_local) = resolve_flattened_self_source_local(ctx, arg_local) else {
        return;
    };
    if let Some(hints) = flattened_self_field_hints_for_target(ctx, target_local, 1) {
        debug!(
            target_local,
            field_count = hints.len(),
            "fn_inline: populated flattened self field hints (#3830)"
        );
        ctx.inline_self_field_hints = Some(hints);
    }
}

/// Fix A helper: does the receiver's ref chain carry a `Field` re-rooting
/// projection (e.g. `&outer.inner`)?
///
/// When true, the flattened self-field-hint fast path would map the callee's
/// `self` fields against the whole flattened local and drop the sub-field
/// offset, reading the wrong scalar slot. The caller skips the fast path and
/// uses the memory-load path instead.
fn receiver_reroots_into_field<'tcx, 'body>(ctx: &ChcCtx<'tcx, 'body>, arg_local: usize) -> bool {
    let has_field =
        |projs: &[ProjectionElem]| projs.iter().any(|p| matches!(p, ProjectionElem::Field(..)));
    if let Some(rt) = ctx.ref_resolution.ref_targets.get(&arg_local)
        && has_field(&rt.projections)
    {
        return true;
    }
    if let Some(rt) = trace_pointer_identity_ref_target(ctx, arg_local)
        && has_field(&rt.projections)
    {
        return true;
    }
    false
}

/// Fix A helper: does the flattened `target_local`'s type match the callee's
/// `self` pointee sort?
///
/// Only then is it sound to reuse `target_local`'s whole flattened layout as
/// the self field map. A proven mismatch means the receiver re-roots into a
/// sub-field (e.g. `&outer.inner` where `self: &Inner` but the base local is
/// `Outer`), which must use the per-field memory-load path instead.
///
/// Conservative: returns `true` (allow the fast path, preserving prior
/// behavior) whenever either sort is unavailable — it only blocks on a
/// positively-proven type mismatch.
fn flattened_target_matches_pointee<'tcx, 'body>(
    ctx: &ChcCtx<'tcx, 'body>,
    target_local: usize,
    self_pointee_sort: Option<&Sort>,
) -> bool {
    let Some(pointee_sort) = self_pointee_sort else {
        return true;
    };
    let Some(local_decl) = ctx.body.locals().get(target_local) else {
        return true;
    };
    let Some(target_sort) = ChcCtx::translate_ty(local_decl.ty) else {
        return true;
    };
    target_sort == *pointee_sort
}

fn flattened_self_field_hints_for_target<'tcx, 'body>(
    ctx: &ChcCtx<'tcx, 'body>,
    target_local: usize,
    self_local: usize,
) -> Option<HashMap<(usize, usize), Expr>> {
    let local_decl = ctx.body.locals().get(target_local)?;
    let sort = ChcCtx::translate_ty(local_decl.ty)?;
    let dt = sort.datatype_sort()?;
    if dt.constructors.len() != 1 {
        return None;
    }

    let no_modified = HashSet::new();
    let mut hints = HashMap::new();
    if let Some(expr) = ctx.reconstruct_flattened_bare_read(target_local, &no_modified) {
        hints.insert((self_local, DIRECT_DEREF_FIELD), expr);
    }
    let mut slot_offset = 0;
    for (field_idx, field) in dt.constructors[0].fields.iter().enumerate() {
        let leaf_sorts = collect_leaf_sorts(&field.sort, 0);
        let leaf_count = leaf_sorts.len();
        if leaf_count == 1 {
            if let Some(expr) =
                ctx.flattened_local_field_expr(target_local, slot_offset, &no_modified)
            {
                hints.insert((self_local, field_idx), expr);
            }
        } else if let Some(inner_dt) = field.sort.datatype_sort()
            && inner_dt.constructors.len() == 1
        {
            let cons = &inner_dt.constructors[0];
            let sub_exprs: Option<Vec<_>> = cons
                .fields
                .iter()
                .enumerate()
                .map(|(sub_idx, _)| {
                    ctx.flattened_local_field_expr(
                        target_local,
                        slot_offset + sub_idx,
                        &no_modified,
                    )
                })
                .collect();
            if let Some(sub_exprs) = sub_exprs {
                let constructed = Expr::datatype_constructor(
                    &inner_dt.name,
                    &cons.name,
                    sub_exprs,
                    field.sort.clone(),
                );
                hints.insert((self_local, field_idx), constructed);
            }
        }
        slot_offset += leaf_count;
    }

    (!hints.is_empty()).then_some(hints)
}
