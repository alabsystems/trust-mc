// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Multi-field Aggregate inline translation for struct/tuple constructors.
//!
//! Part of #3561: Enables inline translation of struct constructors like
//! `SolverState { scopes, scope_len, trail_len, next_var }`. Without this,
//! the inline walker cannot track locals assigned from multi-field aggregates,
//! causing downstream projected reads/writes to bail.

use crate::codegen_ay::chc::codegen_ctx::{ExactVar, Havoc, sound_havoc};
use ay_bindings::Expr;
use rustc_public::mir::{AggregateKind, LocalDecl, Operand};
use rustc_public::ty::{CoroutineDef, GenericArgs, RigidTy, TyKind};
use std::collections::HashMap;
use tracing::debug;

use super::codegen_types::CodegenTypes;
use super::inline_shared::{PlaceResolver, inline_operand_to_expr};
use super::{ChcCtx, chc_fresh_name};
use crate::codegen_ay::coroutine_layout::build_coroutine_sort_info;
use crate::codegen_ay::types::ptr_sort;
use crate::rustc_public_bridge::IndexedVal;

/// Translate a Rvalue::Aggregate into a AY Datatype constructor.
///
/// Handles multi-field structs/tuples and zero-field enum variants (like `None`).
/// Part of #3561 (multi-field), #3889 (zero-field variant).
pub(in crate::codegen_ay) fn inline_aggregate_to_expr<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    kind: &AggregateKind,
    operands: &[Operand],
    local_exprs: &HashMap<usize, Expr>,
    resolver: &PlaceResolver<'_>,
    locals: &[LocalDecl],
    dest_local: Option<usize>,
) -> Option<Expr> {
    if let AggregateKind::Coroutine(def, args) = kind {
        return inline_coroutine_aggregate_to_expr(
            ctx,
            *def,
            args,
            operands,
            local_exprs,
            resolver,
            locals,
        );
    }

    if let AggregateKind::Array(elem_ty) = kind {
        return inline_array_aggregate_to_expr(
            ctx,
            *elem_ty,
            operands,
            local_exprs,
            resolver,
            locals,
        );
    }

    // Get the destination type to determine the target sort.
    let dest_ty = dest_local.and_then(|l| locals.get(l)).map(|ld| ld.ty)?;
    let Some(sort) = ChcCtx::translate_ty(dest_ty) else {
        debug!(?dest_ty, "inline_aggregate: destination type does not translate");
        return None;
    };

    // `translate_ty` erases the layer of a one-element tuple, including
    // RustCall's `(argument,)`. Reconstruct that representation before the
    // datatype-only path: a scalar/address payload has no constructor, and a
    // datatype payload has its OWN fields, not the tuple's sole field. Never
    // widen a stored element value into an address merely to fit this tuple.
    if matches!(kind, AggregateKind::Tuple)
        && matches!(dest_ty.kind(), TyKind::RigidTy(RigidTy::Tuple(fields)) if fields.len() == 1)
        && let [operand] = operands
    {
        let TyKind::RigidTy(RigidTy::Tuple(fields)) = ctx.resolve_body_ty(dest_ty).kind() else {
            return None;
        };
        let reference = ctx.resolve_body_ty(fields[0]);
        let payload = inline_operand_to_expr(ctx, operand, local_exprs, resolver, locals)?;
        if let TyKind::RigidTy(RigidTy::Ref(_, pointee, mutability)) = reference.kind()
            && !ctx.inline_walk_operand_is_address(operand)
        {
            // A walker can intentionally bind &T to T's logical value. Carry
            // that value through RustCall's erased singleton layer only when
            // the binder/borrow established it, its scalar sort is exact, and
            // the downstream Fn ABI cannot mistake its shape for an address.
            if ctx.inline_walk_operand_is_referent(operand)
                && (payload.sort().is_bool() || payload.sort().is_bitvec())
                && ChcCtx::translate_ty(ctx.resolve_body_ty(pointee)).as_ref()
                    == Some(payload.sort())
                && (crate::codegen_ay::chc::dyn_coercion::extract_pointer_expr(&payload).is_none()
                    || (mutability == rustc_public::mir::Mutability::Not
                        && ctx.readonly_ref_value_matches(operand, reference)))
            {
                if mutability == rustc_public::mir::Mutability::Mut
                    && ctx.inline_operand_mut_ref_owner(operand).is_none()
                {
                    ctx.record_sound_fallback_reason(
                        super::inline_mut_ref_owner::MUT_REF_OWNER_UNRESOLVED,
                    );
                    return None;
                }
                return Some(payload);
            }
            if mutability == rustc_public::mir::Mutability::Mut {
                ctx.record_sound_fallback_reason(
                    super::inline_mut_ref_owner::MUT_REF_OWNER_UNRESOLVED,
                );
            }
            // A reference can still be a logical referent value in this walk.
            // Matching BV64 sorts do not distinguish &u64 from a u64 value.
            return None;
        }
        return (payload.sort() == &sort).then_some(payload);
    }

    // Native BoxRaw has one complete thin pointer field and a ZST marker.
    // Preserve that field under the same authenticated representation rule as
    // type translation; do not construct a datatype around pointer bits.
    if let TyKind::RigidTy(RigidTy::Adt(def, args)) = ctx.resolve_body_ty(dest_ty).kind()
        && let Some((index, field_ty)) =
            crate::codegen_ay::shared::native_box_raw::native_box_raw_pointer_field(
                ctx.tcx, def, &args,
            )
        && let AggregateKind::Adt(kind_def, variant, _, _, _) = kind
    {
        if *kind_def != def || variant.to_index() != 0 || operands.len() != 2 {
            return None;
        }
        let pointer = inline_operand_to_expr(ctx, &operands[index], local_exprs, resolver, locals)?;
        return (pointer.sort() == &sort && ChcCtx::translate_ty(field_ty).as_ref() == Some(&sort))
            .then_some(pointer);
    }

    // `Layout` is the opaque `bv128 = concat(size, align)` of the allocator
    // models (`translate_ty`, `extract_layout_size_align`): built exactly from
    // its two pointer-width fields (the statement path's
    // `codegen_stmt_aggregate_adt_special`, without its defaults for an
    // operand that does not translate). Declined before, so a walked
    // `Layout::from_size_align_unchecked` left the layout unpopulated and
    // every `__rust_dealloc` below it without a stated size (package round 2
    // item e).
    if let AggregateKind::Adt(def, _, _, _, _) = kind
        && sort.bitvec_width() == Some(128)
        && operands.len() == 2
        && {
            let name = rustc_public::CrateDef::name(def);
            name.rsplit("::").next() == Some("Layout")
        }
    {
        let size = inline_operand_to_expr(ctx, &operands[0], local_exprs, resolver, locals)?;
        let align = inline_operand_to_expr(ctx, &operands[1], local_exprs, resolver, locals)?;
        let pointer = Some(crate::codegen_ay::types::POINTER_WIDTH);
        if size.sort().bitvec_width() != pointer || align.sort().bitvec_width() != pointer {
            debug!("inline_aggregate: Layout field is not pointer-width, declining");
            return None;
        }
        return Some(size.concat(align));
    }

    // Only handle Datatype sorts (structs/tuples encoded as AY Datatypes).
    let dt = match sort.inner() {
        ay_bindings::SortInner::Datatype(dt) => dt,
        _ => {
            debug!("inline_aggregate: dest sort is not Datatype, skipping");
            return None;
        }
    };

    // Part of #3889: Select constructor by variant index from AggregateKind.
    // For enums (Option, Result), the variant index determines which constructor
    // to use (e.g., None=0, Some=1). For structs, variant index is always 0.
    let variant_idx = match kind {
        AggregateKind::Adt(_, variant, _, _, _) => {
            use crate::rustc_public_bridge::IndexedVal;
            variant.to_index()
        }
        _ => 0,
    };
    let cons = dt.constructors.get(variant_idx).or_else(|| dt.constructors.first())?;
    if cons.fields.len() != operands.len() {
        debug!(
            variant_idx,
            fields = cons.fields.len(),
            operands = operands.len(),
            "inline_aggregate: field/operand count mismatch"
        );
        return None;
    }

    // Translate all operands ONCE — `inline_operand_to_expr` can declare pending
    // vars, so it must not be run twice for the same operand.
    let mut operand_exprs = Vec::with_capacity(operands.len());
    for op in operands {
        let Some(expr) = inline_operand_to_expr(ctx, op, local_exprs, resolver, locals) else {
            debug!(?op, "inline_aggregate: operand does not translate");
            return None;
        };
        operand_exprs.push(expr);
    }

    // TRANSPARENT WRAPPER PASS-THROUGH.
    //
    // `translate_ty` collapses payload-shaped wrappers — `MaybeUninit<T>`,
    // `ManuallyDrop<T>`, `#[repr(transparent)]` newtypes — onto the sort of the
    // PAYLOAD, so `MaybeUninit<AscII>` and `AscII` are the same sort. An
    // aggregate that *builds the wrapper* (`_0 = MaybeUninit::<AscII> { value:
    // move _2 }`, a union aggregate whose one operand is already an `AscII`)
    // must therefore hand the payload straight back. Feeding it to the loop
    // below instead matches it against the payload's OWN field list and
    // re-wraps it: `AscII_mk(<AscII>)`, whose argument sort is `AscII` where
    // the constructor declares `fld_inner: BitVec 8`. Nothing rejects that
    // term at construction; it travels until a consumer asks for the declared
    // field sort — `reinterpret_fixed_layout_expr` selects `fld_inner`, gets
    // the datatype back from ay's selector-over-constructor fold, and aborts
    // codegen in `Expr::extract` (#3312 raw_ptr).
    //
    // A genuine one-field struct cannot be mistaken for this: its field sort is
    // a strict component of its own sort, so `operand.sort() == sort` is
    // exactly the wrapper case.
    if operand_exprs.len() == 1 && *operand_exprs[0].sort() == sort {
        debug!(dt_name = %dt.name, "inline_aggregate: transparent wrapper, passing payload through");
        return operand_exprs.pop();
    }

    let mut field_values = Vec::with_capacity(operands.len());
    for (i, expr) in operand_exprs.into_iter().enumerate() {
        // A datatype-involved sort mismatch declines instead of emitting an
        // ill-sorted constructor that AY's parser rejects (see `ctor_field`).
        let expr_sort = expr.sort().clone();
        let Some(coerced) =
            super::inline_shared::ctor_field::coerce_inline_ctor_field(expr, &cons.fields[i].sort)
        else {
            debug!(
                field = i,
                ?expr_sort,
                field_sort = ?cons.fields[i].sort,
                "inline_aggregate: field sort mismatch"
            );
            ctx.record_aggregate_gap("inline_ctor_field_sort_mismatch");
            return None;
        };
        field_values.push(coerced);
    }

    let dt_name = dt.name.clone();
    let cons_name = cons.name.clone();
    debug!(
        %dt_name,
        operand_count = operands.len(),
        "inline_aggregate: constructing Datatype (Part of #3561)"
    );
    // Declines a field-sort mismatch instead of panicking the harness.
    super::inline_shared::checked_inline_variant_constructor(
        &dt_name,
        &cons_name,
        field_values,
        sort.clone(),
    )
}

#[cfg(all(test, feature = "compiler-corpus-tests"))]
mod tests;

/// `[v0, v1, ..]` in a walked body: the array the statement path builds
/// (`translate_array_aggregate`), exactly.
///
/// The sort is `translate_ty`'s for `[T; N]`: `Array<usize, E>` with a
/// flattenable datatype element packed to its bitvector
/// (`flatten_dt_array_element`, which the walker's `Index` read unpacks,
/// `try_unflatten_bv_to_datatype`), and `Bool` for a zero-sized element. The
/// base is the constant array of `v0`, so every in-bounds index reads exactly
/// its element and nothing is left free; an out-of-bounds read is a bounds
/// check's failure before it is a value. Every operand must translate and
/// store at the element sort exactly (the same sort, or a datatype packed by
/// the flatten `translate_ty` assumes); otherwise the aggregate declines and
/// the local stays unpopulated, as before.
///
/// This was declined outright (`inline_aggregate_to_expr` built datatype
/// sorts only), so every read of an array a walked body built was
/// untranslatable: a check over it became an uncertified reach check and a
/// call taking it was havocked (fix/chc-walker-fail-closed, package round 2
/// item c; the eight known-red safe rows of that branch).
fn inline_array_aggregate_to_expr<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    elem_ty: rustc_public::ty::Ty,
    operands: &[Operand],
    local_exprs: &HashMap<usize, Expr>,
    resolver: &PlaceResolver<'_>,
    locals: &[LocalDecl],
) -> Option<Expr> {
    let elem_ty = ctx.resolve_body_ty(elem_ty);
    let is_zst_elem =
        matches!(
            elem_ty.kind(),
            rustc_public::ty::TyKind::RigidTy(RigidTy::Tuple(tys)) if tys.is_empty()
        ) || matches!(elem_ty.kind(), rustc_public::ty::TyKind::RigidTy(RigidTy::Never));
    let mut values = Vec::with_capacity(operands.len());
    for op in operands {
        values.push(inline_operand_to_expr(ctx, op, local_exprs, resolver, locals)?);
    }
    if is_zst_elem {
        // `translate_ty` encodes `[(); N]` as the ZST pipeline's `Bool`.
        return Some(Expr::bool_const(true));
    }
    let raw_elem_sort = ChcCtx::translate_ty(elem_ty)?;
    let elem_sort = crate::codegen_ay::types::flatten_dt_array_element(raw_elem_sort.clone());
    let packs = elem_sort != raw_elem_sort;
    if packs {
        ctx.declare_datatype_sort_if_needed(&raw_elem_sort);
    }
    let mut stored = Vec::with_capacity(values.len());
    for value in values {
        let exact = if *value.sort() == elem_sort {
            Some(value)
        } else if packs && *value.sort() == raw_elem_sort {
            let width = elem_sort.bitvec_width()?;
            crate::codegen_ay::types::flatten_datatype_to_bitvec(&value, width)
                .filter(|packed| packed.sort().bitvec_width() == Some(width))
        } else {
            None
        };
        let Some(exact) = exact else {
            debug!(?elem_sort, "inline array aggregate: element does not store exactly, declining");
            ctx.record_aggregate_gap("inline_array_aggregate_element_sort_mismatch");
            return None;
        };
        stored.push(exact);
    }
    let index_sort = ptr_sort();
    let Some(first) = stored.first().cloned() else {
        // `[]`: every read is out of bounds; any array of the sort is exact
        // (Rule E: no execution reads the value as data).
        return Some(ExactVar::unobserved(
            chc_fresh_name("__inline_empty_array"),
            ay_bindings::Sort::array(index_sort, elem_sort),
        ));
    };
    let mut array = Expr::const_array(index_sort, first);
    for (index, value) in stored.into_iter().enumerate().skip(1) {
        array = array.store(
            Expr::bitvec_const(index as u128, crate::codegen_ay::types::POINTER_WIDTH),
            value,
        );
    }
    debug!(elements = operands.len(), "inline array aggregate: exact store chain");
    Some(array)
}

fn inline_coroutine_aggregate_to_expr<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    def: CoroutineDef,
    args: &GenericArgs,
    operands: &[Operand],
    local_exprs: &HashMap<usize, Expr>,
    resolver: &PlaceResolver<'_>,
    locals: &[LocalDecl],
) -> Option<Expr> {
    let coro_name = crate::codegen_ay::names::coroutine_sort_name(def.0.to_index());
    let coroutine_ty = rustc_public::ty::Ty::from_rigid_kind(RigidTy::Coroutine(def, args.clone()));
    let info = build_coroutine_sort_info(ctx.tcx, coroutine_ty, |field_ty| {
        ChcCtx::translate_ty(field_ty).unwrap_or_else(ptr_sort)
    })?;

    // By-name operand mapping: view fields are offset-ordered while MIR
    // aggregate operands are indexed by MIR field index — pair them via the
    // index encoded in each field's name, never positionally. Fields without
    // a corresponding operand (e.g. promoted saved locals) keep this path's
    // havoc behavior: a fresh unconstrained variable.
    let operand_map = info.direct_fields.operand_map(operands.len())?;
    let mut direct_field_exprs = Vec::with_capacity(info.direct_fields.fields.len());
    for (field, mapped_idx) in info.direct_fields.fields.iter().zip(&operand_map) {
        let expr = match mapped_idx {
            None => match field.sort.bitvec_width() {
                Some(width) => Expr::bitvec_const(0, width),
                None => Expr::bool_const(false),
            },
            Some(mir_idx) => match operands.get(*mir_idx) {
                Some(op) => inline_operand_to_expr(ctx, op, local_exprs, resolver, locals)?,
                None => Havoc::mint(
                    ctx,
                    sound_havoc::UNTRACKED_COROUTINE_STATE,
                    chc_fresh_name("__coroutine_direct_field"),
                    field.sort.clone(),
                ),
            },
        };
        direct_field_exprs.push(expr);
    }

    ctx.declare_datatype_sort_if_needed(&info.root_sort);
    let direct_sort_name = info.direct_fields.sort.datatype_name()?;
    let direct_cons =
        crate::codegen_ay::names::resolve_ctor_name(&info.direct_fields.sort, &direct_sort_name);
    let direct_expr = match Expr::try_datatype_constructor(
        direct_sort_name,
        direct_cons,
        direct_field_exprs,
        info.direct_fields.sort.clone(),
    ) {
        Ok(expr) => expr,
        Err(err) => {
            tracing::debug!(
                ?err,
                "inline_coroutine_aggregate direct fields: datatype constructor signature mismatch; declining"
            );
            return None;
        }
    };

    let mut root_field_exprs = Vec::with_capacity(1 + info.variants.len());
    root_field_exprs.push(direct_expr);
    for variant in &info.variants {
        let fresh_name = chc_fresh_name("__coroutine_variant_view");
        root_field_exprs.push(ExactVar::nondet(fresh_name, variant.sort.clone()));
    }

    let cons = crate::codegen_ay::names::resolve_ctor_name(&info.root_sort, &coro_name);
    Expr::try_datatype_constructor(coro_name, cons, root_field_exprs, info.root_sort)
        .map_err(|err| tracing::debug!(?err, "inline_coroutine_aggregate root: datatype constructor signature mismatch; declining"))
        .ok()
}
