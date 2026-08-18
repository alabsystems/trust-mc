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

use ay_bindings::Expr;
use rustc_public::mir::{AggregateKind, LocalDecl, Operand};
use rustc_public::ty::{CoroutineDef, GenericArgs, RigidTy};
use std::collections::HashMap;
use tracing::debug;

use super::codegen_types::CodegenTypes;
use super::inline_shared::{PlaceResolver, inline_operand_to_expr};
use super::{ChcCtx, chc_fresh_name, declare_pending_var};
use crate::codegen_ay::coroutine_layout::build_coroutine_sort_info;
use crate::codegen_ay::types::{SignExtension, coerce_bitvec_width, ptr_sort};
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

    // Get the destination type to determine the target sort.
    let dest_ty = dest_local.and_then(|l| locals.get(l)).map(|ld| ld.ty)?;
    let sort = ChcCtx::translate_ty(dest_ty)?;

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
        operand_exprs.push(inline_operand_to_expr(ctx, op, local_exprs, resolver, locals)?);
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
        let field_sort = &cons.fields[i].sort;

        // Coerce BV width if needed (e.g., u32 operand into usize field).
        let coerced = if *expr.sort() == *field_sort {
            expr
        } else if expr.sort().is_bool() && field_sort.is_bitvec() {
            let width = field_sort.bitvec_width()?;
            Expr::ite(expr, Expr::bitvec_const(1u64, width), Expr::bitvec_const(0u64, width))
        } else if expr.sort().is_bitvec() && field_sort.is_bool() {
            let width = expr.sort().bitvec_width()?;
            expr.ne(Expr::bitvec_const(0u64, width))
        } else if expr.sort().is_bitvec() && field_sort.is_bitvec() {
            if let (Some(src_w), Some(dst_w)) =
                (expr.sort().bitvec_width(), field_sort.bitvec_width())
            {
                if src_w != dst_w {
                    coerce_bitvec_width(expr, dst_w, SignExtension::ZeroExtend)
                } else {
                    expr
                }
            } else {
                expr
            }
        } else {
            expr
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
    Some(Expr::datatype_constructor(&dt_name, &cons_name, field_values, sort.clone()))
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
                None => declare_pending_var(
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
    let direct_expr = Expr::datatype_constructor(
        direct_sort_name,
        direct_cons,
        direct_field_exprs,
        info.direct_fields.sort.clone(),
    );

    let mut root_field_exprs = Vec::with_capacity(1 + info.variants.len());
    root_field_exprs.push(direct_expr);
    for variant in &info.variants {
        let fresh_name = chc_fresh_name("__coroutine_variant_view");
        root_field_exprs.push(declare_pending_var(fresh_name, variant.sort.clone()));
    }

    let cons = crate::codegen_ay::names::resolve_ctor_name(&info.root_sort, &coro_name);
    Some(Expr::datatype_constructor(coro_name, cons, root_field_exprs, info.root_sort))
}
