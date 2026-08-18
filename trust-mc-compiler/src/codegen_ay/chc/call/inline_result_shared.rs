// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Shared inline-result epilogue preparation and resolved-destination emission.
//!
//! Top-level inline consumers all need the same post-inline contract:
//! capture returned vtables, mirror the destination into typed memory, write
//! back alias updates, optionally drain pending heap side effects, filter
//! superseded store chains, and then emit the final destination constraints.
//!
//! This module centralizes that shared work so individual call families only
//! keep their genuinely different unresolved-destination fallbacks.

use std::collections::BTreeMap;

use ay_bindings::Expr;
use rustc_public::ty::{RigidTy, TyKind};
use tracing::debug;

use super::ChcCtx;
use super::chc_call_context::DispatchCallContext;
use super::codegen_call_coerce::CallCoerce;
use super::codegen_call_result_mem::build_call_result_memory_bridge_constraints;
use super::codegen_rules::CodegenRules;
use super::inline_alias_writeback::apply_inline_alias_updates;

pub(in crate::codegen_ay::chc) struct InlineResultEpilogueSpec<'dcx> {
    pub dcx: &'dcx DispatchCallContext<'dcx>,
    pub target: usize,
    pub dest_local: usize,
    pub result_expr: Expr,
    pub inline_vtable: Option<Expr>,
    pub fallback_vtable: Option<Expr>,
    pub alias_updates: &'dcx BTreeMap<usize, Expr>,
    pub pre_resolved_args: &'dcx BTreeMap<usize, usize>,
    pub eq_reason: &'static str,
    pub alias_reason: &'static str,
    pub extra_constraints: Vec<Expr>,
    pub extra_dests: Vec<usize>,
    pub drain_pending_updates: bool,
    pub drain_pending_checks: bool,
}

pub(in crate::codegen_ay::chc) struct PreparedInlineResultEpilogue<'dcx> {
    pub dcx: &'dcx DispatchCallContext<'dcx>,
    pub target: usize,
    pub dest_local: usize,
    pub result_expr: Expr,
    pub eq_reason: &'static str,
    pub vtable_constraint: Option<Expr>,
    pub mem_constraints: Vec<Expr>,
    pub extra_constraints: Vec<Expr>,
    pub extra_dests: Vec<usize>,
    filtered_stmts: Option<Vec<Expr>>,
}

impl PreparedInlineResultEpilogue<'_> {
    pub(in crate::codegen_ay::chc) fn effective_stmts(&self) -> &[Expr] {
        self.filtered_stmts.as_deref().unwrap_or(self.dcx.stmt_constraints)
    }
}

fn uses_ref_destination_memory_bridge(ctx: &ChcCtx<'_, '_>, dest_local: usize) -> bool {
    matches!(
        ctx.body.locals()[dest_local].ty.kind(),
        TyKind::RigidTy(RigidTy::Ref(..) | RigidTy::RawPtr(..))
    )
}

/// Part of #4017: After inline return, seed slice metadata side tables for the
/// destination local so that downstream `translate_ptr_metadata` can resolve
/// `.len()` / `size_of_val()` without hitting the symbolic fallback.
///
/// Only runs when `dest_local` is `Ref`/`RawPtr` to `Slice(_)`, `Str`, or an
/// ADT with an unsized slice/str tail (custom DST), and the result expression
/// carries a datatype `fld_len` field.
fn capture_inline_return_slice_metadata(
    ctx: &mut ChcCtx<'_, '_>,
    dest_local: usize,
    result_expr: &Expr,
) {
    let pointee = match ctx.body.locals()[dest_local].ty.kind() {
        TyKind::RigidTy(RigidTy::Ref(_, pointee, _))
        | TyKind::RigidTy(RigidTy::RawPtr(pointee, _)) => pointee,
        _ => return,
    };
    // Part of #4163: also capture metadata for ADTs with unsized slice/str tails
    // (custom DSTs like `MyStr { header: u8, data: str }`).
    let is_fat_slice_ptr = match pointee.kind() {
        TyKind::RigidTy(RigidTy::Slice(_)) | TyKind::RigidTy(RigidTy::Str) => true,
        TyKind::RigidTy(RigidTy::Adt(..)) => {
            use crate::kani_middle::abi::LayoutOf;
            LayoutOf::new(pointee).has_slice_tail()
        }
        _ => false,
    };
    if !is_fat_slice_ptr {
        return;
    }

    let Some(len_expr) = ChcCtx::chc_array_length(result_expr) else {
        return;
    };

    debug!(dest_local, "inline_result: seeding subslice_len from returned slice expression");
    ctx.ref_resolution.subslice_len.insert(dest_local, len_expr);

    // Also seed const_ref_values and const_ref_slice_views if fld_data is present.
    if let Some(dt_name) = result_expr.sort().datatype_name() {
        if let Some(data_sort) = ChcCtx::get_dt_field_sort(result_expr, "fld_data") {
            let data_expr =
                result_expr.clone().field_select(dt_name.to_string(), "fld_data", data_sort);
            ctx.ref_resolution.const_ref_values.insert(dest_local, data_expr);
            ctx.ref_resolution.const_ref_slice_views.insert(dest_local, result_expr.clone());
        }
    }

    ctx.ref_resolution.subslice_offset.remove(&dest_local);
}

/// Seed same-block reads from an inline-return destination with the exact
/// return expression instead of the generic `__out` state variable.
///
/// This preserves concrete pointer-wrapper payloads for later calls in the same
/// basic block (for example `wrapper_return().as_ptr()`), which would otherwise
/// only see an unconstrained destination var. When the returned storage pointer
/// is a zero-offset split pointer, also keep its concrete allocation identity so
/// wrapper-specific handlers can materialize the precise base/value address.
fn capture_inline_return_local_value(
    ctx: &mut ChcCtx<'_, '_>,
    dest_local: usize,
    result_expr: &Expr,
) {
    ctx.encode.local_expr_env.insert(dest_local, result_expr.clone());
    ctx.encode.invalidate_local_cache(dest_local);

    let alloc_obj_id = ctx
        .extract_pointer_storage_expr(result_expr)
        .and_then(|ptr| {
            // Part of #4014: When the fn_inline result is a BV128 produced by
            // zero_extend(64, alloc_ptr), extract_pointer_storage_expr returns
            // extract(63,0, zero_extend(64, alloc_ptr)).  try_extract_constant_addr
            // only recognises BvConcat patterns, so unwrap the
            // extract(zero_extend(...)) to recover the original BV64 constant.
            ChcCtx::try_extract_constant_addr(ptr.as_expr()).or_else(|| {
                use ay_bindings::ExprValue;
                if let ExprValue::BvExtract { expr: inner, high: 63, low: 0 } =
                    ptr.as_expr().value()
                {
                    if let ExprValue::BvZeroExtend { expr: core_expr, .. } = inner.value() {
                        return ChcCtx::try_extract_constant_addr(&core_expr);
                    }
                }
                // Also handle direct zero_extend without extract wrapper.
                if let ExprValue::BvZeroExtend { expr: core_expr, .. } = ptr.as_expr().value() {
                    return ChcCtx::try_extract_constant_addr(&core_expr);
                }
                None
            })
        })
        .and_then(|(obj_id, offset)| (offset == 0).then_some(obj_id));

    if let Some(obj_id) = alloc_obj_id {
        ctx.known_alloc_ids.insert(dest_local, obj_id);
    } else {
        ctx.known_alloc_ids.remove(&dest_local);
    }
}

pub(in crate::codegen_ay::chc) fn prepare_inline_result_epilogue<'dcx>(
    ctx: &mut ChcCtx<'_, '_>,
    spec: InlineResultEpilogueSpec<'dcx>,
) -> PreparedInlineResultEpilogue<'dcx> {
    let mut vtable_constraint = ctx.capture_vtable_discriminant(spec.dest_local, &spec.result_expr);
    if vtable_constraint.is_none()
        && let Some(vtable_expr) = spec.inline_vtable
    {
        vtable_constraint = ctx.capture_known_vtable_discriminant(spec.dest_local, vtable_expr);
    }
    if vtable_constraint.is_none()
        && let Some(vtable_expr) = spec.fallback_vtable
    {
        vtable_constraint = ctx.capture_known_vtable_discriminant(spec.dest_local, vtable_expr);
    }

    capture_inline_return_local_value(ctx, spec.dest_local, &spec.result_expr);

    // Part of #4017: Seed slice metadata side tables for the destination local
    // so that downstream translate_ptr_metadata can resolve .len() / size_of_val()
    // for slice/str references returned from inline calls.
    capture_inline_return_slice_metadata(ctx, spec.dest_local, &spec.result_expr);

    let mut mem_constraints = build_call_result_memory_bridge_constraints(
        ctx,
        spec.dest_local,
        &spec.result_expr,
        spec.dcx.modified_locals,
    );
    let mut extra_dests = Vec::with_capacity(spec.extra_dests.len() + 1);
    extra_dests.push(spec.dest_local);
    for dest in spec.extra_dests {
        if dest != spec.dest_local && !extra_dests.contains(&dest) {
            extra_dests.push(dest);
        }
    }
    let mut extra_constraints = spec.extra_constraints;
    apply_inline_alias_updates(
        ctx,
        spec.dcx,
        spec.alias_updates,
        spec.pre_resolved_args,
        spec.dest_local,
        &mut extra_dests,
        &mut extra_constraints,
        &mut mem_constraints,
        spec.alias_reason,
    );
    if spec.drain_pending_updates {
        super::ptr_receiver_mem::drain_pending_updates(ctx, &mut mem_constraints);
    }
    if spec.drain_pending_checks {
        super::ptr_receiver_mem::drain_pending_checks(ctx, spec.dcx, spec.target);
    }

    let filtered_stmts = super::heap_store_chains::filter_superseded_store_chains(
        spec.dcx.stmt_constraints,
        &mem_constraints,
    );
    PreparedInlineResultEpilogue {
        dcx: spec.dcx,
        target: spec.target,
        dest_local: spec.dest_local,
        result_expr: spec.result_expr,
        eq_reason: spec.eq_reason,
        vtable_constraint,
        mem_constraints,
        extra_constraints,
        extra_dests,
        filtered_stmts,
    }
}

#[allow(clippy::result_large_err)]
pub(in crate::codegen_ay::chc) fn emit_prepared_inline_result<'dcx>(
    ctx: &mut ChcCtx<'_, '_>,
    mut prepared: PreparedInlineResultEpilogue<'dcx>,
) -> Result<(), PreparedInlineResultEpilogue<'dcx>> {
    let effective_stmts = prepared.effective_stmts().to_vec();
    if let Some(mut flat_constraints) = ctx
        .build_flattened_destination_constraints(prepared.dest_local, prepared.result_expr.clone())
    {
        // Include dest_local in extra_dests so all flattened fields
        // (e.g., fld0=discriminant, fld1=payload) appear in the output
        // relation signature. Without this, flattened fields that are
        // constrained (fld0__out = true) but not in the output args
        // become free variables — the constraint is in the rule body
        // but the head relation doesn't carry the output variable,
        // leaving the discriminant unconstrained and causing spurious
        // CTREX for Option<NonZero<u128>> and similar flattened enums.
        let mut flat_extra_dests = prepared.extra_dests.clone();
        if !flat_extra_dests.contains(&prepared.dest_local) {
            flat_extra_dests.push(prepared.dest_local);
        }
        // Part of #discriminant_128bits: Belt-and-suspenders — explicitly mark ALL
        // flattened field state-var indices as modified so they always get __out in
        // the output relation head. The extra_dests expansion in build_output_args
        // should already do this, but empirically fld1 was missing __out for
        // Option<NonZero<u128>>, leaving the payload unconstrained.
        if ctx.flatten.flattened_tuple_locals.contains(&prepared.dest_local) {
            if let Some(base_idx) = ctx.try_state_idx_for_local(prepared.dest_local) {
                let n = ctx.flattened_field_count(prepared.dest_local);
                for i in 0..n {
                    ctx.mark_state_var_modified(base_idx + i);
                }
            }
        }
        let new_output_args =
            ctx.build_output_args(prepared.dcx.modified_locals, &flat_extra_dests);
        if let Some(vc) = &prepared.vtable_constraint {
            flat_constraints.push(vc.clone());
        }
        flat_constraints.append(&mut prepared.mem_constraints);
        flat_constraints.append(&mut prepared.extra_constraints);
        ctx.emit_goto_rule_extra(
            prepared.dcx.from_app,
            prepared.target,
            &new_output_args,
            &effective_stmts,
            flat_constraints,
        );
        return Ok(());
    }
    let new_output_args =
        ctx.build_output_args(prepared.dcx.modified_locals, &prepared.extra_dests);

    let Some((_, dest_var)) = ctx.resolve_destination(prepared.dest_local) else {
        return Err(prepared);
    };
    if uses_ref_destination_memory_bridge(ctx, prepared.dest_local)
        && !prepared.mem_constraints.is_empty()
    {
        debug!(
            fn_name = %ctx.fn_name,
            dest_local = prepared.dest_local,
            "inline result: using memory bridge for reference destination"
        );
        // Part of #4030: The memory bridge writes the result to typed memory
        // arrays (mem_ptr_u8, etc.) but does NOT constrain the destination
        // state variable (_N__out). For Ref destinations this is fine because
        // downstream reads go through memory. But for RawPtr destinations
        // used in comparisons (e.g., `assert_eq!(hi, p2)` after `p1.max(p2)`),
        // the assertion reads the state variable directly — leaving it
        // unconstrained produces spurious counterexamples.
        // Fix: also emit the state variable equality constraint alongside
        // the memory constraints.
        let eq = ctx.make_coerced_eq_constraint(
            &dest_var,
            prepared.result_expr,
            dest_var.sort(),
            prepared.dest_local,
            prepared.eq_reason,
        );
        let extra: Vec<Expr> = eq
            .into_iter()
            .chain(prepared.vtable_constraint)
            .chain(prepared.mem_constraints)
            .chain(prepared.extra_constraints)
            .collect();
        ctx.emit_goto_rule_extra(
            prepared.dcx.from_app,
            prepared.target,
            &new_output_args,
            &effective_stmts,
            extra,
        );
        return Ok(());
    }
    let eq = ctx.make_coerced_eq_constraint(
        &dest_var,
        prepared.result_expr,
        dest_var.sort(),
        prepared.dest_local,
        prepared.eq_reason,
    );
    let extra: Vec<Expr> = eq
        .into_iter()
        .chain(prepared.vtable_constraint)
        .chain(prepared.mem_constraints)
        .chain(prepared.extra_constraints)
        .collect();
    ctx.emit_goto_rule_extra(
        prepared.dcx.from_app,
        prepared.target,
        &new_output_args,
        &effective_stmts,
        extra,
    );
    Ok(())
}
