// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Shared Mem-level call-result mirroring helpers.
//!
//! Reconstructs flattened destinations through their post-assignment output
//! locals before storing them to typed memory.

use std::collections::HashSet;

use ay_bindings::Expr;
use rustc_public::mir::Place;
use rustc_public::ty::{GenericArgKind, RigidTy, TyKind};
use tracing::debug;

use crate::args::ChcTrackLevel;
use crate::codegen_ay::types::POINTER_WIDTH;

use super::ChcCtx;

/// Rebuild the post-assignment destination value before mirroring it to typed
/// memory, so flattened call results preserve their tag/payload contract.
pub(in crate::codegen_ay::chc) fn build_call_result_memory_bridge_constraints(
    ctx: &mut ChcCtx<'_, '_>,
    dest_local: usize,
    result_expr: &Expr,
    modified_locals: &HashSet<usize>,
) -> Vec<Expr> {
    if ctx.track_level < ChcTrackLevel::Mem {
        return Vec::new();
    }

    let mut bridge_modified = modified_locals.clone();
    bridge_modified.insert(dest_local);
    let local_place = Place { local: dest_local, projection: vec![] };
    let is_flattened = ctx.flatten.flattened_tuple_locals.contains(&dest_local)
        || ctx.flatten.enum_bv_layouts.contains_key(&dest_local);
    let bridge_value = if let Some(value) =
        ctx.build_canonical_enum_bv_bridge_value(dest_local, result_expr)
    {
        value
    } else if is_flattened {
        let Some(value) = ctx.translate_place_with_modified(&local_place, &bridge_modified) else {
            return Vec::new();
        };
        value
    } else {
        result_expr.clone()
    };
    let Some(addr_loc) = ctx.translate_ref_to_address(&local_place, &bridge_modified) else {
        return Vec::new();
    };
    // `translate_ref_to_address` is a wave-11 address producer, so this local
    // is an address by construction. The three consumers below
    // (`build_memory_store` and the two field-decomposition helpers) are
    // wave-13 territory and still take a bare `Expr`, so the tag is dropped
    // exactly once, here, instead of being re-derived by each of them.
    let addr_expr = addr_loc.into_expr();

    let local_ty = ctx.body.locals()[dest_local].ty;
    let mut mem_constraints = Vec::new();
    // Part of #3962: suppress heap-access safety checks for synthetic bridge
    // stores (same pattern as mirror_ref_value_to_memory in
    // codegen_stmt_memory_bridge.rs).
    let prev_suppress = ctx.suppress_heap_store_checks;
    ctx.suppress_heap_store_checks = true;
    if let Some(store) =
        ctx.build_memory_store_untyped(addr_expr.clone(), bridge_value.clone(), local_ty)
    {
        mem_constraints.push(store);
    }
    // Part of #3962: decompose struct/enum fields into their type-indexed memory
    // arrays. Without this, the aggregate Result<u8,u8> is stored to
    // mem_std_result_Result_u8_u8 but the individual u8 payloads are never stored
    // to mem_u8, causing reference-based reads (PartialEq::eq) to see
    // unconstrained values.
    if bridge_value.sort().is_datatype() {
        ctx.try_decompose_struct_store(&addr_expr, &bridge_value, local_ty, &mut mem_constraints);
    }
    // Part of #3963: Always try flattened enum decomposition for multi-constructor
    // enum locals (Result, Option), regardless of bridge_value sort. For
    // AtomicBool CAS, translate_place_with_modified returns BV8 (not Datatype)
    // so the is_datatype() gate above is skipped. The flattened enum
    // decomposition reads from flattened_field_env — independent of bridge_value
    // sort — so it fires correctly even when the aggregate reconstruction fails.
    try_decompose_flattened_enum_field_stores(
        ctx,
        dest_local,
        &addr_expr,
        local_ty,
        &bridge_modified,
        &mut mem_constraints,
    );
    ctx.suppress_heap_store_checks = prev_suppress;
    mem_constraints.append(&mut ctx.heap_state.pending_updates);
    mem_constraints.append(&mut ctx.heap_state.drain_store_chains(&ctx.diagnostics));
    mem_constraints
}

/// Store flattened enum fields (discriminant + payload) to type-indexed memory.
///
/// Fixes #3962: For multi-constructor enums like `Result<u8, u8>`, the aggregate
/// Datatype store goes to `mem_std_result_Result_u8_u8` but the fn_inline
/// PartialEq path reads individual bytes from `mem_u8` at variant field offsets.
/// This function bridges that gap by storing each flattened field at its layout
/// offset.
#[allow(clippy::needless_range_loop)]
pub(in crate::codegen_ay::chc) fn try_decompose_flattened_enum_field_stores(
    ctx: &mut ChcCtx<'_, '_>,
    dest_local: usize,
    addr_expr: &Expr,
    local_ty: rustc_public::ty::Ty,
    modified_locals: &HashSet<usize>,
    constraints: &mut Vec<Expr>,
) {
    // Only handle flattened enum locals.
    if !ctx.flatten.flattened_tuple_locals.contains(&dest_local)
        && !ctx.flatten.enum_bv_layouts.contains_key(&dest_local)
    {
        return;
    }

    // Only handle ADT enums (Result, Option, etc.).
    let TyKind::RigidTy(RigidTy::Adt(def, args)) = local_ty.kind() else {
        return;
    };
    let variants = def.variants();
    if variants.len() < 2 {
        return;
    }

    let field_count = ctx.flattened_field_count(dest_local);
    if field_count < 2 {
        return;
    }

    let variant_0_fields = variants[0].fields();

    // Store payload fields at variant field offsets.
    for payload_idx in 0..variant_0_fields.len().min(field_count - 1) {
        let flat_field_idx = payload_idx + 1; // skip discriminant
        let Some(field_expr) =
            ctx.flattened_local_field_expr(dest_local, flat_field_idx, modified_locals)
        else {
            continue;
        };

        let Some(offset) = ctx.get_variant_field_offset(local_ty, 0, payload_idx) else {
            continue;
        };

        let field_addr = if offset > 0 {
            addr_expr.clone().bvadd(Expr::bitvec_const(offset as i64, POINTER_WIDTH))
        } else {
            addr_expr.clone()
        };

        // Resolve generic Param types (e.g., Param(0) → u8 for Result<u8, u8>)
        // using the ADT's own GenericArgs. Without this, stores go to
        // mem_param_0 instead of mem_u8.
        let raw_field_ty = variant_0_fields[payload_idx].ty();
        let field_ty = match raw_field_ty.kind() {
            TyKind::Param(param_ty) => args
                .0
                .get(param_ty.index as usize)
                .and_then(|arg| match arg {
                    GenericArgKind::Type(resolved) => Some(*resolved),
                    _ => None,
                })
                .unwrap_or(raw_field_ty),
            _ => raw_field_ty,
        };
        constraints.extend(ctx.build_memory_store_untyped(field_addr, field_expr, field_ty));
    }

    // Store the discriminant tag byte.
    if let Some(discr_expr) = ctx.flattened_local_field_expr(dest_local, 0, modified_locals) {
        let discr_offset = ctx.get_field_offset(local_ty, 0);

        if let Some(offset) = discr_offset {
            let discr_addr = if offset > 0 {
                addr_expr.clone().bvadd(Expr::bitvec_const(offset as i64, POINTER_WIDTH))
            } else {
                addr_expr.clone()
            };

            // Convert Bool discriminant to BV8 for storage in mem_u8.
            let discr_bv8 = if discr_expr.sort().is_bool() {
                Expr::ite(discr_expr, Expr::bitvec_const(1u64, 8), Expr::bitvec_const(0u64, 8))
            } else if discr_expr.sort().bitvec_width() == Some(8) {
                discr_expr
            } else if let Some(w) = discr_expr.sort().bitvec_width() {
                if w < 8 { discr_expr.zero_extend(8 - w) } else { discr_expr.extract(7, 0) }
            } else {
                return;
            };

            let u8_ty = rustc_public::ty::Ty::unsigned_ty(rustc_public::ty::UintTy::U8);
            constraints.extend(ctx.build_memory_store_untyped(discr_addr, discr_bv8, u8_ty));
        }
    }

    debug!(
        dest_local,
        field_count, "Part of #3963: decomposed flattened enum fields to type-indexed memory"
    );
}
