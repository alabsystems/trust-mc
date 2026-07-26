// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Precise CHC `write_bytes` handler for stack-local full zero overwrites.
//!
//! `mem::zeroed::<T>()` lowers to a `write_bytes(dst, 0u8, count)` intrinsic
//! that fills `count * size_of::<T>()` bytes with zero. The generic
//! `codegen_unconstrained_intrinsic` path leaves the referent unconstrained
//! and records a fallback, which demotes PROOF → CTREX(EncodingGap).
//!
//! This module adds a narrow precise path that handles the common shape:
//! - destination is a whole local (no projection),
//! - byte value is constant `0u8`,
//! - count is concrete,
//! - total write size exactly covers the referent type.
//!
//! When the guard matches, the referent local is constrained to a typed zero
//! expression with no fallback counters recorded.
//!
//! Part of #3702.

use ay_bindings::Expr;
use rustc_public::mir::{BasicBlockIdx, Operand};
use rustc_public::ty::{RigidTy, TyKind};
use tracing::debug;

use super::super::chc_call_context::DispatchCallContext;
use super::super::codegen_call_atomic::resolve_ptr_target_local;
use super::super::codegen_call_coerce::CallCoerce;
use super::super::codegen_rules::CodegenRules;
use super::super::codegen_types::CodegenTypes;
use super::super::{ChcCtx, chc_fresh_name, declare_pending_var};
use crate::kani_middle::abi::LayoutOf;

/// Try to encode `write_bytes(dst, val, count)` when it fully overwrites a
/// stack local.
///
/// Handles both `mem::zeroed()` (val=0) and `mem::uninitialized()` lowering
/// (val=any constant). For zero fills, produces typed zero. For non-zero
/// fills on BV types, produces the repeated-byte constant. When the local is
/// fully overwritten but the byte pattern is not precisely representable,
/// emits a typed fresh value for the whole referent instead of recording a
/// translation-drop fallback.
///
/// Returns `true` if the path was taken (rule emitted, no DEMOTED fallback).
/// Returns `false` if structural guards fail (args missing, dst unresolvable)
/// — caller should use the generic unconstrained fallback.
///
/// Part of #3702 (zero fill), Part of #3798 (any fill / mem::uninitialized).
pub(in crate::codegen_ay::chc) fn try_codegen_full_write_bytes(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    target: BasicBlockIdx,
) -> bool {
    // Guard 1: need at least 3 args (dst, val, count).
    if dcx.args.len() < 3 {
        return false;
    }

    // P4-2: detect the projected-Vec data-start destination up front —
    // `resolve_ptr_target_local` requires an empty projection chain, so a
    // resolved projected-Vec referent IS the `vec.as_mut_ptr()` shape
    // (logical element 0 = buffer start).
    let projected_vec_referent = resolve_ptr_target_local(ctx, &dcx.args[0]).filter(|local| {
        use crate::codegen_ay::chc::codegen_ctx::types::CollectionProjectionKind;
        ctx.collections.projection_locals.get(local).copied() == Some(CollectionProjectionKind::Vec)
    });

    // UB obligations: the written span [dst, dst + count * size_of::<T>())
    // must be writable and aligned, independent of whether the precise fill
    // path below matches. Emitted before the structural guards so the
    // generic unconstrained fallback keeps the checks.
    //
    // P4-2: for a projected-Vec data start the addr-based lane degenerates
    // to `sym_fld_ptr % align == 0` — the fld_ptr state var is a fresh
    // allocator result that is aligned for T by construction, so that
    // obligation is spurious (same shape as the legal-overlap `copy`
    // disjointness). The REAL obligation is the capacity room bound, emitted
    // by `emit_write_bytes_vec_room_checks` in element units against the
    // seeded cap state var.
    if ctx.memory_safety_checks {
        if let Some(vec_local) = projected_vec_referent {
            emit_write_bytes_vec_room_checks(ctx, dcx, target, vec_local);
        } else if let (Some(pointee_ty), Some(dst_addr), Some(count_expr)) = (
            operand_pointee_ty(&dcx.args[0], ctx),
            ctx.translate_operand_with_modified(&dcx.args[0], dcx.modified_locals),
            ctx.translate_operand_with_modified(&dcx.args[2], dcx.modified_locals),
        ) {
            let checks = ctx.heap_span_access_checks(&dst_addr, pointee_ty, &count_expr);
            for check in checks {
                ctx.emit_intrinsic_span_ub_check(dcx.from_app, check, dcx.stmt_constraints, target);
            }
        }
    }

    // Guard 2: dst must resolve to a whole local via ref_targets.
    let Some(referent_local) = resolve_ptr_target_local(ctx, &dcx.args[0]) else {
        return false;
    };

    // UB obligation via the resolved referent: the requested byte span
    // (count * size_of::<T>()) must fit the referent allocation. This covers
    // the common case where the dst operand is an opaque cross-block state
    // var (the address-based checks above skip on unfoldable obj_ids) but
    // ref_targets knows the backing local exactly.
    //
    // P4-2: skipped for projected-Vec referents — the referent LOCAL is the
    // 24-byte Vec header, not the heap buffer, so this bound is the wrong
    // allocation. The capacity room bound above is the real obligation.
    if ctx.memory_safety_checks && projected_vec_referent.is_none() {
        let span_bound =
            ctx.body.locals().get(referent_local).map(|local| local.ty).and_then(|referent_ty| {
                let pointee_ty = operand_pointee_ty(&dcx.args[0], ctx)?;
                let pointee_size = pointee_ty.layout().ok()?.shape().size.bytes();
                if pointee_size == 0 || u32::try_from(pointee_size).is_err() {
                    return None;
                }
                let referent_size = referent_byte_width(ctx, referent_local, referent_ty)?;
                let count_expr =
                    ctx.translate_operand_with_modified(&dcx.args[2], dcx.modified_locals)?;
                let count64 = crate::codegen_ay::types::coerce_bitvec_width_safe(
                    count_expr,
                    crate::codegen_ay::types::POINTER_WIDTH,
                    crate::codegen_ay::types::SignExtension::ZeroExtend,
                );
                let size_expr = Expr::bitvec_const(
                    pointee_size as u128,
                    crate::codegen_ay::types::POINTER_WIDTH,
                );
                let no_mul_overflow = count64.clone().bvmul_no_overflow_unsigned(size_expr.clone());
                let span64 = count64.bvmul(size_expr);
                let referent_size64 = Expr::bitvec_const(
                    referent_size as u128,
                    crate::codegen_ay::types::POINTER_WIDTH,
                );
                Some(vec![no_mul_overflow, span64.bvule(referent_size64)])
            });
        if let Some(checks) = span_bound {
            for check in checks {
                ctx.emit_intrinsic_span_ub_check(dcx.from_app, check, dcx.stmt_constraints, target);
            }
        }
    }

    // Try constant byte value for precise fill.
    let byte_val = extract_const_u8(&dcx.args[1]).or_else(|| {
        ctx.translate_operand_with_modified(&dcx.args[1], dcx.modified_locals)
            .and_then(const_u8_from_expr)
    });
    let count = extract_operand_const_usize(&dcx.args[2]).or_else(|| {
        ctx.translate_operand_with_modified(&dcx.args[2], dcx.modified_locals)
            .and_then(|expr| ChcCtx::const_usize_from_expr(&expr))
            .map(|value| value as u64)
    });

    // WRITE_BYTES_ZERO_COUNT_NOOP: a `write_bytes(dst, val, 0)` writes zero
    // bytes and provably changes no memory, regardless of the pointee type or
    // byte value. Emit a plain identity transition — the referent's value is
    // preserved by the block's accumulated store constraints (unmodified
    // locals pass through their input state var; a local modified earlier in
    // the block keeps its already-pinned output var), and NO translation-drop
    // fallback is recorded.
    //
    // Without this, a zero-count write to a niche type (e.g. the projected-Vec
    // and precise-fill lanes below both require `total_write != 0`) falls into
    // the generic over-approximation path, which records
    // `write_bytes_overapprox` and demotes the SMT PROOF to a tainted
    // OverApproximation CTREX. A zero-count write is a total no-op, so this is
    // sound: the [dst, dst) span's in-bounds/alignment obligations are still
    // emitted above by the memory-safety checks, independent of this value
    // model. `count` is `Some(0)` only for a const-folded zero count; a
    // symbolic count yields `None` and never matches here.
    if count == Some(0) {
        let dest_local: usize = dcx.destination.local;
        let out = ctx.build_output_args(dcx.modified_locals, &[dest_local]);
        ctx.emit_goto_rule(dcx.from_app, target, &out, dcx.stmt_constraints);
        debug!(
            referent_local,
            "CHC: write_bytes zero-count no-op — identity transition (Part of #3702)"
        );
        return true;
    }

    // P4-2: projected-Vec destination — constant byte pattern, constant count.
    // The Vec's logical data array gets a precise prefix fill (elements
    // 0..count-1 = replicated byte, rest preserved by the store chain).
    // Falls through to the existing marked over-approximation when the
    // pattern/count/element shape cannot be encoded precisely.
    //
    // The write_shape lane below must NEVER run for a projected Vec: its
    // "full overwrite" criterion compares against the Vec HEADER layout and
    // would fill the len/cap state with the byte pattern.
    if projected_vec_referent.is_some() {
        if let (Some(bv), Some(cnt)) = (byte_val, count)
            && try_write_bytes_vec_prefix(ctx, dcx, target, referent_local, bv, cnt)
        {
            return true;
        }
        return emit_write_bytes_overapprox(ctx, dcx, target, referent_local, byte_val, count);
    }

    let referent_ty = ctx.body.locals().get(referent_local).map(|local| local.ty);
    let write_shape = referent_ty.and_then(|referent_ty| {
        let pointee_ty = operand_pointee_ty(&dcx.args[0], ctx)?;
        let layout = pointee_ty.layout().ok()?;
        let pointee_size = layout.shape().size.bytes();
        if pointee_size == 0 {
            return None;
        }
        let referent_size = referent_byte_width(ctx, referent_local, referent_ty)?;
        let total_write = (count? as usize).checked_mul(pointee_size)?;
        Some((referent_ty, pointee_size, referent_size, total_write))
    });

    if let Some((referent_ty, _, referent_size, total_write)) = write_shape {
        if total_write < referent_size
            && let Some(bv) = byte_val
            && let Some(fill_expr) =
                partial_prefix_fill_expr(ctx, dcx, referent_local, total_write, bv)
        {
            return emit_write_bytes_fill(ctx, dcx, target, referent_local, fill_expr);
        }

        if total_write != referent_size {
            return emit_write_bytes_overapprox(ctx, dcx, target, referent_local, byte_val, count);
        }

        if let Some(bv) = byte_val {
            let fill_expr = if bv == 0 {
                zero_expr_for_ty(referent_ty)
            } else {
                fill_expr_for_ty(referent_ty, bv)
            };
            if let Some(fill_expr) = fill_expr {
                return emit_write_bytes_fill(ctx, dcx, target, referent_local, fill_expr);
            }
        }

        if let Some(fresh_fill) = fresh_expr_for_local(ctx, referent_local) {
            return emit_write_bytes_fill(ctx, dcx, target, referent_local, fresh_fill);
        }
    }

    emit_write_bytes_overapprox(ctx, dcx, target, referent_local, byte_val, count)
}

fn emit_write_bytes_overapprox(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    target: BasicBlockIdx,
    referent_local: usize,
    byte_val: Option<u8>,
    count: Option<u64>,
) -> bool {
    // Fallback: write_bytes with non-constant val or non-matching size.
    // Emit sound over-approximation: leave referent unconstrained.
    // This is sound because any concrete fill pattern is subsumed by the
    // unconstrained model. No DEMOTED — the encoding is correct (over-approx).
    // Part of #3798: diagnostic to identify which guard fails for uninit patterns.
    // Part of #3798: covers mem::uninitialized() which lowers to write_bytes
    // with a non-constant byte value.
    debug!(
        referent_local,
        ?byte_val,
        ?count,
        "write_bytes: sound over-approximation — precise path guards failed"
    );
    // Task #78: this over-approximation havocs BOTH the return place and the
    // written referent under ONE `place_translation_drop`. Plumb both SMT-var
    // identities (accounting the event once) so the driver can dependency-check
    // the violated `error_p{N}` — the write_bytes overflow/room obligations read
    // count·size, not the havocked buffer, so a genuine overflow certifies.
    let dest_local: usize = dcx.destination.local;
    let dest_freed = ctx.freed_dest_output_var(dest_local);
    let referent_freed = ctx.freed_dest_output_var(referent_local);
    ctx.record_sound_fallback_reason_identified("write_bytes_overapprox", dest_freed.as_deref());
    if let Some(referent_freed) = referent_freed {
        ctx.vc.note_additional_freed_var(&referent_freed);
    }
    let out = ctx.build_output_args(dcx.modified_locals, &[dest_local, referent_local]);
    ctx.emit_goto_rule(dcx.from_app, target, &out, dcx.stmt_constraints);
    true
}

/// P4-2: cap on precise Vec-prefix fill store chains. Larger constant counts
/// fall back to the marked over-approximation path to bound CHC rule size.
const MAX_VEC_PREFIX_FILL_ELEMS: usize = 64;

/// P4-2: room obligations for `write_bytes` on a projected-Vec data start.
///
/// Replaces the addr-based span lane (whose alignment check on the symbolic
/// `fld_ptr` state var is spurious — allocator results are aligned for the
/// element type by construction). The REAL bound: the requested byte span
/// `count * size_of::<T>()` must fit the buffer `cap * elem_width` (cap state
/// var, element units, seeded by the Vec constructor stubs), and the byte
/// product must not wrap.
fn emit_write_bytes_vec_room_checks(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    target: BasicBlockIdx,
    vec_local: usize,
) {
    use crate::codegen_ay::types::{POINTER_WIDTH, SignExtension, coerce_bitvec_width_safe};

    let Some(pointee_ty) = operand_pointee_ty(&dcx.args[0], ctx) else {
        return;
    };
    let Some(pointee_size) = pointee_ty.layout().ok().map(|l| l.shape().size.bytes()) else {
        return;
    };
    if pointee_size == 0 || u32::try_from(pointee_size).is_err() {
        return;
    }
    let Some(count_expr) = ctx.translate_operand_with_modified(&dcx.args[2], dcx.modified_locals)
    else {
        return;
    };
    // Projected Vec layout: base+0 ptr, base+1 len, base+2 cap, base+3 data.
    let Some(base_idx) = ctx.try_state_idx_for_local(vec_local) else {
        return;
    };
    let vars = if dcx.modified_locals.contains(&vec_local) {
        &ctx.state_var_mgr.output_state_vars
    } else {
        &ctx.state_var_mgr.state_vars
    };
    let Some((cap_name, cap_sort)) = vars.get(base_idx + 2).cloned() else {
        return;
    };
    let Some(elem_width) = vars
        .get(base_idx + 3)
        .and_then(|(_, s)| s.array_sort())
        .and_then(|arr| ChcCtx::sort_byte_width(&arr.element_sort))
        .filter(|w| *w > 0)
    else {
        return;
    };

    let count64 = coerce_bitvec_width_safe(count_expr, POINTER_WIDTH, SignExtension::ZeroExtend);
    let size_expr = Expr::bitvec_const(pointee_size as u128, POINTER_WIDTH);
    let no_mul_overflow = count64.clone().bvmul_no_overflow_unsigned(size_expr.clone());
    let span64 = count64.bvmul(size_expr);

    let cap = Expr::var(&*cap_name, cap_sort);
    let cap64 = coerce_bitvec_width_safe(cap, POINTER_WIDTH, SignExtension::ZeroExtend);
    // cap_bytes wrapping can only make the bound STRICTER (fail-closed);
    // model caps are seeded from real lengths and never approach 2^64.
    let cap_bytes = cap64.bvmul(Expr::bitvec_const(elem_width as u128, POINTER_WIDTH));
    let room = span64.bvule(cap_bytes);

    for check in [no_mul_overflow, room] {
        ctx.emit_intrinsic_span_ub_check(dcx.from_app, check, dcx.stmt_constraints, target);
    }
    debug!(
        vec_local,
        pointee_size, elem_width, "CHC: write_bytes projected-Vec room checks (P4-2)"
    );
}

/// P4-2: precise `write_bytes` prefix fill over a projected Vec's logical
/// data array.
///
/// For `write_bytes(vec.as_mut_ptr(), 0xfe, 2)` on `Vec<u32>`, constrains the
/// data-array output state variable to
/// `store(store(data, 0, 0xfefefefe), 1, 0xfefefefe)` — elements past the
/// count keep their previous values via store-chain semantics. `fld_data`
/// uses LOGICAL element indices (0, 1, ...), and `as_mut_ptr()` points at
/// logical element 0, so byte offset k*elem_width is logical index k.
///
/// Returns `false` (caller falls back to the existing marked over-approx
/// path) when: the referent is not a projected Vec, the byte span is not a
/// whole number of elements, the replicated element value is not encodable,
/// or the count exceeds `MAX_VEC_PREFIX_FILL_ELEMS`.
///
/// The requested span's in-bounds obligations are emitted by the caller
/// (`heap_span_access_checks` / referent span bound) independent of this
/// value model.
fn try_write_bytes_vec_prefix(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    target: BasicBlockIdx,
    referent_local: usize,
    byte_val: u8,
    count: u64,
) -> bool {
    use crate::codegen_ay::chc::codegen_ctx::types::CollectionProjectionKind;

    if ctx.collections.projection_locals.get(&referent_local).copied()
        != Some(CollectionProjectionKind::Vec)
    {
        return false;
    }
    let Some(pointee_ty) = operand_pointee_ty(&dcx.args[0], ctx) else {
        return false;
    };
    let Some(pointee_size) = pointee_ty.layout().ok().map(|l| l.shape().size.bytes()) else {
        return false;
    };
    if pointee_size == 0 {
        return false;
    }
    let Some(total_write) = usize::try_from(count).ok().and_then(|c| c.checked_mul(pointee_size))
    else {
        return false;
    };
    if total_write == 0 {
        // Zero-length fill: no memory effect; identity transition.
        let dest_local: usize = dcx.destination.local;
        let out = ctx.build_output_args(dcx.modified_locals, &[dest_local]);
        ctx.emit_goto_rule(dcx.from_app, target, &out, dcx.stmt_constraints);
        return true;
    }

    // Projected Vec layout: base+0 ptr, base+1 len, base+2 cap, base+3 data.
    let Some(base_idx) = ctx.try_state_idx_for_local(referent_local) else {
        return false;
    };
    let data_idx = base_idx + 3;
    // Already-modified referent: the current data value lives in the OUTPUT
    // var, and constraining `data_out = store(data_out, ...)` would be
    // circular (an infeasibility factory). Refuse — the caller's marked
    // over-approximation is the sound fallback.
    if dcx.modified_locals.contains(&referent_local) {
        return false;
    }
    let Some((in_name, in_sort)) = ctx.state_var_mgr.state_vars.get(data_idx).cloned() else {
        return false;
    };
    let Some(arr) = in_sort.array_sort() else {
        return false;
    };
    let Some(elem_width) = ChcCtx::sort_byte_width(&arr.element_sort) else {
        return false;
    };
    if elem_width == 0 || total_write % elem_width != 0 {
        return false;
    }
    let elem_count = total_write / elem_width;
    if elem_count > MAX_VEC_PREFIX_FILL_ELEMS {
        return false;
    }
    let fill_bytes = vec![Some(byte_val); elem_width];
    let Some(fill_elem) = ChcCtx::read_composite_from_bytes(&fill_bytes, 0, &arr.element_sort)
    else {
        return false;
    };
    let idx_width =
        arr.index_sort.bitvec_width().unwrap_or(crate::codegen_ay::types::POINTER_WIDTH);

    let mut updated = Expr::var(&*in_name, in_sort.clone());
    for idx in 0..elem_count {
        updated = updated.store(Expr::bitvec_const(idx as u128, idx_width), fill_elem.clone());
    }

    let Some((out_name, out_sort)) = ctx.state_var_mgr.output_state_vars.get(data_idx).cloned()
    else {
        return false;
    };
    let data_out = Expr::var(&*out_name, out_sort);
    let store_eq = data_out.eq(updated);
    ctx.mark_state_var_modified(data_idx);

    let dest_local: usize = dcx.destination.local;
    let out = ctx.build_output_args(dcx.modified_locals, &[dest_local]);
    ctx.emit_goto_rule_extra(dcx.from_app, target, &out, dcx.stmt_constraints, [store_eq]);
    debug!(
        referent_local,
        elem_count, byte_val, "CHC: write_bytes projected-Vec prefix fill encoded (P4-2)"
    );
    true
}

/// Build a precise prefix update for fixed-size array locals.
///
/// This covers calls like `write_bytes(arr.as_mut_ptr(), 0xfe, 2)` where the
/// destination points at the first array element and the byte count writes a
/// whole number of elements. Untouched elements are preserved by building a
/// store chain over the current array expression.
fn partial_prefix_fill_expr(
    ctx: &ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    referent_local: usize,
    total_write: usize,
    byte_val: u8,
) -> Option<Expr> {
    let current = ctx.local_expr_with_modified(referent_local, dcx.modified_locals)?;
    let arr = current.sort().array_sort()?;
    let elem_width = ChcCtx::sort_byte_width(&arr.element_sort)?;
    if elem_width == 0 || total_write == 0 || total_write % elem_width != 0 {
        return None;
    }

    let elem_count = total_write / elem_width;
    let fill_bytes = vec![Some(byte_val); elem_width];
    let fill_elem = ChcCtx::read_composite_from_bytes(&fill_bytes, 0, &arr.element_sort)?;
    let idx_width =
        arr.index_sort.bitvec_width().unwrap_or(crate::codegen_ay::types::POINTER_WIDTH);

    let mut updated = current;
    for idx in 0..elem_count {
        updated = updated.store(Expr::bitvec_const(idx as u128, idx_width), fill_elem.clone());
    }
    Some(updated)
}

/// Emit a write_bytes fill constraint for a resolved referent.
fn emit_write_bytes_fill(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    target: BasicBlockIdx,
    referent_local: usize,
    fill_expr: Expr,
) -> bool {
    let dest_local: usize = dcx.destination.local;
    let out = ctx.build_output_args(dcx.modified_locals, &[dest_local, referent_local]);

    if let Some(flat_constraints) =
        ctx.build_flattened_destination_constraints(referent_local, fill_expr.clone())
    {
        if flat_constraints.is_empty() {
            ctx.emit_goto_rule(dcx.from_app, target, &out, dcx.stmt_constraints);
        } else {
            ctx.emit_goto_rule_extra(
                dcx.from_app,
                target,
                &out,
                dcx.stmt_constraints,
                flat_constraints,
            );
        }
        debug!(
            referent_local,
            "CHC: write_bytes fill encoded via flattened destination constraints (Part of #3702, #3798)"
        );
        return true;
    }

    if let Some((_, referent_var)) = ctx.resolve_destination(referent_local) {
        let ref_sort = referent_var.sort().clone();
        let mut extra = Vec::new();
        if let Some(eq) = ctx.make_coerced_eq_constraint(
            &referent_var,
            fill_expr,
            &ref_sort,
            referent_local,
            "write_bytes_fill",
        ) {
            extra.push(eq);
        }
        if extra.is_empty() {
            ctx.emit_goto_rule(dcx.from_app, target, &out, dcx.stmt_constraints);
        } else {
            ctx.emit_goto_rule_extra(dcx.from_app, target, &out, dcx.stmt_constraints, extra);
        }
    } else {
        ctx.emit_goto_rule(dcx.from_app, target, &out, dcx.stmt_constraints);
    }
    debug!(referent_local, "CHC: write_bytes fill encoded precisely (Part of #3702, #3798)");
    true
}

/// Build a typed fresh value for a fully-overwritten local.
fn fresh_expr_for_local(ctx: &mut ChcCtx<'_, '_>, referent_local: usize) -> Option<Expr> {
    let sort = if let Some((_, referent_var)) = ctx.resolve_destination(referent_local) {
        referent_var.sort().clone()
    } else {
        let referent_ty = ctx.body.locals().get(referent_local)?.ty;
        ChcCtx::translate_ty(referent_ty)?
    };
    Some(declare_pending_var(chc_fresh_name("__write_bytes_full"), sort))
}

fn referent_byte_width(
    ctx: &mut ChcCtx<'_, '_>,
    referent_local: usize,
    referent_ty: rustc_public::ty::Ty,
) -> Option<usize> {
    // P4-2/P4-3: layout size FIRST. The destination sort's byte width ignores
    // alignment padding (e.g. `struct { u8, u32 }` sums to 5, layout is 8), so
    // a whole-value `write_bytes` — `mem::zeroed::<T>()` writes
    // `size_of::<T>()` bytes — failed the span bound `span <= referent_size`
    // against the padding-free width: a spurious memory-safety FAILURE. The
    // allocation extent is the LAYOUT size; the sort width stays as a
    // fallback for locals without a computable layout.
    if let Some(byte_width) = LayoutOf::new(referent_ty).size_of() {
        return Some(byte_width);
    }
    ctx.resolve_destination(referent_local)
        .and_then(|(_, referent_var)| ChcCtx::sort_byte_width(referent_var.sort()))
}

/// Build a typed zero expression for the given Rust type.
///
/// Uses the existing type translation and constant decoding infrastructure
/// rather than hand-building struct zero values field by field.
pub(in crate::codegen_ay::chc) fn zero_expr_for_ty(ty: rustc_public::ty::Ty) -> Option<Expr> {
    let sort = ChcCtx::translate_ty(ty)?;

    // Scalar sorts: direct zero construction.
    if sort.is_bool() {
        return Some(Expr::bool_const(false));
    }
    if let Some(width) = sort.bitvec_width() {
        return Some(Expr::bitvec_const(0u128, width));
    }
    if sort.is_int() {
        return Some(Expr::int_const(0));
    }

    // Composite sorts: compute byte width and decode from zero bytes.
    let byte_width = ChcCtx::sort_byte_width(&sort)?;
    if byte_width == 0 {
        return None;
    }
    let zero_bytes: Vec<Option<u8>> = vec![Some(0u8); byte_width];
    ChcCtx::read_composite_from_bytes(&zero_bytes, 0, &sort)
}

/// Extract a constant u8 value from an operand.
///
/// Part of #3949: `eval_target_usize()` panics on non-usize-width constants
/// (e.g. u8 → "expected int of size 8, but got size 1"). Use the translate
/// fallback path (`const_u8_from_expr`) instead of calling `eval_target_usize`
/// on a u8.
fn extract_const_u8(operand: &Operand) -> Option<u8> {
    let Operand::Constant(c) = operand else {
        return None;
    };
    match c.ty().kind() {
        TyKind::RigidTy(RigidTy::Uint(rustc_public::ty::UintTy::U8)) => {}
        _ => return None,
    }
    // Try usize eval only for usize-width constants; for u8 this would ICE.
    // The caller's .or_else path handles u8 via translate_operand → const_u8_from_expr.
    None
}

fn const_u8_from_expr(expr: Expr) -> Option<u8> {
    match expr.value() {
        ay_bindings::ExprValue::BitVecConst { value, .. } => {
            u64::try_from(value).ok()?.try_into().ok()
        }
        ay_bindings::ExprValue::IntConst(value) => u64::try_from(value).ok()?.try_into().ok(),
        _ => None,
    }
}

/// Build a fill expression for a type with repeated byte value.
///
/// For BV types, produces a bitvec constant by repeating the byte.
/// For composite types, uses the byte-decoding infrastructure.
/// Returns None for types where fill construction isn't supported.
fn fill_expr_for_ty(ty: rustc_public::ty::Ty, byte_val: u8) -> Option<Expr> {
    let sort = ChcCtx::translate_ty(ty)?;

    if let Some(width) = sort.bitvec_width() {
        let byte_count = width.div_ceil(8);
        let mut val: u128 = 0;
        for _ in 0..byte_count {
            val = (val << 8) | (byte_val as u128);
        }
        return Some(Expr::bitvec_const(val, width));
    }

    // Composite sorts: fill with repeated byte.
    let byte_width = ChcCtx::sort_byte_width(&sort)?;
    if byte_width == 0 {
        return None;
    }
    let fill_bytes: Vec<Option<u8>> = vec![Some(byte_val); byte_width];
    ChcCtx::read_composite_from_bytes(&fill_bytes, 0, &sort)
}

/// Extract a concrete usize value from a constant operand.
fn extract_operand_const_usize(operand: &Operand) -> Option<u64> {
    if let Operand::Constant(const_op) = operand {
        const_op.const_.eval_target_usize().ok()
    } else {
        None
    }
}

/// Extract the pointee type from a pointer operand.
fn operand_pointee_ty(operand: &Operand, ctx: &ChcCtx<'_, '_>) -> Option<rustc_public::ty::Ty> {
    let ty = match operand {
        Operand::Copy(place) | Operand::Move(place) => {
            ctx.body.locals().get(place.local).map(|l| l.ty)?
        }
        Operand::Constant(c) => c.ty(),
    };
    match ty.kind() {
        TyKind::RigidTy(RigidTy::RawPtr(pointee_ty, _)) => Some(pointee_ty),
        _ => None,
    }
}
