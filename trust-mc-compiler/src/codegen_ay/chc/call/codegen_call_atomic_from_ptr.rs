// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! `AtomicT::from_ptr` handler for CHC encoding.
//!
//! `from_ptr` is a transparent alias boundary: semantically `unsafe { &*ptr.cast() }`.
//! The destination `&AtomicT` points to the same memory as the input raw pointer.
//! Models this as pointer identity plus alias metadata forwarding, following
//! the same pattern as `UnsafeCell::get` (codegen_call_unsafe_cell.rs).
//!
//! Split from codegen_call_atomic.rs per file size limit.
//! Part of #3598.

use rustc_public::mir::{BasicBlockIdx, Operand};
use tracing::debug;

use super::ChcCtx;
use super::chc_call_context::DispatchCallContext;
use super::codegen_call_coerce::{CallCoerce, emit_sound_fallback_goto};
use super::codegen_rules::CodegenRules;

/// `AtomicUsize::from_ptr(ptr)` / `AtomicBool::from_ptr(ptr)` / etc.
///
/// Two-part model:
/// 1. Forward ref_targets from the raw pointer input to dest ONLY when the
///    input already has stack-local ref_targets (fast path). For heap-backed
///    pointers (e.g., `Box::into_raw(Box::new(...))`), skip ref_target
///    insertion so that downstream store/load/swap handlers fall through to
///    the Mem-level path, which correctly accesses heap memory arrays.
///    Part of #3710: setting ref_targets to the Box's owning local caused
///    store/load to constrain the Box pointer value instead of the pointed-to
///    memory, producing CTREX(OverApproximation).
/// 2. Constrain dest = input pointer (pointer value identity) for the CHC rule.
///
/// Part of #3598: CHC misses AtomicUsize::from_ptr alias boundary.
/// Part of #3710: heap-backed from_ptr must use Mem-level, not ref_target.
pub(in crate::codegen_ay::chc) fn codegen_atomic_from_ptr(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    target: BasicBlockIdx,
) {
    let dest_local: usize = dcx.destination.local;

    if dcx.args.is_empty() {
        emit_sound_fallback_goto(
            ctx,
            dcx.from_app,
            target,
            dcx.modified_locals,
            &[dest_local],
            dcx.stmt_constraints,
        );
        return;
    }

    // Forward ref_targets only from the fast path: when the input argument
    // already has stack-local ref_targets. Skip the heap-derived obj_id path
    // (#3710) — heap-backed atomics must use Mem-level operations so that
    // store/load/swap access the correct memory array instead of trying to
    // constrain the Box pointer variable directly.
    if let Operand::Copy(place) | Operand::Move(place) = &dcx.args[0] {
        let arg_local: usize = place.local;
        if place.projection.is_empty() {
            if let Some(ref_target) = ctx.ref_resolution.ref_targets.get(&arg_local).cloned() {
                // Fast path: input already has stack-local ref_targets.
                debug!(
                    arg_local,
                    dest_local,
                    referent = ref_target.local,
                    "atomic_from_ptr: forwarded existing ref_target"
                );
                ctx.ref_resolution.ref_targets.insert(dest_local, ref_target);
                ctx.ref_resolution.call_forwarded_raw_ptrs.insert(dest_local);
            }
            // Primary path (heap-derived obj_id) intentionally omitted (#3710).
            // Heap-backed atomics rely on Mem-level store/load in the atomic
            // handlers, which correctly key into the type array system.
        }
    }

    // Skip const_ref_values seeding (#3710): for heap-backed pointers, the
    // resolved value is the pointer ADDRESS (BV64), not the stored VALUE.
    // On 64-bit platforms both have the same sort, so atomic_load would
    // incorrectly use the address as the loaded value.

    // Constrain dest pointer = input pointer (pointer identity).
    let ptr_expr = ctx
        .translate_operand_with_modified(&dcx.args[0], dcx.modified_locals)
        .or_else(|| ctx.resolve_ref_operand(&dcx.args[0], dcx.modified_locals));
    if let Some(ptr_expr) = ptr_expr
        && let Some((_, dest_var)) = ctx.resolve_destination(dest_local)
    {
        if let Some(eq) = ctx.make_coerced_eq_constraint(
            &dest_var,
            ptr_expr,
            dest_var.sort(),
            dest_local,
            "atomic_from_ptr",
        ) {
            let out = ctx.build_output_args(dcx.modified_locals, &[dest_local]);
            ctx.emit_goto_rule_extra(dcx.from_app, target, &out, dcx.stmt_constraints, [eq]);
        } else {
            emit_sound_fallback_goto(
                ctx,
                dcx.from_app,
                target,
                dcx.modified_locals,
                &[dest_local],
                dcx.stmt_constraints,
            );
        }
        debug!(dest_local, "atomic_from_ptr: modeled as pointer identity alias (bb{})", dcx.bb_idx);
    } else {
        emit_sound_fallback_goto(
            ctx,
            dcx.from_app,
            target,
            dcx.modified_locals,
            &[dest_local],
            dcx.stmt_constraints,
        );
    }
}
