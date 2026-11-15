// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Inline handling for atomic operations (fetch_add, load, store) inside
//! inlined bodies.
//!
//! Part of #4023: When a Drop impl calls `AtomicUsize::fetch_add()` (e.g.,
//! for drop counting), the inline walker must handle the atomic operation
//! through the memory model rather than falling back to a fresh symbolic
//! variable. Without this, the atomic counter is never updated and assertions
//! on the counter fail with CTREX(Genuine).

use ay_bindings::Expr;
use rustc_public::CrateDef;
use rustc_public::mir::LocalDecl;
use rustc_public::mir::Operand;
use rustc_public::mir::mono::Instance;
use rustc_public::rustc_internal;
use rustc_public::ty::{RigidTy, TyKind};
use std::collections::HashMap;
use tracing::debug;

use super::super::ChcCtx;
use super::super::codegen_call_atomic::{AtomicKind, atomic_scalar, detect_atomic_intrinsic};
use super::super::codegen_call_atomic_rmw::compute_rmw_value;
use super::super::codegen_types::CodegenTypes;
use super::super::inline_shared::{PlaceResolver, inline_operand_to_expr};
use super::super::ptr_receiver_mem;
use crate::codegen_ay::provenance::MaybeLoc;

/// Handle atomic operations (fetch_add, load, store, etc.) inside an inlined
/// function body.
///
/// Returns `Some(result_expr)` if handled, None if not an atomic operation.
///
/// Part of #4023: enables Drop impls that use AtomicUsize for side-effect
/// counting to be properly modeled in the CHC memory model.
pub(super) fn try_handle_atomic_call_inline<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    func: &Operand,
    args: &[Operand],
    locals: &[LocalDecl],
    local_exprs: &HashMap<usize, Expr>,
    resolver: &PlaceResolver<'_>,
) -> Option<Expr> {
    // 1. Resolve callee path.
    let func_ty = func.ty(locals).ok()?;
    let func_ty = ctx.resolve_body_ty(func_ty);
    let (fn_def, fn_args) = match func_ty.kind() {
        TyKind::RigidTy(RigidTy::FnDef(def, args)) => (def, args),
        _ => return None,
    };
    let instance = Instance::resolve(fn_def, &fn_args).ok()?;
    let def_id = instance.def.def_id();
    let internal_def_id = rustc_internal::internal(ctx.tcx, def_id);
    let callee_path = ctx.tcx.def_path_str(internal_def_id);
    if callee_path.contains("atomic") {
        tracing::warn!(
            callee = %callee_path,
            "atomic_inline: entry — callee path resolved (#4023)"
        );
    }

    // 2. Detect atomic operation kind.
    let kind = detect_atomic_intrinsic(&callee_path);
    if kind.is_none() && callee_path.contains("atomic") {
        tracing::warn!(
            callee = %callee_path,
            "atomic_inline: callee contains 'atomic' but detect_atomic_intrinsic returned None"
        );
    }
    let kind = kind?;

    // 3. Translate args in inline context, by position: an argument that does
    // not translate must not shift the ones after it into its place (the
    // ordering argument read as the operand).
    let translated_args: Vec<Option<Expr>> = args
        .iter()
        .map(|arg| inline_operand_to_expr(ctx, arg, local_exprs, resolver, locals))
        .collect();
    let arg = |i: usize| translated_args.get(i).cloned().flatten();
    let n_translated = translated_args.iter().flatten().count();

    // Need at least the receiver (&self) for all atomic ops.
    if n_translated == 0 {
        return None;
    }
    let receiver_addr = &arg(0)?;

    // The memory cell is keyed by what the receiver POINTS AT (`&Atomic<u32>`
    // is a cell of `Atomic<u32>`, `atomic_xadd`'s `*mut u32` one of `u32`):
    // every other access of the atomic (its `load`, a static's seeding) reads
    // that key, and a write under the scalar's key instead was lost
    // (`field_type_static_generic_dual.rs::bug_generic_static` was proved).
    // The cell holds the scalar the signature names (`atomic_value_ty`,
    // never the callee's name); a cell whose element sort is not that
    // scalar's is refused rather than written with a mismatched value.
    let value_ty = atomic_value_ty(&kind, func_ty)?;
    let pointee_ty = atomic_cell_ty(func_ty).unwrap_or(value_ty);
    let value_sort = ChcCtx::translate_ty(value_ty);
    if matches!(kind, AtomicKind::Load | AtomicKind::Store) || is_atomic_rmw(&kind) {
        let value_sort = value_sort.clone()?;
        if ctx.elem_sort_for_memory_array(pointee_ty) != value_sort {
            debug!(
                ?kind,
                ?pointee_ty,
                ?value_ty,
                "atomic_inline: cell sort is not the value's — refused"
            );
            return None;
        }
    }

    debug!(
        ?kind,
        callee = %callee_path,
        n_args = translated_args.len(),
        "atomic_inline: handling atomic call inside inlined body (#4023)"
    );

    match kind {
        AtomicKind::Load => {
            // Load: read from memory at receiver address. The cell is keyed by
            // the atomic, whose load may come back as the atomic's datatype
            // (`Atomic_usize { v: .. }`); the operation returns its scalar.
            let loaded = ptr_receiver_mem::load_from_memory(
                ctx,
                &MaybeLoc::Unknown(receiver_addr.clone()),
                pointee_ty,
            )?
            .into_expr();
            let loaded = atomic_scalar(loaded);
            if Some(loaded.sort()) != value_sort.as_ref() {
                debug!(
                    ?pointee_ty,
                    ?value_ty,
                    "atomic_inline: loaded sort is not the value's — refused"
                );
                return None;
            }
            Some(loaded)
        }

        AtomicKind::Store => {
            // Store: write value to memory at receiver address.
            let value = arg(1)?;
            if Some(value.sort()) != value_sort.as_ref() {
                debug!(?value_ty, "atomic_inline: stored value's sort is not the cell's — refused");
                return None;
            }
            // A static the store may write is havocked, and the stored value's
            // own views written back (`static_store_from_inlined_body`).
            ctx.with_static_store_routing(|ctx| {
                ctx.build_memory_store_untyped(receiver_addr.clone(), value.clone(), pointee_ty);
                ctx.static_store_from_inlined_body(receiver_addr, pointee_ty, &value);
            });
            // Store returns () — produce a dummy value.
            Some(Expr::bitvec_const(0u64, crate::codegen_ay::types::POINTER_WIDTH))
        }

        AtomicKind::FetchAdd
        | AtomicKind::FetchSub
        | AtomicKind::FetchAnd
        | AtomicKind::FetchOr
        | AtomicKind::FetchXor
        | AtomicKind::FetchNand
        | AtomicKind::FetchMax
        | AtomicKind::FetchMin
        | AtomicKind::FetchUmax
        | AtomicKind::FetchUmin
        | AtomicKind::Exchange => {
            // RMW: load old, compute new, store new, return old. The operand
            // and the loaded cell must both have the value's sort: a cell the
            // memory model reads back under another sort is refused, never
            // combined with the operand (`bvadd requires same BitVec sorts`).
            let operand = arg(1)?;
            // A translated call argument: `translate_operand` reports nothing about
            // what it produced, so the ignorance is stated, not papered over.
            let old_value = atomic_scalar(
                ptr_receiver_mem::load_from_memory(
                    ctx,
                    &MaybeLoc::Unknown(receiver_addr.clone()),
                    pointee_ty,
                )?
                .into_expr(),
            );
            let value_sort = value_sort.as_ref();
            if Some(old_value.sort()) != value_sort || Some(operand.sort()) != value_sort {
                debug!(
                    ?kind,
                    ?pointee_ty,
                    old_sort = ?old_value.sort(),
                    operand_sort = ?operand.sort(),
                    ?value_sort,
                    "atomic_inline: RMW sorts disagree — refused"
                );
                return None;
            }

            let new_value = if matches!(kind, AtomicKind::Exchange) {
                operand
            } else {
                compute_rmw_value(&kind, old_value.clone(), operand)
            };

            ctx.with_static_store_routing(|ctx| {
                ctx.build_memory_store_untyped(
                    receiver_addr.clone(),
                    new_value.clone(),
                    pointee_ty,
                );
                ctx.static_store_from_inlined_body(receiver_addr, pointee_ty, &new_value);
            });
            debug!(?kind, "atomic_inline: RMW completed, old_value returned (#4023)");
            Some(old_value)
        }

        AtomicKind::New => {
            // AtomicT::new(val) — store initial value.
            if n_translated < 2 {
                return None;
            }
            // For `new`, args[0] is the value, not a receiver.
            // AtomicUsize::new(val) is a constructor — returns the AtomicUsize.
            // In inline context, this is typically handled by the assignment
            // to the destination local. The constructor just wraps the value.
            arg(0)
        }

        AtomicKind::Fence => {
            // Fence is a no-op for verification purposes.
            Some(Expr::bitvec_const(0u64, crate::codegen_ay::types::POINTER_WIDTH))
        }

        AtomicKind::GetMut => {
            // get_mut(&mut self) — identity passthrough (Part of #4067).
            // In inline context, return the receiver address/value as-is.
            Some(receiver_addr.clone())
        }

        AtomicKind::Cxchg | AtomicKind::CompareExchange | AtomicKind::FromPtr => {
            // Complex atomics not yet supported in inline context.
            None
        }
    }
}

/// The receiver's pointee: the atomic cell the operation reads and writes.
fn atomic_cell_ty(func_ty: rustc_public::ty::Ty) -> Option<rustc_public::ty::Ty> {
    let sig = func_ty.kind().fn_sig()?.skip_binder();
    match sig.inputs().first()?.kind() {
        TyKind::RigidTy(RigidTy::Ref(_, pointee, _) | RigidTy::RawPtr(pointee, _)) => Some(pointee),
        _ => None,
    }
}

fn is_atomic_rmw(kind: &AtomicKind) -> bool {
    matches!(
        kind,
        AtomicKind::FetchAdd
            | AtomicKind::FetchSub
            | AtomicKind::FetchAnd
            | AtomicKind::FetchOr
            | AtomicKind::FetchXor
            | AtomicKind::FetchNand
            | AtomicKind::FetchMax
            | AtomicKind::FetchMin
            | AtomicKind::FetchUmax
            | AtomicKind::FetchUmin
            | AtomicKind::Exchange
    )
}

/// The value type an atomic operation reads or writes, from the callee's
/// signature: a load returns it, a store or read-modify-write takes it as its
/// second argument (`AtomicU32::fetch_add(&self, val: u32, ..)`,
/// `atomic_xadd::<u32>(dst: *mut u32, src: u32)`). A `bool` is stored as a
/// byte. `None` when the signature does not say (the walk then gives up on the
/// call, and Rule D books it).
///
/// This read the callee's NAME before (`contains("AtomicU32")`, falling back to
/// `usize`), and the Trust standard library names every atomic method
/// `Atomic::<T>::..`: a `u32` receiver was loaded as a `usize` and added to a
/// `u32` operand (`bvadd requires same BitVec sorts`,
/// `field_type_static_generic_dual.rs::safe_generic_static`).
fn atomic_value_ty(
    kind: &AtomicKind,
    func_ty: rustc_public::ty::Ty,
) -> Option<rustc_public::ty::Ty> {
    use rustc_public::ty::UintTy;
    let sig = func_ty.kind().fn_sig()?.skip_binder();
    let value_ty = match kind {
        AtomicKind::Load => sig.output(),
        AtomicKind::Store
        | AtomicKind::FetchAdd
        | AtomicKind::FetchSub
        | AtomicKind::FetchAnd
        | AtomicKind::FetchOr
        | AtomicKind::FetchXor
        | AtomicKind::FetchNand
        | AtomicKind::FetchMax
        | AtomicKind::FetchMin
        | AtomicKind::FetchUmax
        | AtomicKind::FetchUmin
        | AtomicKind::Exchange => *sig.inputs().get(1)?,
        // `new`, fences, `get_mut` and the compare-exchanges read no value
        // through the receiver here; their arms do not use this type.
        _ => return Some(rustc_public::ty::Ty::unsigned_ty(UintTy::Usize)),
    };
    match value_ty.kind() {
        TyKind::RigidTy(RigidTy::Bool) => Some(rustc_public::ty::Ty::unsigned_ty(UintTy::U8)),
        TyKind::RigidTy(RigidTy::Int(_) | RigidTy::Uint(_) | RigidTy::RawPtr(..)) => Some(value_ty),
        _ => None,
    }
}
