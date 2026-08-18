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
use super::super::codegen_call_atomic::{AtomicKind, detect_atomic_intrinsic};
use super::super::codegen_call_atomic_rmw::compute_rmw_value;
use super::super::inline_shared::{PlaceResolver, inline_operand_to_expr};
use super::super::ptr_receiver_mem;
use crate::codegen_ay::provenance::{MaybeLoc, Val};

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

    // 3. Translate args in inline context.
    let translated_args: Vec<Expr> = args
        .iter()
        .filter_map(|arg| inline_operand_to_expr(ctx, arg, local_exprs, resolver, locals))
        .collect();

    // Need at least the receiver (&self) for all atomic ops.
    if translated_args.is_empty() {
        return None;
    }
    let receiver_addr = &translated_args[0];

    // Resolve pointee type: AtomicUsize → usize, AtomicBool → bool, etc.
    let pointee_ty = resolve_atomic_pointee_ty(&callee_path, &fn_args)?;

    debug!(
        ?kind,
        callee = %callee_path,
        n_args = translated_args.len(),
        "atomic_inline: handling atomic call inside inlined body (#4023)"
    );

    match kind {
        AtomicKind::Load => {
            // Load: read from memory at receiver address.
            ptr_receiver_mem::load_from_memory(
                ctx,
                &MaybeLoc::Unknown(receiver_addr.clone()),
                pointee_ty,
            )
            .map(Val::into_expr)
        }

        AtomicKind::Store => {
            // Store: write value to memory at receiver address.
            if translated_args.len() < 2 {
                return None;
            }
            let value = translated_args[1].clone();
            ctx.build_memory_store_untyped(receiver_addr.clone(), value, pointee_ty);
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
            // RMW: load old, compute new, store new, return old.
            if !matches!(kind, AtomicKind::Exchange) && translated_args.len() < 2 {
                return None;
            }
            // A translated call argument: `translate_operand` reports nothing about
            // what it produced, so the ignorance is stated, not papered over.
            let old_value = ptr_receiver_mem::load_from_memory(
                ctx,
                &MaybeLoc::Unknown(receiver_addr.clone()),
                pointee_ty,
            )?
            .into_expr();

            let new_value = if matches!(kind, AtomicKind::Exchange) {
                if translated_args.len() < 2 {
                    return None;
                }
                translated_args[1].clone()
            } else {
                let operand = translated_args[1].clone();
                compute_rmw_value(&kind, old_value.clone(), operand)
            };

            ctx.build_memory_store_untyped(receiver_addr.clone(), new_value, pointee_ty);
            debug!(?kind, "atomic_inline: RMW completed, old_value returned (#4023)");
            Some(old_value)
        }

        AtomicKind::New => {
            // AtomicT::new(val) — store initial value.
            if translated_args.len() < 2 {
                return None;
            }
            // For `new`, args[0] is the value, not a receiver.
            // AtomicUsize::new(val) is a constructor — returns the AtomicUsize.
            // In inline context, this is typically handled by the assignment
            // to the destination local. The constructor just wraps the value.
            Some(translated_args[0].clone())
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

/// Resolve the pointee type for an atomic operation.
///
/// Atomic types wrap `UnsafeCell<T>` where T is the value type.
/// We extract T from the callee path pattern (e.g., `AtomicUsize` → `usize`).
fn resolve_atomic_pointee_ty(
    callee_path: &str,
    _fn_args: &rustc_public::ty::GenericArgs,
) -> Option<rustc_public::ty::Ty> {
    use rustc_public::ty::{IntTy, UintTy};

    // Match stable API paths like `core::sync::atomic::AtomicUsize::fetch_add`
    // or intrinsic paths like `core::intrinsics::atomic_xadd`.
    if callee_path.contains("AtomicUsize") || callee_path.contains("atomic_usize") {
        Some(rustc_public::ty::Ty::unsigned_ty(UintTy::Usize))
    } else if callee_path.contains("AtomicIsize") || callee_path.contains("atomic_isize") {
        Some(rustc_public::ty::Ty::signed_ty(IntTy::Isize))
    } else if callee_path.contains("AtomicU8") || callee_path.contains("atomic_u8") {
        Some(rustc_public::ty::Ty::unsigned_ty(UintTy::U8))
    } else if callee_path.contains("AtomicU16") || callee_path.contains("atomic_u16") {
        Some(rustc_public::ty::Ty::unsigned_ty(UintTy::U16))
    } else if callee_path.contains("AtomicU32") || callee_path.contains("atomic_u32") {
        Some(rustc_public::ty::Ty::unsigned_ty(UintTy::U32))
    } else if callee_path.contains("AtomicU64") || callee_path.contains("atomic_u64") {
        Some(rustc_public::ty::Ty::unsigned_ty(UintTy::U64))
    } else if callee_path.contains("AtomicI8") || callee_path.contains("atomic_i8") {
        Some(rustc_public::ty::Ty::signed_ty(IntTy::I8))
    } else if callee_path.contains("AtomicI16") || callee_path.contains("atomic_i16") {
        Some(rustc_public::ty::Ty::signed_ty(IntTy::I16))
    } else if callee_path.contains("AtomicI32") || callee_path.contains("atomic_i32") {
        Some(rustc_public::ty::Ty::signed_ty(IntTy::I32))
    } else if callee_path.contains("AtomicI64") || callee_path.contains("atomic_i64") {
        Some(rustc_public::ty::Ty::signed_ty(IntTy::I64))
    } else if callee_path.contains("AtomicBool") || callee_path.contains("atomic_bool") {
        // AtomicBool stores as u8 internally.
        Some(rustc_public::ty::Ty::unsigned_ty(UintTy::U8))
    } else {
        // Fallback: try usize for unrecognized atomic intrinsic paths.
        // Many raw intrinsics like `atomic_xadd_seqcst` don't contain the
        // type name — the type is inferred from the generic parameter.
        Some(rustc_public::ty::Ty::unsigned_ty(UintTy::Usize))
    }
}
