// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! MIR analysis helpers for inline drop translation.
//! Extracted from inline_drop.rs per #4206.

use ay_bindings::Expr;
use std::collections::HashMap;

use super::super::ChcCtx;
use super::walker::InlineWalkCtx;
use crate::codegen_ay::provenance::{
    Loc, Val, is_value_widened_into_address, mir_ty_denotes_address,
};
use crate::codegen_ay::ptr_repr::PtrSlot;
use crate::codegen_ay::types::POINTER_WIDTH;

pub(super) fn is_transparent_platform_drop(ty: rustc_public::ty::Ty) -> bool {
    use rustc_public::CrateDef;
    use rustc_public::ty::{RigidTy, TyKind};

    match ty.kind() {
        TyKind::RigidTy(RigidTy::Adt(def, args)) => {
            let full_name = def.0.name();
            // Direct platform sync types
            if full_name.contains("sys::sync::mutex")
                || full_name.contains("sys::pal::unix::sync")
                || full_name.contains("once_box::OnceBox")
                || full_name.contains("sync::poison::Flag")
                || full_name.contains("pthread_mutex_t")
            {
                return true;
            }
            // Transparent wrappers: Pin, Box, Option -- recurse into inner type
            let name = def.trimmed_name();
            if matches!(name.as_str(), "Pin" | "Box" | "Option") {
                if let Some(rustc_public::ty::GenericArgKind::Type(inner)) = args.0.first() {
                    return is_transparent_platform_drop(*inner);
                }
            }
            false
        }
        _ => false,
    }
}

/// Resolve the self parameter (address) for an inline Drop terminator.
///
/// Part of #3848: The drop body expects `&mut Self` (a pointer to the value
/// being dropped). Returns the memory address if derivable from the inline
/// context. Returns `None` if not -- caller uses fresh symbolic BV64.
pub(super) fn resolve_inline_drop_self_expr(
    ctx: &mut ChcCtx<'_, '_>,
    walk_ctx: &InlineWalkCtx<'_>,
    local_exprs: &HashMap<usize, Expr>,
    place: &rustc_public::mir::Place,
) -> Option<Expr> {
    use rustc_public::CrateDef;
    use rustc_public::mir::ProjectionElem;
    use rustc_public::ty::{GenericArgKind, RigidTy, TyKind};

    let proj = place.projection.as_slice();

    // Case 1: Deref-prefixed place (e.g., `(*_1).field`). The local holds
    // a pointer -- the pointee address is the base for the drop target.
    if matches!(proj.first(), Some(ProjectionElem::Deref)) {
        let root = local_exprs.get(&place.local)?;
        let base_addr = crate::codegen_ay::chc::dyn_coercion::extract_pointer_expr(root)
            .map(Loc::into_expr)
            .unwrap_or_else(|| root.clone());
        // GUARD KEPT (not a provenance guess): the fallback lane above is the
        // untyped root term of any sort, and the `bvadd` byte-offset walk below
        // needs a POINTER_WIDTH operand. `extract_pointer_expr`'s named
        // `fld_ptr` lane also returns whatever sort that field was DECLARED
        // with, so this is not vacuous on the extracted lane either.
        if base_addr.sort().bitvec_width() != Some(POINTER_WIDTH) {
            return None;
        }
        let remaining = &proj[1..];
        if remaining.is_empty() {
            return Some(base_addr);
        }
        let local_decl = walk_ctx.locals.get(place.local)?;
        let pointer_ty = ctx.resolve_body_ty(local_decl.ty);
        let mut current_ty = match pointer_ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(_, pointee, _))
            | TyKind::RigidTy(RigidTy::RawPtr(pointee, _)) => ctx.resolve_body_ty(pointee),
            TyKind::RigidTy(RigidTy::Adt(def, args))
                if crate::codegen_ay::shared::is_pointer_wrapper_adt(&def.trimmed_name()) =>
            {
                args.0.iter().find_map(|arg| match arg {
                    GenericArgKind::Type(pointee) => Some(ctx.resolve_body_ty(*pointee)),
                    _ => None,
                })?
            }
            _ => return None,
        };
        let mut addr = base_addr;
        for p in remaining {
            match p {
                ProjectionElem::Field(idx, field_ty) => {
                    let layout_ty = ctx.normalize_unique_dyn_tail_ty(current_ty);
                    let offset = ctx.get_field_offset(layout_ty, *idx)?;
                    if offset > 0 {
                        addr = addr.bvadd(Expr::bitvec_const(offset as i64, POINTER_WIDTH));
                    }
                    current_ty = ctx.resolve_body_ty(*field_ty);
                }
                _ => return None,
            }
        }
        return Some(addr);
    }

    // Case 2: Simple local -- either a BV64 address or a fat-pointer
    // Datatype (Box<dyn T>, &dyn T). For fat pointers, extract the
    // BV64 pointer component. Part of #3872.
    if proj.is_empty() {
        if let Some(val) = local_exprs.get(&place.local) {
            // Coroutine locals already carry a structured state value in CHC.
            // Passing that value through preserves discriminant-driven drop
            // glue instead of forcing the walker onto a fresh synthetic
            // pointer with no field content.
            if crate::codegen_ay::types::is_coroutine_root_sort(val.sort()) {
                return Some(val.clone());
            }
            // The width test that used to stand alone here is retired: it read
            // "this local's term is 64 bits wide" as "this local's term is the
            // drop target's ADDRESS", and handed the result to the drop body as
            // its `&mut Self` — i.e. straight onto the free/deref path. It is
            // not a provenance test. `translate_adt_ty` collapses a dozen
            // non-pointer ADTs (`Cow`, `Alignment`, `Drain`, every opaque
            // iterator adapter) to the same `ptr_sort()`, and a `usize` local
            // lands there too, so the guess fabricated an address out of an
            // opaque VALUE for exactly the types whose drop glue is non-trivial.
            //
            // Provenance now comes from the MIR type of the local, which states
            // the fact outright — see `mir_ty_denotes_address`. When it says no,
            // fall through: `resolve_inline_drop_self_expr` returning `None` is
            // the caller's supported lane (a fresh symbolic `__drop_self`, the
            // sound over-approximation already used for ZSTs), never a
            // fabricated address.
            let local_is_pointer = walk_ctx
                .locals
                .get(place.local)
                .map(|decl| ctx.resolve_body_ty(decl.ty))
                .is_some_and(mir_ty_denotes_address);
            // The pointer-width requirement survives as a REPRESENTATION check
            // only: a `&mut T` local can hold the pointee's own term under the
            // walker's transparent-Deref model, and that term is not addressable.
            if local_is_pointer
                && PtrSlot::of_sort(val.sort()) == Some(PtrSlot::Thin)
                && !is_value_widened_into_address(val)
            {
                return Some(val.clone());
            }
            // Part of #3872: Fat-pointer Datatype -- extract pointer component.
            if let Some(ptr) = crate::codegen_ay::chc::dyn_coercion::extract_pointer_expr(val) {
                // Same as above: this tests the DECLARED sort of the extracted
                // field, not whether the term is an address — so it asks the
                // one classification of a declared pointer slot, `PtrSlot`,
                // exactly as the `local_is_pointer` arm does. Provenance came
                // from `extract_pointer_expr`'s declared `fld_ptr` role.
                if PtrSlot::of_sort(ptr.as_expr().sort()) == Some(PtrSlot::Thin) {
                    return Some(ptr.into_expr());
                }
            }
            // Part of #3977: BV128 packed fat pointer (data:64 | vtable:64).
            // Extract lower POINTER_WIDTH bits as the data pointer.
            if let Some(w) = val.sort().bitvec_width() {
                if w == 2 * POINTER_WIDTH {
                    return Some(val.clone().extract(POINTER_WIDTH - 1, 0));
                }
            }
        }
    }

    None
}

/// Part of #4150: Coroutine drop glue is too complex for the inline walker.
pub(super) fn is_coroutine_drop(ty: rustc_public::ty::Ty) -> bool {
    matches!(ty.kind(), rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::Coroutine(..)))
}
