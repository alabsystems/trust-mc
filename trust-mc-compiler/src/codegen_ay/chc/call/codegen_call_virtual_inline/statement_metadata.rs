// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Metadata propagation helpers for inline statement execution.

use rustc_public::mir::{Operand, Rvalue};

use super::super::ChcCtx;

/// The local whose slice metadata a whole-local write of `rvalue` carries
/// over: the source of a copy, a cast or a borrow.
fn subslice_metadata_source(rvalue: &Rvalue) -> Option<usize> {
    match rvalue {
        Rvalue::Use(Operand::Copy(src) | Operand::Move(src), ..) if src.projection.is_empty() => {
            Some(src.local)
        }
        Rvalue::Cast(_, operand, _) => match operand {
            Operand::Copy(src) | Operand::Move(src) if src.projection.is_empty() => Some(src.local),
            _ => None,
        },
        Rvalue::Ref(_, _, src) | Rvalue::AddressOf(_, src) => Some(src.local),
        _ => None,
    }
}

/// A whole-local write REPLACES `dest_local`'s slice metadata, so its entries
/// in the side tables (`ref_resolution.subslice_len` / `subslice_offset`) are
/// removed before the rvalue is evaluated. What the write itself records
/// afterwards (an array's slice view, `inline_shared/rvalue.rs`; the
/// source's entry, [`propagate_inline_subslice_metadata`]) is then all that
/// describes the local.
///
/// The tables are keyed by local and only ever inserted into on this path, so
/// an entry outlived the value it described: `s = &arr as &[u8]` recorded
/// `len(s) = 4`, and a later `s = copy v` on the same path left it in place,
/// so `s.len()` read 4 for `v` (walker fail-closed review 6, finding 1:
/// `c3_len_in_walk_bug` proved, `s1_len_matches_safe` failed Genuine). The
/// SwitchInt arm walks restore the tables between arms (`switchint.rs`);
/// this covers one path writing a local twice (a loop, a reassignment).
///
/// An rvalue whose metadata source is `dest_local` itself (a copy onto
/// itself) keeps the entries: its value is unchanged.
pub(super) fn clear_inline_subslice_metadata_for_write(
    ctx: &mut ChcCtx<'_, '_>,
    rvalue: Option<&Rvalue>,
    dest_local: usize,
) {
    if rvalue.and_then(subslice_metadata_source) == Some(dest_local) {
        return;
    }
    ctx.ref_resolution.subslice_len.remove(&dest_local);
    ctx.ref_resolution.subslice_offset.remove(&dest_local);
}

pub(super) fn propagate_inline_subslice_metadata(
    ctx: &mut ChcCtx<'_, '_>,
    rvalue: &Rvalue,
    dest_local: usize,
) {
    let Some(src_local) = subslice_metadata_source(rvalue) else { return };
    if let Some(len) = ctx.ref_resolution.subslice_len.get(&src_local).cloned() {
        ctx.ref_resolution.subslice_len.insert(dest_local, len);
    }
    if let Some(offset) = ctx.ref_resolution.subslice_offset.get(&src_local).cloned() {
        ctx.ref_resolution.subslice_offset.insert(dest_local, offset);
    }
}

/// The slice view of an array (`&[T; N]` unsized to `&[T]`) has the array's
/// compile-time length. A walked body holds an array it built as a value,
/// with no pointer whose metadata half could carry it
/// (`inline_pack_array_unsize_len` packs a thin POINTER's), so `PtrMetadata`
/// of the view reads it from the side table (package round 2 item c:
/// `<[T]>::get_unchecked` on such an array checks `i < N`, not
/// `i < <fresh>`).
///
/// Recorded here, by the walker's statement executor, and not by the shared
/// rvalue translator, because only the walk scopes the tables: to the walked
/// body (`walker.rs`, both front doors), to one SwitchInt arm
/// (`switchint.rs`), and to one write of the local
/// ([`clear_inline_subslice_metadata_for_write`]). The quantifier and
/// bool-helper translators share the rvalue translator with no such scope,
/// so an entry they recorded for a local of THEIR body would have been read
/// by the host local of the same index.
pub(super) fn seed_inline_array_view_len(
    ctx: &mut ChcCtx<'_, '_>,
    rvalue: &Rvalue,
    locals: &[rustc_public::mir::LocalDecl],
    dest_local: usize,
) {
    use rustc_public::ty::{RigidTy, TyKind};
    let Rvalue::Cast(
        rustc_public::mir::CastKind::PointerCoercion(rustc_public::mir::PointerCoercion::Unsize),
        operand,
        target_ty,
    ) = rvalue
    else {
        return;
    };
    let Ok(src_ty) = operand.ty(locals) else { return };
    let Some(len) = ChcCtx::extract_array_len_from_ref(ctx.resolve_body_ty(src_ty)) else {
        return;
    };
    let target_is_slice_pointer = matches!(
        ctx.resolve_body_ty(*target_ty).kind(),
        TyKind::RigidTy(RigidTy::Ref(_, pointee, _) | RigidTy::RawPtr(pointee, _))
            if matches!(pointee.kind(), TyKind::RigidTy(RigidTy::Slice(_)))
    );
    if target_is_slice_pointer {
        ctx.ref_resolution.subslice_len.insert(
            dest_local,
            ay_bindings::Expr::bitvec_const(
                u128::from(len),
                crate::codegen_ay::types::POINTER_WIDTH,
            ),
        );
    }
}
