// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Shared Mem-level call-result mirroring helpers.
//!
//! Reconstructs flattened destinations through their post-assignment output
//! locals before storing them to typed memory.

use crate::codegen_ay::shared::mono_ty;
#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use std::collections::HashSet;

use ay_bindings::Expr;
use rustc_public::mir::Place;
use rustc_public::ty::{RigidTy, TyKind};
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
        // Design 4 D: a slice slot's memory copy gets the same guard as the
        // slot itself. Callers that guard first pass a packed value, which this
        // leaves unchanged, so both views share one fresh length.
        let dest_ty = ctx.body.locals()[dest_local].ty;
        ctx.guard_slice_len_slot_write(dest_ty, result_expr.clone(), "call_result_memory_bridge")
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

        // Rule A (`shared::mono_ty::field_ty`): the payload's type at the ADT's
        // own arguments (`u8` for `Result<u8, u8>`; a shallow read stored to
        // mem_param_0). A payload whose type does not instantiate is not stored.
        let Some(field_ty) = mono_ty::field_ty(&variant_0_fields[payload_idx], &args) else {
            continue;
        };
        constraints.extend(ctx.build_memory_store_untyped(field_addr, field_expr, field_ty));
    }

    // Store the tag in its memory image (rustc layout): every tag byte to
    // the `u8` view, and a multi-byte tag also whole to its integer view.
    if let Some(image) = flattened_enum_tag_image(ctx, dest_local, local_ty, modified_locals) {
        let byte_addr = |k: u64| {
            let off = image.offset + k;
            if off > 0 {
                addr_expr.clone().bvadd(Expr::bitvec_const(off as u128, POINTER_WIDTH))
            } else {
                addr_expr.clone()
            }
        };
        let u8_ty = rustc_public::ty::Ty::unsigned_ty(rustc_public::ty::UintTy::U8);
        let fold =
            |e: Expr| trust_mc_core::chc_const_prop::eval::try_eval_to_const(&e).unwrap_or(e);
        for k in 0..image.size {
            let byte = fold(image.value.clone().extract(8 * k as u32 + 7, 8 * k as u32));
            constraints.extend(ctx.build_memory_store_untyped(byte_addr(k), byte, u8_ty));
        }
        let whole_ty = match image.size {
            2 => Some(rustc_public::ty::UintTy::U16),
            4 => Some(rustc_public::ty::UintTy::U32),
            8 => Some(rustc_public::ty::UintTy::U64),
            _ => None,
        };
        if let Some(uint) = whole_ty {
            let ty = rustc_public::ty::Ty::unsigned_ty(uint);
            constraints.extend(ctx.build_memory_store_untyped(byte_addr(0), fold(image.value), ty));
        }
    }

    debug!(
        dest_local,
        field_count, "Part of #3963: decomposed flattened enum fields to type-indexed memory"
    );
}

/// A flattened enum tag's memory image: `size` bytes at `offset` from the
/// enum's address, `value` their little-endian bits.
struct EnumTagImage {
    offset: u64,
    size: u64,
    value: Expr,
}

/// The memory image of flattened enum local `dest_local`'s tag, from the
/// enum's rustc layout and the local's discriminant VALUE
/// ([`ChcCtx::flattened_local_discriminant`]).
///
/// - A direct tag holds the active variant's discriminant value, at the
///   tag's width (`#[repr(u8)] enum Disc { Val(u8) = 7, Nothing = 2 }` is
///   byte 7 or 2).
/// - A niche tag holds `niche_start + (v - niche_variants.start)` for a niche
///   variant `v`, and the untagged variant's own payload bytes otherwise
///   (`Option<bool>`: `None` is 2, `Some(b)` is `b`). Those bytes are the
///   payload's image when its one flattened payload slot has one, else a
///   fresh value recorded with its identity
///   (`sound_havoc::ENUM_TAG_IMAGE_PAYLOAD_UNKNOWN`), so no counterexample that reads
///   them is certified.
///
/// Before, every flattened tag was stored as one byte `ite(fld0, 1, 0)`,
/// whatever the encoding or the local's tag convention: an explicit
/// discriminant, a `Result` (whose `fld0` names `Ok`, variant 0) and every
/// niche-encoded enum read through a `*const u8` saw a wrong byte, so
/// `bug_tag_disc_sym`, `bug_opt_bool_none_byte` and
/// `bug_opt_nonzero_some_byte` verified and their safe twins were certified
/// false failures (review of fix/chc-lost-writes, lostwrite track round 3,
/// finding 3). `None` for a layout with no tag (`Single`), a tag wider than
/// 64 bits, or a local whose discriminant does not translate.
fn flattened_enum_tag_image(
    ctx: &mut ChcCtx<'_, '_>,
    dest_local: usize,
    local_ty: rustc_public::ty::Ty,
    modified_locals: &HashSet<usize>,
) -> Option<EnumTagImage> {
    use crate::rustc_public_bridge::IndexedVal;
    use rustc_abi::VariantIdx as InternalVariantIdx;
    use rustc_public::abi::{FieldsShape, Scalar, TagEncoding, VariantsShape};
    use rustc_public::rustc_internal;
    use rustc_public::target::MachineInfo;

    let TyKind::RigidTy(RigidTy::Adt(def, args)) = local_ty.kind() else {
        return None;
    };
    let layout = local_ty.layout().ok()?;
    let shape = layout.shape();
    let VariantsShape::Multiple { tag, tag_encoding, tag_field, .. } = &shape.variants else {
        return None;
    };
    let FieldsShape::Arbitrary { offsets } = &shape.fields else {
        return None;
    };
    let offset = offsets.get(*tag_field)?.bytes() as u64;
    let Scalar::Initialized { value: tag_primitive, .. } = tag else {
        return None;
    };
    let size = tag_primitive.size(&MachineInfo::target()).bytes() as u64;
    let bits = u32::try_from(size.checked_mul(8)?).ok()?;
    if bits == 0 || bits > POINTER_WIDTH {
        return None;
    }
    let discr = ctx.flattened_local_discriminant(dest_local, modified_locals)?;
    let at_width = |e: Expr| if bits == POINTER_WIDTH { e } else { e.extract(bits - 1, 0) };
    let value = match tag_encoding {
        TagEncoding::Direct => at_width(discr),
        TagEncoding::Niche { untagged_variant, niche_variants, niche_start } => {
            let untagged = untagged_variant.to_index();
            let internal_def = rustc_internal::internal(ctx.tcx, def);
            let discr_of = |v: usize| {
                let d = internal_def
                    .discriminant_for_variant(ctx.tcx, InternalVariantIdx::from_usize(v));
                crate::codegen_ay::chc::stmt::codegen_stmt_aggregate_adt::sign_extend_discr_val(
                    d.val,
                    d.ty,
                    ctx.tcx,
                    POINTER_WIDTH,
                )
            };
            let mask = if bits >= 128 { u128::MAX } else { (1u128 << bits) - 1 };
            let niche_values: Vec<(u128, u128)> = (niche_variants.start().to_index()
                ..=niche_variants.end().to_index())
                .filter(|&v| v != untagged)
                .map(|v| {
                    let rel = (v - niche_variants.start().to_index()) as u128;
                    (discr_of(v), rel.wrapping_add(*niche_start) & mask)
                })
                .collect();
            let payload = untagged_payload_niche_image(
                ctx,
                dest_local,
                local_ty,
                &def,
                &args,
                untagged,
                offset,
                size,
                modified_locals,
            )
            .unwrap_or_else(|| {
                let name =
                    crate::codegen_ay::chc::chc_fresh_name("__enum_tag_image_payload_unknown");
                crate::codegen_ay::chc::codegen_ctx::Havoc::mint(
                    ctx,
                    crate::codegen_ay::chc::codegen_ctx::sound_havoc::ENUM_TAG_IMAGE_PAYLOAD_UNKNOWN,
                    name,
                    ay_bindings::Sort::bitvec(bits),
                )
            });
            niche_values.into_iter().fold(payload, |acc, (dv, nv)| {
                Expr::ite(
                    discr.clone().eq(Expr::bitvec_const(dv, POINTER_WIDTH)),
                    Expr::bitvec_const(nv, bits),
                    acc,
                )
            })
        }
    };
    Some(EnumTagImage { offset, size, value })
}

/// The untagged variant's bytes at a niche tag `[tag_offset, tag_offset +
/// tag_size)`, sliced from the byte image of its payload when the variant
/// has one field, the local one flattened payload slot (`fld1`), and that
/// field covers the tag; `None` otherwise.
#[allow(clippy::too_many_arguments)]
fn untagged_payload_niche_image(
    ctx: &mut ChcCtx<'_, '_>,
    dest_local: usize,
    local_ty: rustc_public::ty::Ty,
    def: &rustc_public::ty::AdtDef,
    args: &rustc_public::ty::GenericArgs,
    untagged: usize,
    tag_offset: u64,
    tag_size: u64,
    modified_locals: &HashSet<usize>,
) -> Option<Expr> {
    if ctx.flattened_field_count(dest_local) != 2 {
        return None;
    }
    let variants = def.variants();
    let fields = variants.get(untagged)?.fields();
    if fields.len() != 1 {
        return None;
    }
    let field_ty = mono_ty::field_ty(&fields[0], args)?;
    let field_off = ctx.get_variant_field_offset(local_ty, untagged, 0)?;
    let field_size = ctx.get_type_size(field_ty)? as u64;
    let rel = tag_offset.checked_sub(field_off)?;
    if rel.checked_add(tag_size)? > field_size {
        return None;
    }
    let payload = ctx.flattened_local_field_expr(dest_local, 1, modified_locals)?;
    let image = if payload.sort().bitvec_width() == u32::try_from(field_size * 8).ok()
        && transparent_scalar_newtype(ctx, field_ty, field_size)
    {
        // A one-field wrapper of a primitive (`NonZeroU8` holds a `u8`) is
        // carried as that primitive's bits, which are its image.
        payload
    } else {
        ctx.scalar_le_byte_image(&payload, Some(field_ty), field_size as usize)?
    };
    if image.sort().bitvec_width()? != u32::try_from(field_size * 8).ok()? {
        return None;
    }
    let lo = u32::try_from(rel * 8).ok()?;
    let hi = u32::try_from((rel + tag_size) * 8 - 1).ok()?;
    Some(image.extract(hi, lo))
}

/// Whether `ty` is a chain of one-field structs ending in a primitive integer,
/// `char` or `bool` of `size` bytes (`NonZero<u8>` -> `NonZeroU8Inner` -> `u8`),
/// so its value's bits are its memory image.
fn transparent_scalar_newtype(
    ctx: &ChcCtx<'_, '_>,
    ty: rustc_public::ty::Ty,
    size: u64,
) -> bool {
    let mut current = ty;
    for _ in 0..8 {
        match current.kind() {
            TyKind::RigidTy(RigidTy::Int(_) | RigidTy::Uint(_) | RigidTy::Char | RigidTy::Bool) => {
                return current != ty && ctx.get_type_size(current) == usize::try_from(size).ok();
            }
            TyKind::RigidTy(RigidTy::Adt(def, args))
                if def.kind() == rustc_public::ty::AdtKind::Struct =>
            {
                let variants = def.variants();
                let [variant] = variants.as_slice() else { return false };
                let fields = variant.fields();
                let [field] = fields.as_slice() else { return false };
                let Some(field_ty) = mono_ty::field_ty(field, &args) else { return false };
                current = field_ty;
            }
            _ => return false,
        }
    }
    false
}
