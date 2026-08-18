// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Payload extraction helpers shared by CHC constant-expression decoding.

use ay_bindings::{Expr, Sort};
use rustc_public::target::MachineInfo;
use rustc_public::ty::{Allocation, RigidTy, TyKind};

use crate::kani_middle::abi::LayoutOf;

pub(in crate::codegen_ay::chc) fn decode_option_like_variant_index(
    alloc: &Allocation,
    inner_ty: rustc_public::ty::Ty,
    concrete_ty: rustc_public::ty::Ty,
    some_idx: usize,
    variant_count: usize,
) -> Option<usize> {
    if matches!(concrete_ty.kind(), TyKind::RigidTy(RigidTy::Ref(_, _, _) | RigidTy::RawPtr(_, _)))
        && !alloc.provenance.ptrs.is_empty()
    {
        // Part of #4026: niche-optimized Option<&T>/Option<*const T> carries
        // the active variant in the pointer niche rather than a tag byte.
        return Some(some_idx);
    }

    decode_non_unit_enum_variant_index(alloc, inner_ty, variant_count)
}

pub(in crate::codegen_ay) fn decode_non_unit_enum_variant_index(
    alloc: &Allocation,
    inner_ty: rustc_public::ty::Ty,
    variant_count: usize,
) -> Option<usize> {
    use rustc_public::abi::{TagEncoding, VariantsShape};

    let layout = inner_ty.layout().ok()?;
    let VariantsShape::Multiple { tag: tag_scalar, tag_encoding, .. } = &layout.shape().variants
    else {
        return None;
    };

    // Part of #4087 D4 residual: niche-encoded promoted enum refs can store the
    // active variant in a full-width pointer/tag scalar rather than the low 1-2
    // bytes. Read the actual layout tag width so multi-variant enums like
    // `MyError::Error2(&str)` do not decode to the untagged last variant.
    let machine_info = MachineInfo::target();
    let tag_primitive = match tag_scalar {
        rustc_public::abi::Scalar::Initialized { value, .. } => value,
        _ => return None,
    };
    let tag_bytes = tag_primitive.size(&machine_info).bytes();
    if alloc.bytes.len() < tag_bytes {
        return None;
    }

    let mut tag: u128 = 0;
    for (i, byte) in alloc.bytes.iter().take(tag_bytes).enumerate() {
        let b = (*byte)? as u128;
        tag |= b << (i * 8);
    }

    match tag_encoding {
        TagEncoding::Niche { untagged_variant, niche_variants, niche_start } => {
            use crate::rustc_public_bridge::IndexedVal;

            let niche_count =
                (niche_variants.end().to_index() - niche_variants.start().to_index() + 1) as u128;
            let relative = tag.wrapping_sub(*niche_start);
            if relative < niche_count {
                Some(niche_variants.start().to_index() + relative as usize)
            } else {
                Some(untagged_variant.to_index())
            }
        }
        _ => {
            let idx = usize::try_from(tag).ok()?;
            (idx < variant_count).then_some(idx)
        }
    }
}

/// Decoded components of a constant BV128 fat-pointer payload (`&str`/`&[T]`).
///
/// Part of the fat-pointer payload unification: enum payloads holding
/// references to unsized pointees are BV128 `concat(len, data_ptr)` values,
/// so constants must be decoded to (len, backing bytes) instead of reading
/// the pointee content in place.
pub(in crate::codegen_ay::chc) struct FatRefConstParts {
    /// Element count stored in the fat pointer's metadata word.
    pub len: u64,
    /// AllocId of the provenance target (the literal's backing allocation).
    pub target_alloc_id: rustc_public::mir::alloc::AllocId,
    /// Provenance target allocation holding the literal backing bytes.
    pub target_alloc: Allocation,
}

/// Decode the metadata (len) and provenance target of a constant fat pointer.
///
/// `alloc` holds the fat-pointer bytes (e.g. a niche-optimized `Option<&str>`
/// allocation, or the `&str` payload region of an enum variant). The data
/// pointer's position within `alloc` is taken from its provenance entry; the
/// length metadata is the pointer-width word immediately following it.
pub(in crate::codegen_ay::chc) fn decode_fat_ref_const_parts(
    alloc: &Allocation,
) -> Option<FatRefConstParts> {
    use rustc_public::mir::alloc::GlobalAlloc;

    let (_, prov) = alloc.provenance.ptrs.first()?;
    let target_alloc_id = prov.0;
    let GlobalAlloc::Memory(target_alloc) = GlobalAlloc::from(target_alloc_id) else {
        return None;
    };
    let len = fat_ref_const_len(alloc)?;
    Some(FatRefConstParts { len, target_alloc_id, target_alloc })
}

/// Read the length metadata word of a constant fat pointer without following
/// provenance. The data pointer's offset within `alloc` comes from the first
/// provenance entry (0 when absent); the length is the pointer-width word
/// immediately after it.
pub(in crate::codegen_ay::chc) fn fat_ref_const_len(alloc: &Allocation) -> Option<u64> {
    let ptr_offset = alloc.provenance.ptrs.first().map_or(0, |(off, _)| *off);
    let ptr_bytes = (crate::codegen_ay::types::POINTER_WIDTH / 8) as usize;
    let len_start = ptr_offset + ptr_bytes;
    let len_bytes = alloc.bytes.get(len_start..len_start + ptr_bytes)?;
    let mut len: u64 = 0;
    for (i, byte) in len_bytes.iter().enumerate() {
        len |= ((*byte)? as u64) << (i * 8);
    }
    Some(len)
}

/// Returns true when a constant enum payload of type `concrete_ty` must be
/// decoded as a BV128 fat pointer (`&str` / `&[T]` / slice-tail DST ref).
///
/// Address-vs-value: this predicate takes no [`Expr`], so there is no
/// provenance to thread through it — the decision is already made from the
/// TYPE (`RigidTy::Ref`/`RawPtr` whose pointee is a fat-BV128 DST), and the
/// width term is only a representation precondition on the declared payload
/// slot. The width term alone would also match a plain `u128` VALUE, which is
/// why it must stay a conjunct and not become the discriminator. Separating a
/// real fat pointer from a zero-extended thin one where the type is *not*
/// available is the `PtrRepr` work in wave 3 of
/// `docs/addr-vs-value-conversion-queue.md`, not a wave-1 retyping.
pub(in crate::codegen_ay::chc) fn const_payload_is_fat_ref(
    concrete_ty: rustc_public::ty::Ty,
    payload_sort: &Sort,
) -> bool {
    use super::codegen_types::CodegenTypes as _;

    payload_sort.bitvec_width() == Some(2 * crate::codegen_ay::types::POINTER_WIDTH)
        && matches!(
            concrete_ty.kind(),
            TyKind::RigidTy(RigidTy::Ref(_, pointee, _) | RigidTy::RawPtr(pointee, _))
                if super::ChcCtx::ref_pointee_is_fat_bv128(pointee)
        )
}

/// Extracts a bitvector or boolean payload from a MIR allocation at a
/// type-aligned offset.
///
/// MIR allocations for enum variants store the discriminant first, then the
/// payload at an offset determined by the payload's natural alignment.
/// For Option<u8>, discriminant is at byte 0 and payload at byte 1.
/// For Option<u32>, discriminant is at byte 0 and payload at bytes 4..8.
#[must_use]
pub(in crate::codegen_ay::chc) fn extract_payload_from_alloc(
    alloc: &Allocation,
    concrete_ty: rustc_public::ty::Ty,
    payload_sort: &Sort,
) -> Option<Expr> {
    if let TyKind::RigidTy(RigidTy::Ref(_, pointee_ty, _) | RigidTy::RawPtr(pointee_ty, _)) =
        concrete_ty.kind()
        && !alloc.provenance.ptrs.is_empty()
        && let rustc_public::mir::alloc::GlobalAlloc::Memory(target_alloc) =
            rustc_public::mir::alloc::GlobalAlloc::from(alloc.provenance.ptrs[0].1.0)
        && let Some(expr) =
            extract_provenance_payload_from_alloc(&target_alloc, pointee_ty, payload_sort)
    {
        // Part of #4026: Option<&T> constants are modeled value-semantically as
        // Option<T>. Follow provenance to decode the pointee value instead of
        // treating the reference bytes as an in-place payload.
        return Some(expr);
    }

    if LayoutOf::new(concrete_ty).size_of() == Some(0) && payload_sort.is_bool() {
        // CHC models ZST payloads (for example `()`) with the canonical Bool
        // sentinel `true`. Promoted constants for variants like Yielded(())
        // have no payload bytes to read, so byte-based extraction would
        // incorrectly materialize `false`.
        return Some(Expr::bool_const(true));
    }

    if let Some(width) = payload_sort.bitvec_width() {
        let byte_size = (width / 8) as usize;
        // Tagged layouts place the payload after the discriminant at its natural
        // alignment (matches statement layer operand.rs). Niche-encoded layouts
        // (e.g. `Option<char>`, `Option<NonZero<_>>`) store the payload in-place
        // at offset 0 with no separate tag, so the whole allocation is exactly
        // the payload size. Reading at `align_of()` there would run past the end
        // and materialize a spurious 0 (the `Some('o')` -> 0x00000000 bug).
        // Detect the niche case by allocation size: if the aligned read would not
        // fit, the payload is in-place at 0.
        let align_off = LayoutOf::new(concrete_ty).align_of().unwrap_or(byte_size.max(1));
        let offset = if align_off + byte_size > alloc.bytes.len() { 0 } else { align_off };
        let payload_bytes = alloc.bytes.get(offset..)?;
        let mut value: u128 = 0;
        for (i, byte) in payload_bytes.iter().take(byte_size).enumerate() {
            if let Some(b) = byte {
                value |= (*b as u128) << (i * 8);
            }
        }
        let masked = if width >= 128 { value } else { value & ((1u128 << width) - 1) };
        return Some(Expr::bitvec_const(masked, width));
    }

    if payload_sort.is_bool() {
        let b = (*alloc.bytes.get(1)?)?;
        return Some(Expr::bool_const(b != 0));
    }

    None
}

fn extract_provenance_payload_from_alloc(
    alloc: &Allocation,
    pointee_ty: rustc_public::ty::Ty,
    payload_sort: &Sort,
) -> Option<Expr> {
    if LayoutOf::new(pointee_ty).size_of() == Some(0) && payload_sort.is_bool() {
        return Some(Expr::bool_const(true));
    }

    if let Some(width) = payload_sort.bitvec_width() {
        let byte_size = (width / 8) as usize;
        let payload_bytes = alloc.bytes.get(..byte_size)?;
        let mut value: u128 = 0;
        for (i, byte) in payload_bytes.iter().enumerate() {
            if let Some(b) = byte {
                value |= (*b as u128) << (i * 8);
            }
        }
        let masked = if width >= 128 { value } else { value & ((1u128 << width) - 1) };
        return Some(Expr::bitvec_const(masked, width));
    }

    if payload_sort.is_bool() {
        let b = (*alloc.bytes.first()?)?;
        return Some(Expr::bool_const(b != 0));
    }

    None
}
