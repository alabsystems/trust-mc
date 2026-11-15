// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Payload extraction helpers shared by CHC constant-expression decoding.

use ay_bindings::{Expr, Sort};
use rustc_abi::VariantIdx as InternalVariantIdx;
use rustc_middle::ty::tls;
use rustc_public::rustc_internal;
use rustc_public::target::MachineInfo;
use rustc_public::ty::{AdtKind, RigidTy, TyKind};

use crate::codegen_ay::chc::codegen_stmt_aggregate_adt::sign_extend_discr_val;
use crate::codegen_ay::shared::const_pointer::{self, ConstPtr, ConstRead, ConstRef, Slot};
use crate::codegen_ay::types::POINTER_WIDTH;

/// Resolves a pointer stored in a constant (a relocation plus its offset) to
/// the address the lane gives it (`const_pointer`'s rule), or `None` when the
/// lane cannot name it. Readers that meet a pointer slot call it instead of
/// reading the slot's bytes as data.
pub(in crate::codegen_ay) type PtrResolver<'a> = &'a dyn Fn(&ConstPtr) -> Option<Expr>;
use crate::codegen_ay::shared::mono_ty;
use crate::kani_middle::abi::LayoutOf;
#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;

pub(in crate::codegen_ay::chc) fn decode_option_like_variant_index(
    bytes: &dyn ConstRead,
    inner_ty: rustc_public::ty::Ty,
    concrete_ty: rustc_public::ty::Ty,
    some_idx: usize,
    variant_count: usize,
) -> Option<usize> {
    if matches!(concrete_ty.kind(), TyKind::RigidTy(RigidTy::Ref(_, _, _) | RigidTy::RawPtr(_, _)))
        && matches!(bytes.read_slot(0, POINTER_WIDTH), Slot::Pointer(_))
    {
        // Part of #4026: niche-optimized Option<&T>/Option<*const T> carries
        // the active variant in the pointer niche rather than a tag byte; a
        // relocated pointer is never null.
        return Some(some_idx);
    }

    decode_non_unit_enum_variant_index(bytes, inner_ty, variant_count)
}

/// The variant index of the enum value of type `inner_ty` whose bytes are
/// `bytes`: its tag read at the layout's TAG FIELD offset (not byte 0) and at
/// the layout's tag width, under the slot clause. A tag slot covered by a
/// relocation is a pointer niche holding a (never-null) pointer, so it names
/// the untagged variant; any other non-data tag declines.
pub(in crate::codegen_ay) fn decode_non_unit_enum_variant_index(
    bytes: &dyn ConstRead,
    inner_ty: rustc_public::ty::Ty,
    variant_count: usize,
) -> Option<usize> {
    use rustc_public::abi::{FieldsShape, TagEncoding, VariantsShape};

    let layout = inner_ty.layout().ok()?;
    let shape = layout.shape();
    let VariantsShape::Multiple { tag: tag_scalar, tag_encoding, tag_field, .. } = &shape.variants
    else {
        return None;
    };
    let FieldsShape::Arbitrary { offsets } = &shape.fields else {
        return None;
    };
    let tag_offset = offsets.get(*tag_field)?.bytes();

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

    let tag = match bytes.read_slot(tag_offset, u32::try_from(tag_bytes * 8).ok()?) {
        Slot::Data(tag) => tag,
        Slot::Pointer(_) => {
            use crate::rustc_public_bridge::IndexedVal;
            return match tag_encoding {
                TagEncoding::Niche { untagged_variant, .. } => Some(untagged_variant.to_index()),
                _ => None,
            };
        }
        Slot::Uninit | Slot::PartialPointer | Slot::OutOfBounds => return None,
    };

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
        _ => direct_tag_variant_index(inner_ty, tag, tag_bytes as u64, variant_count),
    }
}

/// The variant a DIRECT tag names: the one whose discriminant VALUE, at the
/// tag's width, is the tag. A direct tag stores the discriminant, not the
/// variant index (`#[repr(u8)] enum Perm { A(u8) = 1, B = 0 }` stores 1 for
/// `A`, variant 0), so reading the tag as the index decoded `const CA: Perm =
/// Perm::A(5)` as `B` (review of fix/chc-lost-writes, lostwrite track round 3:
/// the discriminant-value repair otherwise turned that into a missed bug,
/// `bug_const_perm_a_ref`). A coroutine's tag is its variant index. `None`
/// when no variant has the tag.
fn direct_tag_variant_index(
    inner_ty: rustc_public::ty::Ty,
    tag: u128,
    tag_bytes: u64,
    variant_count: usize,
) -> Option<usize> {
    let TyKind::RigidTy(RigidTy::Adt(def, _)) = inner_ty.kind() else {
        let idx = usize::try_from(tag).ok()?;
        return (idx < variant_count).then_some(idx);
    };
    if def.kind() != AdtKind::Enum {
        return None;
    }
    let bits = u32::try_from(tag_bytes.checked_mul(8)?).ok()?;
    let mask = if bits >= 128 { u128::MAX } else { (1u128 << bits) - 1 };
    tls::with(|tcx| {
        let internal_def = rustc_internal::internal(tcx, def);
        (0..def.variants().len().min(variant_count)).find(|&v| {
            let d = internal_def.discriminant_for_variant(tcx, InternalVariantIdx::from_usize(v));
            d.val & mask == tag & mask
        })
    })
}

/// The fat pointer (`&str` / `&[T]`) stored at `slot_offset` in `bytes`: its
/// data pointer (the relocation STARTING there, with its offset) and its
/// length word, read as a pointer to `pointee` (`const_pointer::const_ref`).
pub(in crate::codegen_ay::chc) fn fat_ref_const_ref(
    bytes: &dyn ConstRead,
    slot_offset: usize,
    pointee: rustc_public::ty::Ty,
) -> Option<ConstRef> {
    const_pointer::const_ref(bytes, slot_offset, pointee)
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

/// Extracts the single-field payload of variant `variant_idx` of the enum
/// constant `bytes` (of type `enum_ty`) as a bitvector or boolean.
///
/// The payload sits at its own offset in the enum's layout: after the tag for
/// a tagged layout (`Option<u32>`: bytes 4..8), in place at 0 for a
/// niche-encoded one (`Option<char>`, `Option<Ordering>`). Exactly the
/// payload's bytes are read, under the slot clause; a fieldless enum payload
/// goes through [`fieldless_enum_const_bits`]. A pointer payload of a
/// non-reference type (`Option<NonNull<T>>`, `Option<fn()>`) is the address
/// `resolve` gives its relocation, never the relocation's offset bytes.
#[must_use]
pub(in crate::codegen_ay::chc) fn extract_payload_from_alloc(
    bytes: &dyn ConstRead,
    enum_ty: rustc_public::ty::Ty,
    variant_idx: usize,
    concrete_ty: rustc_public::ty::Ty,
    payload_sort: &Sort,
    resolve: PtrResolver<'_>,
) -> Option<Expr> {
    // The payload's offset in the enum's layout. `None` only when the layout
    // is not available; the size-based rules below then apply.
    let layout_offset = LayoutOf::new(enum_ty).variant_field_offset(variant_idx, 0);

    if let TyKind::RigidTy(RigidTy::Ref(_, pointee_ty, _) | RigidTy::RawPtr(pointee_ty, _)) =
        concrete_ty.kind()
    {
        // Part of #4026: Option<&T> constants are modeled value-semantically as
        // Option<T>: decode the POINTEE, which is the window at the stored
        // pointer's offset in a fixed target (`const_pointer::fixed_pointee`),
        // never the target from byte 0.
        let slot = layout_offset.unwrap_or(0);
        if let Some(expr) = tls::with(|tcx| {
            let (_, window) = const_pointer::fixed_pointee(tcx, bytes, slot, pointee_ty)?;
            extract_provenance_payload_from_alloc(&window, pointee_ty, payload_sort)
        }) {
            return Some(expr);
        }
        // A pointer payload that does not decode is not read as data below.
        if bytes.stored_pointer(slot).is_some() {
            return None;
        }
    }

    if LayoutOf::new(concrete_ty).size_of() == Some(0) && payload_sort.is_bool() {
        // CHC models ZST payloads (for example `()`) with the canonical Bool
        // sentinel `true`. Promoted constants for variants like Yielded(())
        // have no payload bytes to read, so byte-based extraction would
        // incorrectly materialize `false`.
        return Some(Expr::bool_const(true));
    }

    if let Some(width) = payload_sort.bitvec_width()
        && ty_is_fieldless_enum(concrete_ty)
    {
        let offset = layout_offset?;
        let value = fieldless_enum_const_bits(concrete_ty, bytes, offset, width)?;
        return Some(Expr::bitvec_const(value, width));
    }

    if let Some(width) = payload_sort.bitvec_width() {
        let byte_size = (width / 8) as usize;
        // A payload whose layout size is not its sort's width is not a plain
        // little-endian scalar of that width; reading `byte_size` bytes would
        // take the neighbouring bytes (or none) and invent a value.
        if LayoutOf::new(concrete_ty).size_of().is_some_and(|size| size != byte_size) {
            return None;
        }
        // Tagged layouts place the payload after the discriminant at its natural
        // alignment (matches statement layer operand.rs). Niche-encoded layouts
        // (e.g. `Option<char>`, `Option<NonZero<_>>`) store the payload in-place
        // at offset 0 with no separate tag, so the whole allocation is exactly
        // the payload size. Reading at `align_of()` there would run past the end
        // and materialize a spurious 0 (the `Some('o')` -> 0x00000000 bug).
        // Detect the niche case by allocation size: if the aligned read would not
        // fit, the payload is in-place at 0.
        let offset = match layout_offset {
            Some(offset) => offset,
            None => {
                let align_off = LayoutOf::new(concrete_ty).align_of().unwrap_or(byte_size.max(1));
                if align_off + byte_size > bytes.len() { 0 } else { align_off }
            }
        };
        return match bytes.read_slot(offset, width) {
            Slot::Data(value) => {
                let masked = if width >= 128 { value } else { value & ((1u128 << width) - 1) };
                Some(Expr::bitvec_const(masked, width))
            }
            // Bytes covered by a relocation are never data: the slot is the
            // pointer's address (D8).
            Slot::Pointer(ptr) => resolve(&ptr),
            Slot::Uninit | Slot::PartialPointer | Slot::OutOfBounds => None,
        };
    }

    if payload_sort.is_bool() {
        // Same tagged-vs-niche offset rule as the bitvec branch above. The
        // hard-coded `1` assumed a TAGGED layout (tag byte, then payload); a
        // niche-encoded `enum E { A, B(bool) }` is ONE byte with the payload
        // in place at offset 0, so that read ran past the end, returned None,
        // and dropped the ENTIRE promoted constant — its memory image was
        // never seeded, and `x == E::B(true)` compared against an
        // unconstrained byte.
        // A ONE-BYTE allocation is unambiguously niche-encoded: there is no room
        // for a tag, so the payload is in place at 0. Anything larger is read at
        // the alignment boundary like the bitvec branch, and an out-of-range
        // offset FAILS CLOSED (`?` -> constant dropped) rather than falling back
        // to 0. The fallback would mis-decode a tagged layout whose payload does
        // not start at 0 -- reading the tag as the payload -- and a wrong
        // constant can make an assertion PASS that should fail, which is the
        // missed-bug direction. Dropping the constant is merely imprecise.
        let offset = match layout_offset {
            Some(offset) => offset,
            None if bytes.len() == 1 => 0,
            None => LayoutOf::new(concrete_ty).align_of().unwrap_or(1),
        };
        let b = bytes.read_uint_at(offset, 1)?;
        return Some(Expr::bool_const(b != 0));
    }

    None
}

/// The pointee value an `Option<&T>` payload's window decodes to. Every read
/// obeys the slot clause: an uninitialized byte declines (it was read as 0).
fn extract_provenance_payload_from_alloc(
    window: &dyn ConstRead,
    pointee_ty: rustc_public::ty::Ty,
    payload_sort: &Sort,
) -> Option<Expr> {
    if LayoutOf::new(pointee_ty).size_of() == Some(0) && payload_sort.is_bool() {
        return Some(Expr::bool_const(true));
    }

    if let Some(width) = payload_sort.bitvec_width()
        && ty_is_fieldless_enum(pointee_ty)
    {
        return fieldless_enum_const_bits(pointee_ty, window, 0, width)
            .map(|value| Expr::bitvec_const(value, width));
    }

    if let Some(width) = payload_sort.bitvec_width() {
        let byte_size = (width / 8) as usize;
        if LayoutOf::new(pointee_ty).size_of().is_some_and(|size| size != byte_size) {
            return None;
        }
        let value = window.read_uint_at(0, byte_size)?;
        let masked = if width >= 128 { value } else { value & ((1u128 << width) - 1) };
        return Some(Expr::bitvec_const(masked, width));
    }

    if payload_sort.is_bool() {
        let b = window.read_uint_at(0, 1)?;
        return Some(Expr::bool_const(b != 0));
    }

    None
}

/// Is `ty` an enum all of whose variants are fieldless (`Ordering`,
/// `enum E { A, B }`)?
pub(in crate::codegen_ay) fn ty_is_fieldless_enum(ty: rustc_public::ty::Ty) -> bool {
    matches!(
        ty.kind(),
        TyKind::RigidTy(RigidTy::Adt(def, _))
            if def.kind() == AdtKind::Enum
                && def.variants_iter().all(|variant| variant.fields().is_empty())
    )
}

/// The `width`-bit value every lane gives the FIELDLESS enum `ty` whose bytes
/// start `bytes`, or `None` when it cannot be decoded exactly.
///
/// A fieldless enum is encoded as its discriminant, a two's-complement integer
/// of the sort's width: `translate_adt_aggregate`, the statement lane's
/// unit-enum aggregate and `adt_scalar_to_expr` all go through
/// `sign_extend_discr_val`. A constant's bytes hold the enum's TAG, `size_of`
/// bytes wide (one byte for `Ordering`, whose sort is BV32). Payload and field
/// readers that took the sort's width read the neighbouring bytes or ran off the
/// allocation, and never sign-extended: `Some(Ordering::Less)` decoded as
/// `Some(0x000000FF)` and `Ok(Ordering::Greater)` (tag at byte 0, payload at
/// byte 1) as `Ok(0x100)`. A joined `o` then compared unequal to the constant
/// and `!(o == Some(Ordering::Less))` was proved
/// (tools/soundness-duals/negative/joined_enum_constant_payloads.rs).
///
/// The tag is read zero- and sign-extended and must match exactly one variant's
/// discriminant. An uninitialised or missing byte, or a value no variant has,
/// is `None`.
pub(in crate::codegen_ay) fn fieldless_enum_const_bits(
    ty: rustc_public::ty::Ty,
    bytes: &dyn ConstRead,
    at: usize,
    width: u32,
) -> Option<u128> {
    let TyKind::RigidTy(RigidTy::Adt(def, _)) = ty.kind() else {
        return None;
    };
    if !ty_is_fieldless_enum(ty) || width == 0 || width > 128 {
        return None;
    }
    let variant_count = def.variants().len();
    if variant_count == 0 {
        return None;
    }
    let size = LayoutOf::new(ty).size_of()?;
    if size > 16 {
        return None;
    }
    let mask = |value: u128| if width >= 128 { value } else { value & ((1u128 << width) - 1) };
    tls::with(|tcx| {
        let internal_def = rustc_internal::internal(tcx, def);
        let discriminants: Vec<u128> = (0..variant_count)
            .map(|idx| {
                let discr =
                    internal_def.discriminant_for_variant(tcx, InternalVariantIdx::from_usize(idx));
                mask(sign_extend_discr_val(discr.val, discr.ty, tcx, width))
            })
            .collect();
        if size == 0 {
            return (variant_count == 1).then(|| discriminants[0]);
        }
        // The tag's bytes, under the slot clause (a relocation is not a tag).
        let raw = bytes.read_uint_at(at, size)?;
        let bits = (size * 8) as u32;
        let zero_extended = mask(raw);
        let sign_extended = if bits < 128 && raw & (1u128 << (bits - 1)) != 0 {
            mask(raw | !((1u128 << bits) - 1))
        } else {
            zero_extended
        };
        match (discriminants.contains(&zero_extended), discriminants.contains(&sign_extended)) {
            (true, false) => Some(zero_extended),
            (false, true) => Some(sign_extended),
            (true, true) if zero_extended == sign_extended => Some(zero_extended),
            _ => None,
        }
    })
}

/// Read field `field_idx` of variant `variant_idx` of the enum constant
/// `alloc` (of type `enum_ty`) as a value of `sort`, or `None`.
///
/// The field's type is taken from `enum_ty` with its generic arguments. ZST
/// fields carry no bytes: the model represents them with the canonical `true`
/// Bool sentinel (matching [`extract_payload_from_alloc`]). Every other field is
/// read at its own layout offset over exactly its layout size, a fieldless
/// enum through [`fieldless_enum_const_bits`]. A field whose size is not its
/// sort's width, a missing or uninitialised byte, and a sort this reader does
/// not decode (datatypes, arrays) are `None`: the caller drops the whole
/// constant rather than inventing a value.
pub(in crate::codegen_ay) fn read_enum_variant_field_const(
    bytes: &dyn ConstRead,
    enum_ty: rustc_public::ty::Ty,
    variant_idx: usize,
    field_idx: usize,
    sort: &Sort,
    resolve: PtrResolver<'_>,
) -> Option<Expr> {
    let TyKind::RigidTy(RigidTy::Adt(def, args)) = enum_ty.kind() else {
        return None;
    };
    let field_ty =
        mono_ty::field_ty(def.variants().get(variant_idx)?.fields().get(field_idx)?, &args)?;
    let size = LayoutOf::new(field_ty).size_of()?;
    if size == 0 {
        return if sort.is_bool() {
            Some(Expr::bool_const(true))
        } else {
            sort.bitvec_width().map(|w| Expr::bitvec_const(0u128, w))
        };
    }
    let offset = LayoutOf::new(enum_ty).variant_field_offset(variant_idx, field_idx)?;
    if let Some(width) = sort.bitvec_width()
        && ty_is_fieldless_enum(field_ty)
    {
        let value = fieldless_enum_const_bits(field_ty, bytes, offset, width)?;
        return Some(Expr::bitvec_const(value, width));
    }
    if sort.is_bool() {
        if size != 1 {
            return None;
        }
        return Some(Expr::bool_const(bytes.read_uint_at(offset, 1)? != 0));
    }
    let width = sort.bitvec_width()?;
    let byte_size = (width / 8) as usize;
    if byte_size != size {
        return None;
    }
    match bytes.read_slot(offset, width) {
        Slot::Data(value) => {
            let masked = if width >= 128 { value } else { value & ((1u128 << width) - 1) };
            Some(Expr::bitvec_const(masked, width))
        }
        // A pointer field is its relocation's address (D8), never its offset
        // bytes read as an integer.
        Slot::Pointer(ptr) => resolve(&ptr),
        Slot::Uninit | Slot::PartialPointer | Slot::OutOfBounds => None,
    }
}
