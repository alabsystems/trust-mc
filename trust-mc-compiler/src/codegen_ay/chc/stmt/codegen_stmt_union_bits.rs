// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A union's bits and its fields' values, in MEMORY order.
//!
//! `translate_adt_sort` encodes a union as ONE bitvector of its byte size, and
//! every field of a union lives at offset 0. Writing a field is writing its
//! bytes into the low end of that bitvector (little-endian); reading a field is
//! reading those bytes back as the field's type. This module is the one place
//! both directions are built, for every union access route:
//!
//! - a union aggregate `U { f: v }` ([`ChcCtx::union_bits_of_field_write`]);
//! - an assignment into a field `u.f = v` or a field of it `u.f.g = v`;
//! - a read of a field `u.f`, a field of it `u.f.g`, an element `u.a[i]`, and
//!   the same through a reference (`(*p).f`) ([`ChcCtx::union_field_value`]).
//!
//! Before this module each route read and wrote through type-blind selectors.
//! A struct field `Words { lo, hi }` was flattened in DECLARATION order, MSB
//! first, so `lo` landed in the high half; the bitvector field selector treats
//! every 128-bit container as `Layout { size, align }` (field 0 = high half,
//! field 1 = low half) and every 64-bit container as a pointer wrapper (field 0
//! = the whole value). Reading `u.w` of `U { x: v }` put `v`'s HIGH word into
//! `lo` and never defined `hi`; reading `u.x` of a 128-bit union kept only the
//! low 64 bits; reading `u.w.hi` extracted the low 64 bits. Each gave missed
//! bugs and certified false counterexamples (fix/chc-false-certificates review,
//! 2026-09-27: `wn_read_bug`, `w_hi_only_bug`, `w_read_field_bug`,
//! `nest_read_bug`, `subfield_assign_bug` all SUCCESSFUL where Kani fails).
//!
//! The value of a field is built from its MIR layout: integers, floats and
//! `char` are their bytes; a thin pointer is its address word (converted
//! between the encoder's pointer identity and an integer the way a transmute
//! does); a fieldless enum is its tag; a struct or tuple is its fields at their
//! offsets, recursively (padding is fresh: it is uninitialized); a small array
//! of scalars is its elements; a `bool` is its byte (nonzero is `true`, which
//! agrees with every valid byte). Any other shape (an enum with data or a
//! signed tag, a wide pointer, a large array) is [`UnionLane::Unmodeled`]
//! and the caller writes a FRESH value and books `transmute_layout_fallback`:
//! a sound over-approximation, never a guessed layout.
//!
//! Bytes a union field write does not cover keep their previous value, and in a
//! fresh aggregate they are uninitialized, so they are a fresh bitvector (the
//! model of "any value"; reading them is undefined behaviour, which Kani also
//! reports as a failure rather than as zero).

#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use ay_bindings::{Expr, Sort};
use rustc_public::CrateDef;
use rustc_public::abi::FieldsShape;
use rustc_public::rustc_internal;
use rustc_public::ty::{AdtKind, RigidTy, Ty, TyKind};
use tracing::debug;

use crate::codegen_ay::chc::call::canonical_zst_expr_for_sort;
use crate::codegen_ay::shared::mono_ty;
use crate::codegen_ay::types::{POINTER_WIDTH, datatype_field_select, ptr_sort};

use super::codegen_ctx::push_pending_datatype_sort;
use super::codegen_types::CodegenTypes;
use super::{ChcCtx, chc_fresh_name};
use crate::codegen_ay::chc::codegen_ctx::{ExactVar, Havoc};

/// Deepest nesting of structs, tuples and arrays the lane walks.
const MAX_DEPTH: u32 = 8;

/// Most elements an array field may have for the lane to build it element by
/// element (a store chain on reads, a concatenation on writes).
const MAX_ARRAY_ELEMS: u64 = 64;

/// What the lane decided for one field value or image.
#[derive(Debug)]
pub(in crate::codegen_ay::chc) enum UnionLane {
    /// The value (or the bits), built from the MIR layout.
    Exact(Expr),
    /// A shape the lane does not model: the caller writes a fresh value.
    Unmodeled(&'static str),
}

/// One field of a struct or tuple as it lies in memory.
struct FieldSlot {
    decl_idx: usize,
    offset: u64,
    size: u64,
    ty: Ty,
}

fn layout_size(ty: Ty) -> Option<u64> {
    Some(ty.layout().ok()?.shape().size.bytes() as u64)
}

fn is_scalar_bits_ty(ty: Ty) -> bool {
    matches!(
        ty.kind(),
        TyKind::RigidTy(RigidTy::Int(_) | RigidTy::Uint(_) | RigidTy::Float(_) | RigidTy::Char)
    )
}

fn is_thin_ptr_ty(ty: Ty, size: u64) -> bool {
    matches!(ty.kind(), TyKind::RigidTy(RigidTy::RawPtr(..) | RigidTy::Ref(..)))
        && size == u64::from(POINTER_WIDTH / 8)
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// The bit width of `ty` when it is a union the encoder models as one flat
    /// bitvector of its size: not `MaybeUninit`, which `translate_ty` delegates
    /// to its payload's sort, and not zero-sized.
    pub(in crate::codegen_ay::chc) fn flat_union_width(&self, ty: Ty) -> Option<u32> {
        let ty = self.resolve_body_ty(ty);
        let TyKind::RigidTy(RigidTy::Adt(def, _)) = ty.kind() else { return None };
        if def.kind() != AdtKind::Union {
            return None;
        }
        if matches!(def.trimmed_name().as_str(), "MaybeUninit" | "std::mem::MaybeUninit") {
            return None;
        }
        let bits = u32::try_from(8 * layout_size(ty)?).ok()?;
        if bits == 0 {
            return None;
        }
        (Self::translate_ty(ty)?.bitvec_width() == Some(bits)).then_some(bits)
    }

    /// The value of the union field of type `field_ty` held in `bits` (the
    /// union's bitvector): the field's bytes at offset 0, in memory order. A
    /// shape the lane does not model is a fresh value with the
    /// `transmute_layout_fallback` booking. `None` only when the field type has
    /// no sort at all.
    pub(in crate::codegen_ay::chc) fn union_field_value(
        &self,
        bits: &Expr,
        field_ty: Ty,
    ) -> Option<Expr> {
        let field_ty = self.resolve_body_ty(field_ty);
        let sort = Self::translate_ty(field_ty)?;
        match self.union_field_lane(bits, field_ty) {
            UnionLane::Exact(value) => Some(value),
            UnionLane::Unmodeled(why) => {
                debug!(why, ?field_ty, "CHC: union field layout not modeled; fresh value");
                let booked = self.record_sound_fallback_reason("transmute_layout_fallback");
                if sort.is_datatype() {
                    push_pending_datatype_sort(sort.clone());
                }
                Some(Havoc::booked(booked, chc_fresh_name("__union_field_layout_nondet"), sort))
            }
        }
    }

    /// [`Self::union_field_value`] without the fallback: `Unmodeled` when the
    /// lane cannot build the field exactly.
    pub(in crate::codegen_ay::chc) fn union_field_lane(
        &self,
        bits: &Expr,
        field_ty: Ty,
    ) -> UnionLane {
        let field_ty = self.resolve_body_ty(field_ty);
        let Some(size) = layout_size(field_ty) else {
            return UnionLane::Unmodeled("union field has no layout");
        };
        let Some(sort) = Self::translate_ty(field_ty) else {
            return UnionLane::Unmodeled("union field has no sort");
        };
        if size == 0 {
            return match canonical_zst_expr_for_sort(field_ty, &sort) {
                Some(zst) => UnionLane::Exact(zst),
                None if sort.is_bool() => UnionLane::Exact(Expr::bool_const(true)),
                None => UnionLane::Unmodeled("zero-sized union field has no canonical value"),
            };
        }
        let Some(width) = bits.sort().bitvec_width() else {
            return UnionLane::Unmodeled("union root is not a bitvector");
        };
        let field_bits = 8 * size;
        if u64::from(width) < field_bits {
            return UnionLane::Unmodeled("union narrower than its field");
        }
        let low = if u64::from(width) == field_bits {
            bits.clone()
        } else {
            bits.clone().extract(field_bits as u32 - 1, 0)
        };
        match self.bits_to_value(&low, field_ty, 0) {
            Ok(value) => UnionLane::Exact(value),
            Err(why) => UnionLane::Unmodeled(why),
        }
    }

    /// The union bitvector (of width `union_bits`) after writing `value` into
    /// its field of type `field_ty`. Bytes the field does not cover keep their
    /// value from `old`, or are fresh (uninitialized) when `old` is `None` (a
    /// new aggregate). `Unmodeled` when the field's bytes cannot be built.
    pub(in crate::codegen_ay::chc) fn union_bits_of_field_write(
        &self,
        old: Option<&Expr>,
        union_bits: u32,
        field_ty: Ty,
        value: &Expr,
    ) -> UnionLane {
        let field_ty = self.resolve_body_ty(field_ty);
        let Some(size) = layout_size(field_ty) else {
            return UnionLane::Unmodeled("union field has no layout");
        };
        let field_bits = 8 * size;
        if field_bits == 0 {
            return UnionLane::Unmodeled("zero-sized union field");
        }
        if field_bits > u64::from(union_bits) {
            return UnionLane::Unmodeled("union narrower than its field");
        }
        if let Some(old) = old
            && old.sort().bitvec_width() != Some(union_bits)
        {
            return UnionLane::Unmodeled("union root is not its bitvector");
        }
        let image = match self.value_to_bits(value, field_ty, 0) {
            Ok(image) => image,
            Err(why) => return UnionLane::Unmodeled(why),
        };
        if field_bits == u64::from(union_bits) {
            return UnionLane::Exact(image);
        }
        let high = match old {
            Some(old) => old.clone().extract(union_bits - 1, field_bits as u32),
            None => ExactVar::nondet(
                chc_fresh_name("__union_uninit_bytes"),
                Sort::bitvec(union_bits - field_bits as u32),
            ),
        };
        UnionLane::Exact(high.concat(image))
    }

    /// The value of type `target_ty` whose memory image is that of `value` (of
    /// type `src_ty`): a `transmute` built from both layouts, through the same
    /// value/bits lane as a union field. `Unmodeled` when either side's image
    /// is not modeled or the sizes differ.
    pub(in crate::codegen_ay::chc) fn transmute_via_memory_image(
        &self,
        value: &Expr,
        src_ty: Ty,
        target_ty: Ty,
    ) -> UnionLane {
        let src_ty = self.resolve_body_ty(src_ty);
        let target_ty = self.resolve_body_ty(target_ty);
        match (layout_size(src_ty), layout_size(target_ty)) {
            (Some(a), Some(b)) if a == b && a > 0 => {}
            _ => return UnionLane::Unmodeled("transmute sizes differ or are zero"),
        }
        let image = match self.value_to_bits(value, src_ty, 0) {
            Ok(image) => image,
            Err(why) => return UnionLane::Unmodeled(why),
        };
        match self.bits_to_value(&image, target_ty, 0) {
            Ok(result) => UnionLane::Exact(result),
            Err(why) => UnionLane::Unmodeled(why),
        }
    }

    /// The value of type `referent_ty` after writing `value` (of the NARROWER
    /// type `written_ty`) over `old`'s bytes starting at byte `offset`: `old`'s
    /// memory image with `size_of::<written_ty>()` bytes at `offset` replaced
    /// by `value`'s, read back in `referent_ty`'s layout. A store through a
    /// pointer cast into the referent (`*(&mut s as *mut S as *mut u16) = v` at
    /// offset 0, `*(&mut x as *mut u32 as *mut u8).byte_add(3) = 0` at 3).
    /// `Unmodeled` when either image is not modeled, `written_ty` is not
    /// narrower, or the written bytes leave the referent.
    pub(in crate::codegen_ay::chc) fn splice_bytes_at(
        &self,
        old: &Expr,
        referent_ty: Ty,
        value: &Expr,
        written_ty: Ty,
        offset: u64,
    ) -> UnionLane {
        let referent_ty = self.resolve_body_ty(referent_ty);
        // `MaybeUninit<T>` is encoded as `T` (`translate_ty` delegates to its
        // payload), so its image is `T`'s.
        let referent_ty = match referent_ty.kind() {
            TyKind::RigidTy(RigidTy::Adt(def, args))
                if def.kind() == AdtKind::Union
                    && matches!(
                        def.trimmed_name().as_str(),
                        "MaybeUninit" | "std::mem::MaybeUninit"
                    ) =>
            {
                match args.0.first() {
                    Some(rustc_public::ty::GenericArgKind::Type(inner)) => {
                        self.resolve_body_ty(*inner)
                    }
                    _ => referent_ty,
                }
            }
            _ => referent_ty,
        };
        let written_ty = self.resolve_body_ty(written_ty);
        let (Some(total), Some(written)) = (layout_size(referent_ty), layout_size(written_ty))
        else {
            return UnionLane::Unmodeled("store or referent has no layout");
        };
        if written == 0 || written >= total {
            return UnionLane::Unmodeled("store is not narrower than its referent");
        }
        let Some(end) = offset.checked_add(written).filter(|&end| end <= total) else {
            return UnionLane::Unmodeled("store leaves its referent");
        };
        let old_image = match self.value_to_bits(old, referent_ty, 0) {
            Ok(image) => image,
            Err(why) => return UnionLane::Unmodeled(why),
        };
        let piece = match self.value_to_bits(value, written_ty, 0) {
            Ok(image) => image,
            Err(why) => return UnionLane::Unmodeled(why),
        };
        // Little-endian image: byte `k` is bits `8k .. 8k + 7`, so the bytes
        // above the store are the high part and the bytes below it the low.
        let mut image = piece;
        if end < total {
            image = old_image.clone().extract(8 * total as u32 - 1, 8 * end as u32).concat(image);
        }
        if offset > 0 {
            image = image.concat(old_image.extract(8 * offset as u32 - 1, 0));
        }
        match self.bits_to_value(&image, referent_ty, 0) {
            Ok(result) => UnionLane::Exact(result),
            Err(why) => UnionLane::Unmodeled(why),
        }
    }

    /// The value of type `read_ty` whose bytes are `container`'s (of type
    /// `container_ty`) from byte `offset` on: a read through a pointer cast
    /// that is wider than its referent and stays inside the local holding it
    /// (`*(&s.a as *const u16 as *const u32)` reads `s.a` and `s.b`).
    /// `Unmodeled` when either image is not modeled or the bytes leave the
    /// container.
    pub(in crate::codegen_ay::chc) fn bytes_at(
        &self,
        container: &Expr,
        container_ty: Ty,
        offset: u64,
        read_ty: Ty,
    ) -> UnionLane {
        let container_ty = self.resolve_body_ty(container_ty);
        let read_ty = self.resolve_body_ty(read_ty);
        let (Some(total), Some(read)) = (layout_size(container_ty), layout_size(read_ty)) else {
            return UnionLane::Unmodeled("read or container has no layout");
        };
        let Some(end) = offset.checked_add(read).filter(|&end| read > 0 && end <= total) else {
            return UnionLane::Unmodeled("read leaves its container");
        };
        let image = match self.value_to_bits(container, container_ty, 0) {
            Ok(image) => image,
            Err(why) => return UnionLane::Unmodeled(why),
        };
        let piece = if offset == 0 && end == total {
            image
        } else {
            image.extract(8 * end as u32 - 1, 8 * offset as u32)
        };
        match self.bits_to_value(&piece, read_ty, 0) {
            Ok(result) => UnionLane::Exact(result),
            Err(why) => UnionLane::Unmodeled(why),
        }
    }

    /// The fields of a struct or tuple with their memory offsets, and its size.
    fn struct_field_slots(&self, ty: Ty) -> Option<(Vec<FieldSlot>, u64)> {
        let field_tys: Vec<Ty> = match ty.kind() {
            TyKind::RigidTy(RigidTy::Adt(def, args)) if def.kind() == AdtKind::Struct => {
                let variants = def.variants();
                let [variant] = variants.as_slice() else { return None };
                variant
                    .fields()
                    .iter()
                    .map(|field| Some(self.resolve_body_ty(mono_ty::field_ty(field, &args)?)))
                    .collect::<Option<_>>()?
            }
            TyKind::RigidTy(RigidTy::Tuple(tys)) => {
                tys.iter().map(|ty| self.resolve_body_ty(*ty)).collect()
            }
            _ => return None,
        };
        let shape = ty.layout().ok()?.shape();
        let FieldsShape::Arbitrary { offsets } = &shape.fields else { return None };
        if offsets.len() != field_tys.len() {
            return None;
        }
        let mut slots = Vec::with_capacity(field_tys.len());
        for (decl_idx, (field_ty, offset)) in field_tys.into_iter().zip(offsets).enumerate() {
            slots.push(FieldSlot {
                decl_idx,
                offset: offset.bytes() as u64,
                size: layout_size(field_ty)?,
                ty: field_ty,
            });
        }
        Some((slots, shape.size.bytes() as u64))
    }

    /// Whether every discriminant of the fieldless enum `ty` is a non-negative
    /// value below `2^(8 * size)`: its tag bytes then zero-extend to the
    /// encoded discriminant, and the encoded discriminant truncates to them.
    fn fieldless_enum_tag_is_unsigned(&self, ty: Ty, size: u64) -> bool {
        let TyKind::RigidTy(RigidTy::Adt(def, _)) = ty.kind() else { return false };
        if def.kind() != AdtKind::Enum || def.variants().iter().any(|v| !v.fields().is_empty()) {
            return false;
        }
        let internal_def = rustc_internal::internal(self.tcx, def);
        let tag_bits = 8 * size as u32;
        def.variants().iter().enumerate().all(|(idx, _)| {
            let discr = internal_def
                .discriminant_for_variant(self.tcx, rustc_abi::VariantIdx::from_usize(idx));
            let stable_ty = rustc_internal::stable(discr.ty);
            match stable_ty.kind() {
                TyKind::RigidTy(RigidTy::Int(i)) => {
                    let bits = crate::codegen_ay::types::int_ty_to_bitvec_width(i);
                    if bits == 0 || (bits < 128 && discr.val & (1u128 << (bits - 1)) != 0) {
                        return false;
                    }
                }
                TyKind::RigidTy(RigidTy::Uint(_)) => {}
                _ => return false,
            }
            tag_bits >= 128 || discr.val < (1u128 << tag_bits)
        })
    }

    /// The value of type `ty` whose memory image is `bits` (exactly `8 *
    /// size_of::<ty>()` bits wide). See the module documentation.
    fn bits_to_value(&self, bits: &Expr, ty: Ty, depth: u32) -> Result<Expr, &'static str> {
        if depth > MAX_DEPTH {
            return Err("union field nests too deeply");
        }
        let ty = self.resolve_body_ty(ty);
        let size = layout_size(ty).ok_or("union field has no layout")?;
        let sort = Self::translate_ty(ty).ok_or("union field has no sort")?;
        if size == 0 {
            return canonical_zst_expr_for_sort(ty, &sort)
                .ok_or("zero-sized field has no canonical value");
        }
        let width = 8 * size;
        if bits.sort().bitvec_width().map(u64::from) != Some(width) {
            return Err("field bits have the wrong width");
        }
        if is_scalar_bits_ty(ty) {
            return if sort.bitvec_width().map(u64::from) == Some(width) {
                Ok(bits.clone())
            } else {
                Err("scalar field sort differs from its size")
            };
        }
        if is_thin_ptr_ty(ty, size) {
            return if sort == ptr_sort() {
                Ok(self.int_to_ptr_value(bits.clone()))
            } else {
                Err("pointer field is not a thin pointer sort")
            };
        }
        // A union nested in the image is its own bitvector, in memory order
        // (`flat_union_width`): its bits ARE its value.
        if self.flat_union_width(ty).map(u64::from) == Some(width) {
            return if sort.bitvec_width().map(u64::from) == Some(width) {
                Ok(bits.clone())
            } else {
                Err("union sort differs from its size")
            };
        }
        match ty.kind() {
            // A byte read as `bool`: 0 is false, 1 is true, and any other value
            // is undefined behaviour (an invalid `bool`); reading it as
            // "nonzero" agrees with every valid byte.
            TyKind::RigidTy(RigidTy::Bool) if sort.is_bool() && size == 1 => {
                Ok(bits.clone().eq(Expr::bitvec_const(0u64, 8)).not())
            }
            TyKind::RigidTy(RigidTy::Adt(def, _)) if def.kind() == AdtKind::Enum => {
                let sort_bits = sort.bitvec_width().ok_or("enum field is not a bitvector")?;
                if u64::from(sort_bits) < width || !self.fieldless_enum_tag_is_unsigned(ty, size) {
                    return Err("enum field is not a non-negative fieldless tag");
                }
                if u64::from(sort_bits) == width {
                    Ok(bits.clone())
                } else {
                    Ok(bits.clone().zero_extend(sort_bits - width as u32))
                }
            }
            TyKind::RigidTy(RigidTy::Adt(def, _)) if def.kind() == AdtKind::Struct => {
                self.bits_to_struct(bits, ty, &sort, depth)
            }
            TyKind::RigidTy(RigidTy::Tuple(_)) => self.bits_to_struct(bits, ty, &sort, depth),
            TyKind::RigidTy(RigidTy::Array(elem_ty, _)) => {
                let array_sort = sort.array_sort().ok_or("array field is not an array sort")?;
                let (index_sort, elem_sort) =
                    (array_sort.index_sort.clone(), array_sort.element_sort.clone());
                let elem_ty = self.resolve_body_ty(elem_ty);
                let elem_size = layout_size(elem_ty).ok_or("array element has no layout")?;
                if elem_size == 0 || width % (8 * elem_size) != 0 {
                    return Err("array element size does not divide the array");
                }
                let count = size / elem_size;
                if count > MAX_ARRAY_ELEMS {
                    return Err("array field too large to build element by element");
                }
                let index_bits =
                    index_sort.bitvec_width().ok_or("array index is not a bitvector")?;
                let mut array = ExactVar::unobserved(
                    chc_fresh_name("__union_array_base"),
                    Sort::array(index_sort.clone(), elem_sort.clone()),
                );
                for i in 0..count {
                    let lo = (8 * elem_size * i) as u32;
                    let piece = bits.clone().extract(lo + 8 * elem_size as u32 - 1, lo);
                    let elem = self.bits_to_value(&piece, elem_ty, depth + 1)?;
                    if elem.sort() != &elem_sort {
                        return Err("array element value is not the element sort");
                    }
                    array = array.store(Expr::bitvec_const(u128::from(i), index_bits), elem);
                }
                Ok(array)
            }
            _ => Err("union field type not modeled"),
        }
    }

    /// [`Self::bits_to_value`] for a struct or tuple: each field from the bytes
    /// at its offset.
    fn bits_to_struct(
        &self,
        bits: &Expr,
        ty: Ty,
        sort: &Sort,
        depth: u32,
    ) -> Result<Expr, &'static str> {
        let (slots, _) = self.struct_field_slots(ty).ok_or("struct layout not modeled")?;
        let field_value = |slot: &FieldSlot| -> Result<Expr, &'static str> {
            let lo = 8 * slot.offset as u32;
            let hi = lo + 8 * slot.size as u32;
            if slot.size == 0 {
                let field_sort = Self::translate_ty(slot.ty).ok_or("field has no sort")?;
                return canonical_zst_expr_for_sort(slot.ty, &field_sort)
                    .ok_or("zero-sized field has no canonical value");
            }
            self.bits_to_value(&bits.clone().extract(hi - 1, lo), slot.ty, depth + 1)
        };
        if let Some(dt) = sort.datatype_sort()
            && let [cons] = dt.constructors.as_slice()
            && cons.fields.len() == slots.len()
        {
            let mut fields = Vec::with_capacity(slots.len());
            for (slot, decl) in slots.iter().zip(cons.fields.iter()) {
                let value = field_value(slot)?;
                if value.sort() != &decl.sort {
                    return Err("struct field value is not its constructor sort");
                }
                fields.push(value);
            }
            push_pending_datatype_sort(sort.clone());
            return Ok(Expr::datatype_constructor(&*dt.name, &*cons.name, fields, sort.clone()));
        }
        // A wrapper the sort erases (a one-tuple, a transparent wrapper): the
        // value IS its one non-zero-sized field.
        let mut data = slots.iter().filter(|slot| slot.size != 0);
        if let (Some(only), None) = (data.next(), data.next())
            && Self::translate_ty(only.ty).as_ref() == Some(sort)
        {
            return field_value(only);
        }
        Err("struct sort is not its fields")
    }

    /// The memory image (`8 * size_of::<ty>()` bits) of `value` of type `ty`.
    /// See the module documentation.
    fn value_to_bits(&self, value: &Expr, ty: Ty, depth: u32) -> Result<Expr, &'static str> {
        if depth > MAX_DEPTH {
            return Err("union field nests too deeply");
        }
        let ty = self.resolve_body_ty(ty);
        let size = layout_size(ty).ok_or("union field has no layout")?;
        if size == 0 {
            return Err("zero-sized value has no bits");
        }
        let width = 8 * size;
        if is_scalar_bits_ty(ty) {
            return if value.sort().bitvec_width().map(u64::from) == Some(width) {
                Ok(value.clone())
            } else {
                Err("scalar value sort differs from its size")
            };
        }
        if is_thin_ptr_ty(ty, size) {
            return if value.sort() == &ptr_sort() {
                Ok(self.ptr_to_int_value(value.clone()))
            } else {
                Err("pointer value is not a thin pointer sort")
            };
        }
        if self.flat_union_width(ty).map(u64::from) == Some(width) {
            return if value.sort().bitvec_width().map(u64::from) == Some(width) {
                Ok(value.clone())
            } else {
                Err("union value sort differs from its size")
            };
        }
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Bool) if value.sort().is_bool() && size == 1 => Ok(Expr::ite(
                value.clone(),
                Expr::bitvec_const(1u64, 8),
                Expr::bitvec_const(0u64, 8),
            )),
            TyKind::RigidTy(RigidTy::Adt(def, _)) if def.kind() == AdtKind::Enum => {
                let sort_bits =
                    value.sort().bitvec_width().ok_or("enum value is not a bitvector")?;
                if u64::from(sort_bits) < width || !self.fieldless_enum_tag_is_unsigned(ty, size) {
                    return Err("enum value is not a non-negative fieldless tag");
                }
                if u64::from(sort_bits) == width {
                    Ok(value.clone())
                } else {
                    Ok(value.clone().extract(width as u32 - 1, 0))
                }
            }
            TyKind::RigidTy(RigidTy::Adt(def, _)) if def.kind() == AdtKind::Struct => {
                self.struct_to_bits(value, ty, size, depth)
            }
            TyKind::RigidTy(RigidTy::Tuple(_)) => self.struct_to_bits(value, ty, size, depth),
            TyKind::RigidTy(RigidTy::Array(elem_ty, _)) => {
                let index_sort = value
                    .sort()
                    .array_sort()
                    .ok_or("array value is not an array sort")?
                    .index_sort
                    .clone();
                let elem_ty = self.resolve_body_ty(elem_ty);
                let elem_size = layout_size(elem_ty).ok_or("array element has no layout")?;
                if elem_size == 0 || size % elem_size != 0 {
                    return Err("array element size does not divide the array");
                }
                let count = size / elem_size;
                if count > MAX_ARRAY_ELEMS {
                    return Err("array value too large to flatten element by element");
                }
                let index_bits =
                    index_sort.bitvec_width().ok_or("array index is not a bitvector")?;
                let mut image: Option<Expr> = None;
                for i in 0..count {
                    let elem = value.clone().select(Expr::bitvec_const(u128::from(i), index_bits));
                    let piece = self.value_to_bits(&elem, elem_ty, depth + 1)?;
                    // Element 0 is the lowest address, so the low end.
                    image = Some(match image {
                        None => piece,
                        Some(lower) => piece.concat(lower),
                    });
                }
                image.ok_or("array has no elements")
            }
            _ => Err("union field type not modeled"),
        }
    }

    /// [`Self::value_to_bits`] for a struct or tuple: each field's bytes at its
    /// offset, padding fresh (uninitialized).
    fn struct_to_bits(
        &self,
        value: &Expr,
        ty: Ty,
        size: u64,
        depth: u32,
    ) -> Result<Expr, &'static str> {
        let (slots, _) = self.struct_field_slots(ty).ok_or("struct layout not modeled")?;
        let is_constructor = value.sort().datatype_sort().is_some_and(
            |dt| matches!(dt.constructors.as_slice(), [cons] if cons.fields.len() == slots.len()),
        );
        let mut data: Vec<&FieldSlot> = slots.iter().filter(|slot| slot.size != 0).collect();
        let field_value = |slot: &FieldSlot| -> Result<Expr, &'static str> {
            if is_constructor {
                return datatype_field_select(value.clone(), 0, slot.decl_idx)
                    .ok_or("struct field not selectable");
            }
            // A wrapper the sort erases: the value IS its one data field.
            if data_len_is_one(&slots) && Self::translate_ty(slot.ty).as_ref() == Some(value.sort())
            {
                return Ok(value.clone());
            }
            Err("struct value is not its fields")
        };
        data.sort_by_key(|slot| slot.offset);
        let mut pieces: Vec<Expr> = Vec::with_capacity(2 * data.len() + 1);
        let mut end = 0;
        for slot in data {
            if slot.offset < end {
                return Err("struct fields overlap");
            }
            if slot.offset > end {
                pieces.push(ExactVar::nondet(
                    chc_fresh_name("__union_padding"),
                    Sort::bitvec(8 * (slot.offset - end) as u32),
                ));
            }
            let field = field_value(slot)?;
            pieces.push(self.value_to_bits(&field, slot.ty, depth + 1)?);
            end = slot.offset + slot.size;
        }
        if end > size {
            return Err("struct fields exceed its size");
        }
        if end < size {
            pieces.push(ExactVar::nondet(
                chc_fresh_name("__union_padding"),
                Sort::bitvec(8 * (size - end) as u32),
            ));
        }
        // Little-endian: the piece at the highest offset is the most significant.
        let mut iter = pieces.into_iter().rev();
        let first = iter.next().ok_or("struct has no data")?;
        Ok(iter.fold(first, Expr::concat))
    }
}

fn data_len_is_one(slots: &[FieldSlot]) -> bool {
    slots.iter().filter(|slot| slot.size != 0).count() == 1
}
