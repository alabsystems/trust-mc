// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A static's initializer read by its type's real layout, and the one
//! decomposition the static's memory image is seeded and written under.
//!
//! # The decoder
//!
//! The sequential readers (`read_composite_from_bytes`,
//! `read_composite_from_allocation`) walk a datatype's fields in declaration
//! order and advance a running offset by each field's sort width, and read an
//! array's elements at the element SORT's width. That is right only for a
//! layout rustc did not reorder. `repr(Rust)` makes no such promise:
//! `struct P { x: u8, y: u32 }` is laid out `y@0, x@4`, so
//! `static SP: P = P { x: 1, y: 10 }` decoded as `x = 10, y = 0`. Every
//! struct or tuple static whose fields rustc reorders, and every array of them,
//! started from a wrong initial value: `assert!(SP.x == 10)` verified
//! SUCCESSFUL (a missed bug) and `assert!(SP.x == 1)` was certified Genuine.
//! It was the root cause of `safe_nested_field_addr` in the review of
//! fix/chc-lost-writes round 7 (finding 3). This reader takes each field at its
//! ABI offset and each element at the element's stride, and flattens a
//! datatype element the way `translate_ty` flattens array elements.
//!
//! # The image decomposition
//!
//! `register_static_memory_init_entries` seeds a static's memory image and
//! `write_static_image` writes it under exactly the fields
//! [`ChcCtx::static_image_fields`] returns; the untyped-view net 2 asks the
//! same function which field views are seeded. One function keeps the three
//! from disagreeing.

#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use ay_bindings::{Expr, Sort};
use rustc_public::ty::{AdtKind, RigidTy, Ty, TyKind};

use super::ChcCtx;
use super::codegen_decl_static_alloc::declared_field_tys_for_sort;
use super::codegen_types::CodegenTypes;
use crate::codegen_ay::shared::const_pointer::ConstRead;
use crate::codegen_ay::shared::mono_ty;

/// Nesting the layout reader follows.
const MAX_LAYOUT_DEPTH: usize = 12;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// A static's declared type as a body sees it: regions erased and
    /// constants evaluated (`[(u64, u64); SIZE1]` is `[(u64, u64); 1]`).
    pub(in crate::codegen_ay::chc) fn normalize_static_ty(&self, ty: Ty) -> Ty {
        let internal = rustc_public::rustc_internal::internal(self.tcx, ty);
        // Trust takes the value to normalize wrapped in `Unnormalized`, a
        // marker with no effect on the value; nightly takes it bare.
        #[cfg(trust_toolchain)]
        let to_normalize = rustc_middle::ty::Unnormalized::new(internal);
        #[cfg(not(trust_toolchain))]
        let to_normalize = internal;
        let normalized = self
            .tcx
            .try_normalize_erasing_regions(
                rustc_middle::ty::TypingEnv::fully_monomorphized(),
                to_normalize,
            )
            .unwrap_or_else(|_| self.tcx.erase_and_anonymize_regions(internal));
        rustc_public::rustc_internal::stable(normalized)
    }

    /// Read the value of type `ty` (encoded as `sort`) at byte `offset` of a
    /// static's initializer by `ty`'s layout. `None`: not decodable exactly
    /// (the static is then left unconstrained, a counted sound widening).
    ///
    /// The bytes are a [`ConstRead`]: every leaf is read under the slot
    /// clause of `shared::const_pointer` (`read_composite_from_allocation`),
    /// so a pointer slot is its relocation's address, never its offset bytes,
    /// and a read that overlaps a relocation otherwise declines.
    pub(in crate::codegen_ay::chc) fn read_static_value_by_layout(
        &mut self,
        alloc: &dyn ConstRead,
        offset: usize,
        ty: Ty,
        sort: &Sort,
        depth: usize,
    ) -> Option<Expr> {
        use crate::codegen_ay::chc::expr::codegen_expr_constant_payload::{
            fieldless_enum_const_bits, ty_is_fieldless_enum,
        };

        if depth > MAX_LAYOUT_DEPTH {
            return None;
        }
        let ty = if depth == 0 { self.normalize_static_ty(ty) } else { ty };
        // Decode the same authenticated carrier that the memory image uses.
        // An erased UnsafeCell layer must not send a reordered struct to the
        // sequential fallback while its fields are seeded at ABI offsets.
        // Scalar and array slots retain their existing byte readers; do not
        // impose the datatype carrier's wrapper-depth limit on those reads.
        let mut ty = if sort.is_datatype() { self.static_image_value_carrier(ty)? } else { ty };

        // Decode the same exact content whose views the memory image exposes.
        // A collapsed UnsafeCell<Pt> has Pt's constructor, not UnsafeCell's
        // declared `value` field. Falling through to the sequential reader
        // would then lose Pt's real (possibly reordered) field offsets. The
        // shared guard proves this field occupies the SAME window and sort;
        // retain the caller's offset, including for nested array content.
        // Every step is a proper declared field of a positive-sized Rust
        // value, at the same offset, size and canonical sort. These erased
        // layers do not add value structure, so peel them iteratively without
        // spending the composite recursion budget. The terminal type still
        // selects the enum-tag or ABI-stride decoder below; a bitvector sort
        // alone does not mean raw bytes (fieldless enums and flattened array
        // elements also have bitvector sorts).
        while let Some(content) = self.static_image_collapsed_field(ty, sort) {
            ty = if sort.is_datatype() {
                self.static_image_value_carrier(content)?
            } else {
                content
            };
        }

        // A fieldless enum is its discriminant at the sort's width, from its
        // own tag bytes (a one-byte tag behind a wider sort).
        if let Some(width) = sort.bitvec_width()
            && ty_is_fieldless_enum(ty)
        {
            let value = fieldless_enum_const_bits(ty, alloc, offset, width)?;
            return Some(Expr::bitvec_const(value, width));
        }

        let elem_and_len = match ty.kind() {
            TyKind::RigidTy(RigidTy::Array(elem_ty, len)) => {
                Some((elem_ty, Some(len.eval_target_usize().ok()? as usize)))
            }
            TyKind::RigidTy(RigidTy::Slice(elem_ty)) => Some((elem_ty, None)),
            _ => None,
        };
        if let (Some((elem_ty, len)), Some(arr)) = (elem_and_len, sort.array_sort()) {
            // Pointer elements keep the pointer-element reader at the top level
            // (`static_init_from_alloc`); nested ones the sequential reader,
            // whose leaves obey the slot clause.
            if matches!(elem_ty.kind(), TyKind::RigidTy(RigidTy::Ref(..) | RigidTy::RawPtr(..))) {
                return self.read_composite_from_allocation(alloc, offset, sort);
            }
            let stride = self.get_type_size(elem_ty)?;
            if stride == 0 {
                return self.read_composite_from_allocation(alloc, offset, sort);
            }
            let len = match len {
                Some(len) => len,
                None => alloc.len().saturating_sub(offset) / stride,
            };
            if len == 0 {
                return None;
            }
            let elem_sort = arr.element_sort.clone();
            // `translate_ty` flattens a datatype element to a bitvector: read it
            // as the datatype, by its own layout, and flatten it the same way.
            let datatype_elem = elem_sort.bitvec_width().and_then(|w| {
                Self::translate_ty(elem_ty).filter(Sort::is_datatype).map(|s| (s, w))
            });
            let idx_width =
                arr.index_sort.bitvec_width().unwrap_or(crate::codegen_ay::types::POINTER_WIDTH);
            let mut result =
                Expr::const_array(arr.index_sort.clone(), Self::sort_default_expr(&elem_sort)?);
            for i in 0..len {
                let at = offset + i * stride;
                let elem = match &datatype_elem {
                    Some((dt_sort, width)) => {
                        let value = self.read_static_value_by_layout(
                            alloc,
                            at,
                            elem_ty,
                            dt_sort,
                            depth + 1,
                        )?;
                        let flat =
                            crate::codegen_ay::types::flatten_datatype_to_bitvec(&value, *width)?;
                        self.declare_datatype_sort_if_needed(dt_sort);
                        flat
                    }
                    None => {
                        self.read_static_value_by_layout(alloc, at, elem_ty, &elem_sort, depth + 1)?
                    }
                };
                result = result.store(Expr::bitvec_const(i as u128, idx_width), elem);
            }
            return Some(result);
        }

        // A struct or tuple of the generic per-declared-field encoding: each
        // field at its ABI offset.
        if let Some(dt) = sort.datatype_sort()
            && let [ctor] = dt.constructors.as_slice()
            && let Some(field_tys) = declared_field_tys_for_sort(ty, ctor)
        {
            let layout = crate::kani_middle::abi::LayoutOf::new(ty);
            let mut fields = Vec::with_capacity(ctor.fields.len());
            for (i, (sort_field, field_ty)) in ctor.fields.iter().zip(field_tys).enumerate() {
                let field_offset = layout.field_offset(i)?;
                fields.push(self.read_static_value_by_layout(
                    alloc,
                    offset + field_offset,
                    field_ty,
                    &sort_field.sort,
                    depth + 1,
                )?);
            }
            return Some(Expr::datatype_constructor(&*dt.name, &*ctor.name, fields, sort.clone()));
        }

        // Leaves, and encodings whose fields are not the declared ones.
        self.read_composite_from_allocation(alloc, offset, sort)
    }

    /// The content type the memory image of an IMMUTABLE static decomposes a
    /// value of wrapper type `ty` as: `T` for `MaybeUninit<T>` or
    /// `ManuallyDrop<T>` (nested wrappers unwrapped), when the wrapper is laid
    /// out and encoded exactly like `T` (same size, same sort) and `T` has no
    /// interior mutability. `None`: `ty` is decomposed as itself.
    ///
    /// `MaybeUninit` is a union, which [`Self::static_image_fields`] does not
    /// decompose, while the typed memory keys it like its content: a
    /// `MaybeUninit<[u16; 2]>` static read through `as_ptr()` as a `u16`
    /// selected an element cell the entry rule never seeded, a free value
    /// certified Genuine (review of fix/chc-lost-writes round 3, finding 2).
    /// The entry rule now seeds such a static's content cells, and the
    /// untyped-view net 2 counts the content's views as seeded, both through
    /// here. A MUTABLE static is excluded on both sides: its image writer
    /// (`static_image.rs`) writes a non-array static under its own key only, so
    /// seeded content cells would go stale after a store.
    pub(in crate::codegen_ay::chc) fn static_image_wrapper_content(&self, ty: Ty) -> Option<Ty> {
        use rustc_public::CrateDef;
        use rustc_public::ty::GenericArgKind;
        let size = self.get_type_size(ty)?;
        let sort = Self::translate_ty(ty)?;
        let mut content = ty;
        for _ in 0..4 {
            let TyKind::RigidTy(RigidTy::Adt(def, args)) = content.kind() else { break };
            if !matches!(def.trimmed_name().as_str(), "MaybeUninit" | "ManuallyDrop") {
                break;
            }
            let Some(GenericArgKind::Type(inner)) = args.0.first() else { break };
            content = *inner;
        }
        (content != ty
            && self.get_type_size(content) == Some(size)
            && Self::translate_ty(content).as_ref() == Some(&sort)
            && !self.ty_has_interior_mut(content))
        .then_some(content)
    }

    /// A declared field whose value IS the encoding of its whole owner.
    ///
    /// A collapsed wrapper's datatype belongs to its content, not the wrapper:
    /// `UnsafeCell<Align4<u32>>` has Align4's `fld_0` constructor, whereas its
    /// own declared field is `value`. Matching those names loses the inner
    /// u32 view. Peel only an actual sole field at offset zero that fills the
    /// allocation and already has the same canonical sort. This does not
    /// flatten a new datatype or infer any permission to access the storage.
    fn static_image_collapsed_field(&self, ty: Ty, sort: &Sort) -> Option<Ty> {
        let ty = self.resolve_body_ty(ty);
        let field_ty = match ty.kind() {
            TyKind::RigidTy(RigidTy::Adt(def, args)) if def.kind() == AdtKind::Struct => {
                mono_ty::single_field_storage_ty(def, &args)?
            }
            TyKind::RigidTy(RigidTy::Tuple(fields)) => {
                let [field] = fields.as_slice() else { return None };
                *field
            }
            _ => return None,
        };
        let layout = crate::kani_middle::abi::LayoutOf::new(ty);
        let size = layout.size_of()?;
        if field_ty == ty
            || size == 0
            || layout.field_offset(0)? != 0
            || crate::kani_middle::abi::LayoutOf::new(field_ty).size_of() != Some(size)
            || Self::translate_ty(ty).as_ref() != Some(sort)
            || Self::translate_ty(field_ty).as_ref() != Some(sort)
        {
            return None;
        }
        Some(field_ty)
    }

    /// How the static's memory image decomposes a value of type `ty` whose
    /// image sort is `sort` (the datatype, or the flattened bitvector of an
    /// array element): the datatype sort, and `(field type, field sort, byte
    /// offset)` for each field of a struct or a tuple of the generic
    /// per-declared-field encoding. `None`: the value is held whole only.
    /// [`Self::static_image_fields`] (the entry rule's seeding and
    /// `write_static_image`) and the untyped-view net 2 both go through here.
    pub(in crate::codegen_ay::chc) fn static_image_field_views(
        &self,
        ty: Ty,
        sort: &Sort,
    ) -> Option<Vec<(Ty, Sort, u64)>> {
        let ty = self.static_image_value_carrier(self.resolve_body_ty(ty))?;
        if let Some(field_ty) = self.static_image_collapsed_field(ty, sort) {
            return Some(vec![(field_ty, sort.clone(), 0)]);
        }
        self.static_image_decomposition(ty, sort).map(|(_, fields)| fields)
    }

    /// The declared carrier of a value after genuinely erased transparent
    /// layers. For example, `UnsafeCell<Align4<u32>>` has the Align4 datatype
    /// sort: its image fields belong to Align4, not UnsafeCell. A memory-key
    /// peel alone is insufficient here (it also covers pointer wrappers), so
    /// require an actual transparent struct payload at byte zero, occupying
    /// the whole object, in addition to the shared sort-equality predicate.
    fn static_image_value_carrier(&self, mut ty: Ty) -> Option<Ty> {
        for _ in 0..MAX_LAYOUT_DEPTH {
            let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() else {
                return Some(ty);
            };
            if def.kind() != AdtKind::Struct || !def.repr().flags.is_transparent {
                return Some(ty);
            }
            let Some(peeled) = Self::representation_peel(ty) else { return Some(ty) };
            let peeled = self.resolve_body_ty(peeled);
            let layout = ty.layout().ok()?;
            let payload_layout = peeled.layout().ok()?;
            if !layout.shape().is_sized()
                || !payload_layout.shape().is_sized()
                || layout.shape().size != payload_layout.shape().size
            {
                return Some(ty);
            }
            let rustc_public::abi::FieldsShape::Arbitrary { offsets } = layout.shape().fields
            else {
                return Some(ty);
            };
            let variants = def.variants();
            let [variant] = variants.as_slice() else { return Some(ty) };
            let mut payload = None;
            for (index, field) in variant.fields().iter().enumerate() {
                let field_ty = crate::codegen_ay::shared::mono_ty::field_ty(field, &args)?;
                let field_layout = field_ty.layout().ok()?;
                if !field_layout.shape().is_sized() {
                    return Some(ty);
                }
                if field_layout.shape().size.bytes() == 0 {
                    continue;
                }
                if payload.is_some() {
                    return Some(ty);
                }
                payload = Some((index, self.resolve_body_ty(field_ty)));
            }
            let Some((index, field_ty)) = payload else { return Some(ty) };
            if field_ty != peeled || offsets.get(index)?.bytes() != 0 {
                return Some(ty);
            }
            ty = peeled;
        }
        None
    }

    fn static_image_decomposition(
        &self,
        ty: Ty,
        sort: &Sort,
    ) -> Option<(Sort, Vec<(Ty, Sort, u64)>)> {
        let ty = self.static_image_value_carrier(self.resolve_body_ty(ty))?;
        let struct_or_tuple = match ty.kind() {
            TyKind::RigidTy(RigidTy::Adt(def, _)) => {
                def.kind() == AdtKind::Struct && def.variants().len() == 1
            }
            TyKind::RigidTy(RigidTy::Tuple(tys)) => !tys.is_empty(),
            _ => false,
        };
        if !struct_or_tuple {
            return None;
        }
        let dt_sort = if sort.is_datatype() {
            sort.clone()
        } else if sort.is_bitvec() {
            // An array element: the flattened datatype `try_unflatten_bv_to_datatype`
            // rebuilds.
            let dt_sort = Self::translate_ty(ty).filter(Sort::is_datatype)?;
            let probe = Expr::var("__static_image_probe", sort.clone());
            crate::codegen_ay::types::unflatten_bitvec_to_datatype(&probe, &dt_sort)?;
            dt_sort
        } else {
            return None;
        };
        let dt = dt_sort.datatype_sort()?;
        let [ctor] = dt.constructors.as_slice() else { return None };
        let field_tys = declared_field_tys_for_sort(ty, ctor)?;
        let layout = ty.layout().ok()?;
        let rustc_public::abi::FieldsShape::Arbitrary { offsets } = layout.shape().fields else {
            return None;
        };
        let mut fields = Vec::with_capacity(field_tys.len());
        for (idx, (field, field_ty)) in ctor.fields.iter().zip(field_tys).enumerate() {
            let offset = offsets.get(idx)?.bytes() as u64;
            // A declared field may itself erase a transparent layer. Expose
            // its actual datatype carrier at the same ABI window, so the
            // next decomposition selects that carrier's declared fields.
            // Direct collapsed-owner views above still retain the whole value.
            let field_ty = if field.sort.is_datatype() {
                let carrier = self.static_image_value_carrier(self.resolve_body_ty(field_ty))?;
                if Self::translate_ty(carrier).as_ref() != Some(&field.sort) {
                    return None;
                }
                carrier
            } else {
                field_ty
            };
            fields.push((field_ty, field.sort.clone(), offset));
        }
        Some((dt_sort.clone(), fields))
    }

    /// The fields the static's memory image holds a `value` of type `ty` as,
    /// besides the value itself under `ty`'s own key: `(field type, field
    /// value, byte offset)` (see [`Self::static_image_field_views`]).
    pub(in crate::codegen_ay::chc) fn static_image_fields(
        &mut self,
        ty: Ty,
        value: &Expr,
    ) -> Option<Vec<(Ty, Expr, u64)>> {
        let ty = self.static_image_value_carrier(self.resolve_body_ty(ty))?;
        if let Some(field_ty) = self.static_image_collapsed_field(ty, value.sort()) {
            return Some(vec![(field_ty, value.clone(), 0)]);
        }
        let (dt_sort, fields) = self.static_image_decomposition(ty, value.sort())?;
        let value = if value.sort().is_datatype() {
            value.clone()
        } else {
            let resolved = self.static_image_value_carrier(self.resolve_body_ty(ty))?;
            let unflat = self.try_unflatten_bv_to_datatype(value.clone(), resolved);
            if *unflat.sort() != dt_sort {
                return None;
            }
            unflat
        };
        let dt = dt_sort.datatype_sort()?;
        let [ctor] = dt.constructors.as_slice() else { return None };
        Some(
            ctor.fields
                .iter()
                .zip(fields)
                .map(|(field, (field_ty, _, offset))| {
                    let field_value =
                        value.clone().field_select(&dt.name, &field.name, field.sort.clone());
                    (field_ty, field_value, offset)
                })
                .collect(),
        )
    }
}
