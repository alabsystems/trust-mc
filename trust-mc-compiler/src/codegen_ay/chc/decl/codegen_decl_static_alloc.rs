// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Allocation-aware readers and sort utilities for static/const decoding.
//! Split from `codegen_decl_static.rs` for file-size compliance (Part of #4196).
//! Contains: provenance-aware readers, `scalar_from_alloc`, `read_composite_from_bytes`,
//! `sort_byte_width`, `sort_alignment`, `sort_default_expr`, pointer resolution helpers.

use crate::codegen_ay::shared::mono_ty;
#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;

use crate::codegen_ay::provenance::{Loc, Val};
use crate::codegen_ay::ptr_repr::{PtrRepr, PtrSlot};
use crate::codegen_ay::shared::const_pointer::{self, ConstRead, Slot};

use super::ChcCtx;

/// A scalar decoded out of a static / const **allocation**.
///
/// # The one place the missing fact is already recorded
///
/// Everywhere else in `codegen_ay`, "is this bitvector an address or a value?"
/// has to be re-derived from a width test because the producer's knowledge was
/// dropped. Here it was never dropped in the first place: a `rustc_public`
/// `Allocation` carries `provenance.ptrs`, a table of `(byte offset, AllocId)`
/// pairs naming exactly which byte ranges of the initializer image hold
/// **pointers**. The remaining bytes are plain data by construction — that is
/// what makes const-eval's own relocation model work.
///
/// So the static decoder does not have to guess, and this type stops it from
/// guessing: [`ChcCtx::read_scalar_from_allocation`] consults the provenance
/// table and reports what it found, instead of returning one more anonymous
/// `Expr` for the next consumer to width-test.
///
/// # Why the pointer arm carries a [`PtrRepr`] rather than a [`Loc`]
///
/// A reference-typed slot in a static can be either one word (`&i32`) or two
/// (`&str`, `&[T]`, `&dyn Tr`), and the wide form is an address *and* a value
/// packed together — precisely the asymmetry [`PtrRepr`] exists to express.
/// Keeping the halves apart until [`AllocScalar::into_expr`] means the
/// `[metadata : upper | data : lower]` order is stated once, by
/// [`PtrRepr::into_packed`], instead of being re-asserted by a hand-rolled
/// `concat` at each decode site.
pub(in crate::codegen_ay::chc) enum AllocScalar {
    /// The allocation's provenance table declares a pointer covering this read.
    Ptr(PtrRepr),
    /// Plain initializer bytes: an integer, a bool, a float's bit pattern, or a
    /// fragment of a pointer too narrow to denote the pointer itself.
    Value(Val),
}

impl AllocScalar {
    /// Drops the tag and hands back the underlying expression.
    ///
    /// Every call site is a boundary with code this wave did not convert (the
    /// recursive composite readers, which build aggregates out of leaves).
    pub(in crate::codegen_ay::chc) fn into_expr(self) -> ay_bindings::Expr {
        match self {
            Self::Value(val) => val.into_expr(),
            // Only `Thin` and `Fat` are ever constructed here; `into_packed`
            // returns `None` for the metadata-free shapes, which is exactly the
            // case where the address alone is the whole expression.
            Self::Ptr(repr) => match repr.clone().into_packed() {
                Some(packed) => packed,
                None => repr.into_data().into_expr(),
            },
        }
    }
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Reads `width` bits at byte `offset` of constant bytes under the slot
    /// clause (`shared::const_pointer`), tagged with what the bytes are.
    ///
    /// # What decides the tag
    ///
    /// The relocation table, not the width. A pointer-width read starting
    /// exactly at a relocation is that POINTER: its target's one object base
    /// plus the offset its bytes carry (`const_ptr_address`), or a function's
    /// identity. The relocated bytes themselves are never data: they hold only
    /// the offset, and reading them as the value made a pointer stored in a
    /// constant VALUE decode to `concat(0, offset)` — object 0, the null object
    /// (`PTRS[0].is_null()` PROVED). A read that overlaps a relocation without
    /// being exactly it declines, and so does a pointer whose target has no
    /// object here.
    ///
    /// Uninitialized bytes of a data read are read as 0: the zeroed static
    /// image Kani/CBMC give padding (unchanged; its own audit item).
    pub(in crate::codegen_ay::chc) fn read_scalar_from_allocation(
        &self,
        bytes: &dyn ConstRead,
        offset: usize,
        width: u32,
    ) -> Option<AllocScalar> {
        if width == 0 || width % 8 != 0 || width > 128 {
            return None;
        }
        let mask = |value: u128| if width >= 128 { value } else { value & ((1u128 << width) - 1) };
        match bytes.read_slot(offset, width) {
            Slot::Pointer(ptr) => {
                Some(AllocScalar::Ptr(PtrRepr::Thin(self.const_ptr_address(&ptr)?)))
            }
            Slot::Data(value) => Some(AllocScalar::Value(Val::of_value(
                ay_bindings::Expr::bitvec_const(mask(value), width),
            ))),
            Slot::Uninit => {
                let value = bytes.read_uint_zero_filled(offset, width)?;
                Some(AllocScalar::Value(Val::of_value(ay_bindings::Expr::bitvec_const(
                    mask(value),
                    width,
                ))))
            }
            Slot::PartialPointer | Slot::OutOfBounds => None,
        }
    }

    /// Read a single-variant ADT constant out of an allocation using the
    /// **real ABI field offsets** instead of declaration-order packing.
    ///
    /// `read_composite_from_allocation` walks a Datatype sort's fields in
    /// declaration order and advances a running offset by each field's width.
    /// That is only correct for a layout rustc did not reorder. `repr(Rust)`
    /// makes no such promise, and it really does reorder: `RangeInclusive<u8>`
    /// is declared `{ start, end, exhausted }` but laid out
    /// `start@0, exhausted@1, end@2`, so the sequential reader decoded the
    /// constant `0..=1` as `start=0, end=0, exhausted=true` — a range that
    /// contains nothing.
    ///
    /// This reader asks rustc for `field_offset(i)` and reads each field there,
    /// recursing so nested ADT fields are decoded by their own layout too. It
    /// applies ONLY when the Datatype sort's constructor is the generic
    /// per-declared-field encoding (same field count, `fld_<name>` names from
    /// `adt_struct_field_name`); the specialised sorts (String, Vec, IndexRange,
    /// dyn fat pointers, …) do not describe declared fields and fall back to the
    /// sequential reader unchanged.
    pub(in crate::codegen_ay::chc) fn read_adt_composite_from_allocation(
        &self,
        alloc: &dyn ConstRead,
        offset: usize,
        ty: rustc_public::ty::Ty,
        sort: &ay_bindings::Sort,
    ) -> Option<ay_bindings::Expr> {
        let sequential = || self.read_composite_from_allocation(alloc, offset, sort);

        // A fieldless enum is its discriminant at the sort's width, decoded from
        // its own tag bytes: `Ordering` is one byte behind a BV32 sort, and the
        // width-based leaf reader took the neighbouring bytes with it.
        if let Some(width) = sort.bitvec_width()
            && crate::codegen_ay::chc::expr::codegen_expr_constant_payload::ty_is_fieldless_enum(ty)
        {
            let value =
                crate::codegen_ay::chc::expr::codegen_expr_constant_payload::fieldless_enum_const_bits(
                    ty,
                    alloc,
                    offset,
                    width,
                )?;
            return Some(ay_bindings::Expr::bitvec_const(value, width));
        }

        let Some(dt) = sort.datatype_sort() else { return sequential() };
        let Some(ctor) = dt.constructors.first() else { return sequential() };
        if dt.constructors.len() != 1 {
            return sequential();
        }
        // Per-declared-field types, in the order the Datatype sort declares its
        // fields. `None` means the sort is one of the specialised encodings
        // (String, Vec, IndexRange, dyn fat pointer, …) whose fields do not
        // correspond to declared fields — those keep the sequential reader.
        let Some(field_tys) = declared_field_tys_for_sort(ty, ctor) else { return sequential() };

        let layout = crate::kani_middle::abi::LayoutOf::new(ty);
        let mut field_exprs = Vec::with_capacity(ctor.fields.len());
        for (i, (sort_field, field_ty)) in ctor.fields.iter().zip(field_tys.iter()).enumerate() {
            // No `Arbitrary` field shape (unions, primitives) means there are no
            // offsets to trust: fall back rather than invent one.
            let Some(field_offset) = layout.field_offset(i) else { return sequential() };
            field_exprs.push(self.read_adt_composite_from_allocation(
                alloc,
                offset + field_offset,
                *field_ty,
                &sort_field.sort,
            )?);
        }
        Some(ay_bindings::Expr::datatype_constructor(
            &*dt.name,
            &*ctor.name,
            field_exprs,
            sort.clone(),
        ))
    }

    /// Reads a composite constant under the slot clause: every leaf goes
    /// through [`Self::read_scalar_from_allocation`], so a pointer leaf is its
    /// relocation's address, never its offset bytes.
    pub(in crate::codegen_ay::chc) fn read_composite_from_allocation(
        &self,
        alloc: &dyn ConstRead,
        offset: usize,
        sort: &ay_bindings::Sort,
    ) -> Option<ay_bindings::Expr> {
        use ay_bindings::Expr;

        if sort.is_bool() {
            // A trailing zero-sized field can place a bool leaf past the real
            // bytes (offset >= bytes.len()). Default such an out-of-bytes read
            // to `false` instead of failing the `?` — otherwise the whole
            // composite read bails and the (already-proven) value is spuriously
            // demoted via chc_fallback. Interior in-bounds reads are unchanged.
            // A byte a relocation covers is not a bool.
            let byte_val = match alloc.read_slot(offset, 8) {
                Slot::Data(b) => b,
                Slot::Uninit | Slot::OutOfBounds => 0,
                Slot::Pointer(_) | Slot::PartialPointer => return None,
            };
            return Some(Expr::bool_const(byte_val != 0));
        }
        if let Some(width) = sort.bitvec_width() {
            // Boundary with the untyped recursive readers: a composite is
            // assembled out of leaves, and a datatype constructor has no slot to
            // record which of its fields were relocations.
            return self
                .read_scalar_from_allocation(alloc, offset, width)
                .map(AllocScalar::into_expr);
        }

        if let Some(arr) = sort.array_sort() {
            let elem_width = Self::sort_byte_width(&arr.element_sort)?;
            if elem_width == 0 {
                return None;
            }
            let remaining = alloc.len().saturating_sub(offset);
            let array_len = remaining / elem_width;
            if array_len == 0 {
                return None;
            }
            let default_elem = Self::sort_default_expr(&arr.element_sort)?;
            let mut result = Expr::const_array(arr.index_sort.clone(), default_elem);
            let idx_width =
                arr.index_sort.bitvec_width().unwrap_or(crate::codegen_ay::types::POINTER_WIDTH);
            for i in 0..array_len {
                let elem_offset = offset + i * elem_width;
                let elem =
                    self.read_composite_from_allocation(alloc, elem_offset, &arr.element_sort)?;
                let idx = Expr::bitvec_const(i as u128, idx_width);
                result = result.store(idx, elem);
            }
            return Some(result);
        }

        if let Some(dt) = sort.datatype_sort() {
            let ctor = dt.constructors.first()?;
            if dt.constructors.len() != 1 {
                return None;
            }
            let mut field_exprs = Vec::with_capacity(ctor.fields.len());
            let mut field_offset = offset;
            for (i, field) in ctor.fields.iter().enumerate() {
                let align = Self::sort_alignment(&field.sort)?;
                field_offset = field_offset.div_ceil(align) * align;
                let field_expr =
                    self.read_composite_from_allocation(alloc, field_offset, &field.sort)?;
                field_exprs.push(field_expr);
                if i + 1 < ctor.fields.len() {
                    let fw = Self::sort_byte_width(&field.sort)?;
                    field_offset += fw;
                }
            }
            return Some(Expr::datatype_constructor(
                &*dt.name,
                &*ctor.name,
                field_exprs,
                sort.clone(),
            ));
        }

        None
    }

    /// Read a AY expression from a constant's bytes + sort (scalar or
    /// composite), under the slot clause: a pointer-bearing image is not
    /// read byte-wise at all (its caller reads it at layout offsets with its
    /// pointer slots resolved, `read_adt_composite_from_allocation`).
    /// Part of #3496 Bug A.
    pub(in crate::codegen_ay::chc) fn scalar_from_alloc(
        bytes: &dyn ConstRead,
        sort: &ay_bindings::Sort,
    ) -> Option<ay_bindings::Expr> {
        use ay_bindings::Expr;

        if sort.is_bool() {
            if bytes.len() != 1 {
                return None;
            }
            return Some(Expr::bool_const(bytes.read_bool_at(0)?));
        }
        if let Some(width) = sort.bitvec_width() {
            if let Some(value) = bytes.read_uint_at(0, bytes.len()) {
                let masked = if width >= 128 { value } else { value & ((1u128 << width) - 1) };
                return Some(Expr::bitvec_const(masked, width));
            }
            // An uninitialized byte — which union statics routinely contain
            // (const-eval leaves padding uninit, e.g. `static FOO: Data = Data
            // { a: [0, 1, 0] }` in a 4-byte union): the byte-wise reader below
            // zero-fills it, matching Kani/CBMC static-image semantics (the
            // zeroed binary image; union_transmute's oracle y == 256 REQUIRES
            // padding == 0). A pointer-bearing image has no byte view and
            // bails to the static_init_incomplete demotion.
            return Self::read_composite_from_bytes(&bytes.data_image()?, 0, sort);
        }
        if sort.is_int() {
            return Some(Expr::int_const(bytes.read_int_at(0, bytes.len())?));
        }

        // Composite types: read from the image at offsets.
        Self::read_composite_from_bytes(&bytes.data_image()?, 0, sort)
    }

    /// Read a AY value from raw bytes at a byte offset (recursive decomposition).
    /// Part of #3496 Bug A.
    pub(in crate::codegen_ay::chc) fn read_composite_from_bytes(
        bytes: &[Option<u8>],
        offset: usize,
        sort: &ay_bindings::Sort,
    ) -> Option<ay_bindings::Expr> {
        use ay_bindings::Expr;

        if sort.is_bool() {
            // Mirror of read_composite_from_allocation: tolerate a trailing-ZST
            // bool leaf past the real bytes (default false) rather than bailing.
            let byte_val: u8 = match bytes.get(offset).copied() {
                Some(b) => b.unwrap_or(0),
                None => 0,
            };
            return Some(Expr::bool_const(byte_val != 0));
        }
        if let Some(width) = sort.bitvec_width() {
            let byte_width = width as usize / 8;
            let mut value: u128 = 0;
            for b in 0..byte_width {
                let byte_val: u8 = bytes.get(offset + b).copied()?.unwrap_or(0);
                value |= (byte_val as u128) << (b * 8);
            }
            let masked = if width >= 128 { value } else { value & ((1u128 << width) - 1) };
            return Some(Expr::bitvec_const(masked, width));
        }

        // Array: read elements sequentially from bytes.
        if let Some(arr) = sort.array_sort() {
            let elem_width = Self::sort_byte_width(&arr.element_sort)?;
            if elem_width == 0 {
                return None;
            }
            let remaining = bytes.len().saturating_sub(offset);
            let array_len = remaining / elem_width;
            if array_len == 0 {
                return None;
            }
            let default_elem = Self::sort_default_expr(&arr.element_sort)?;
            let mut result = Expr::const_array(arr.index_sort.clone(), default_elem);
            let idx_width =
                arr.index_sort.bitvec_width().unwrap_or(crate::codegen_ay::types::POINTER_WIDTH);
            for i in 0..array_len {
                let elem_offset = offset + i * elem_width;
                let elem = Self::read_composite_from_bytes(bytes, elem_offset, &arr.element_sort)?;
                let idx = Expr::bitvec_const(i as u128, idx_width);
                result = result.store(idx, elem);
            }
            return Some(result);
        }

        // Datatype (single-constructor struct): read fields at computed offsets.
        if let Some(dt) = sort.datatype_sort() {
            let ctor = dt.constructors.first()?;
            if dt.constructors.len() != 1 {
                return None;
            }
            let mut field_exprs = Vec::with_capacity(ctor.fields.len());
            let mut field_offset = offset;
            for (i, field) in ctor.fields.iter().enumerate() {
                let align = Self::sort_alignment(&field.sort)?;
                field_offset = field_offset.div_ceil(align) * align;
                let field_expr = Self::read_composite_from_bytes(bytes, field_offset, &field.sort)?;
                field_exprs.push(field_expr);
                // Only advance offset when there are more fields to read.
                // Array sorts have no fixed byte width (abstract maps), so
                // sort_byte_width returns None for them. Part of #3806.
                if i + 1 < ctor.fields.len() {
                    let fw = Self::sort_byte_width(&field.sort)?;
                    field_offset += fw;
                }
            }
            return Some(Expr::datatype_constructor(
                &*dt.name,
                &*ctor.name,
                field_exprs,
                sort.clone(),
            ));
        }

        None
    }

    /// Compute byte width of a AY sort for allocation reading.
    pub(in crate::codegen_ay::chc) fn sort_byte_width(sort: &ay_bindings::Sort) -> Option<usize> {
        if sort.is_bool() {
            return Some(1);
        }
        if let Some(width) = sort.bitvec_width() {
            return Some(width as usize / 8);
        }
        if let Some(dt) = sort.datatype_sort() {
            let ctor = dt.constructors.first()?;
            if dt.constructors.len() != 1 {
                return None;
            }
            let mut total = 0usize;
            for field in &ctor.fields {
                let align = Self::sort_alignment(&field.sort)?;
                total = total.div_ceil(align) * align;
                total += Self::sort_byte_width(&field.sort)?;
            }
            return Some(total);
        }
        None
    }

    /// Compute alignment of a AY sort in bytes.
    pub(in crate::codegen_ay::chc) fn sort_alignment(sort: &ay_bindings::Sort) -> Option<usize> {
        if sort.is_bool() {
            return Some(1);
        }
        if let Some(width) = sort.bitvec_width() {
            return Some((width as usize / 8).clamp(1, 16));
        }
        // Array: align to element alignment. Part of #3806.
        if let Some(arr) = sort.array_sort() {
            return Self::sort_alignment(&arr.element_sort);
        }
        if let Some(dt) = sort.datatype_sort() {
            let ctor = dt.constructors.first()?;
            let mut max_align = 1usize;
            for field in &ctor.fields {
                max_align = max_align.max(Self::sort_alignment(&field.sort)?);
            }
            return Some(max_align);
        }
        None
    }

    /// Default/zero expression for a sort. Used for const_array base values.
    pub(in crate::codegen_ay::chc) fn sort_default_expr(
        sort: &ay_bindings::Sort,
    ) -> Option<ay_bindings::Expr> {
        use ay_bindings::Expr;
        if sort.is_bool() {
            return Some(Expr::bool_const(false));
        }
        if let Some(width) = sort.bitvec_width() {
            return Some(Expr::bitvec_const(0u64, width));
        }
        if sort.is_int() {
            return Some(Expr::int_const(0));
        }
        None
    }

    pub(in crate::codegen_ay::chc) fn read_array_with_pointer_elements_from_allocation(
        &mut self,
        alloc: &dyn ConstRead,
        offset: usize,
        array_sort: &ay_bindings::Sort,
        elem_ty: rustc_public::ty::Ty,
        array_len: usize,
    ) -> Option<ay_bindings::Expr> {
        let arr = array_sort.array_sort()?;
        let elem_byte_width = Self::sort_byte_width(&arr.element_sort)?;
        if elem_byte_width == 0 {
            return None;
        }

        let default_elem = Self::sort_default_expr(&arr.element_sort)?;
        let mut result = ay_bindings::Expr::const_array(arr.index_sort.clone(), default_elem);
        let idx_width =
            arr.index_sort.bitvec_width().unwrap_or(crate::codegen_ay::types::POINTER_WIDTH);

        for i in 0..array_len {
            let elem_offset = offset + i * elem_byte_width;
            let elem = self.read_pointer_like_from_allocation(
                alloc,
                elem_offset,
                &arr.element_sort,
                elem_ty,
            )?;
            let idx = ay_bindings::Expr::bitvec_const(i as u128, idx_width);
            result = result.store(idx, elem.into_expr());
        }

        Some(result)
    }

    /// Decodes one reference/raw-pointer-typed slot of a static's initializer
    /// under the slot clause (`shared::const_pointer`).
    ///
    /// The slot is the relocation starting at `offset`: its value is the
    /// target's ONE object base plus the offset the slot's bytes carry
    /// (`const_ptr_address`), or a function's identity. The target is noted as
    /// read at the pointee type, so a fixed target is seeded whole (D2). A fat
    /// slot's metadata is the length word beside it, read as data.
    ///
    /// Before, the target was resolved through its own second mint site and
    /// decoded from its byte 0 at the POINTEE's size, and the pointer was the
    /// target's base: for `static R: &u32 = &ARR[1]`, `*R == 1` PROVED; and a
    /// slot whose target could not be resolved fell back to its own bytes —
    /// the offset read as an address in object 0.
    ///
    /// # What decides thin vs fat
    ///
    /// [`PtrSlot`], read off the sort `translate_ty` produced for `rust_ty` —
    /// i.e. off the *declaration*, never off a width.
    fn read_pointer_like_from_allocation(
        &mut self,
        alloc: &dyn ConstRead,
        offset: usize,
        sort: &ay_bindings::Sort,
        rust_ty: rustc_public::ty::Ty,
    ) -> Option<AllocScalar> {
        use rustc_public::ty::{RigidTy, TyKind};

        let TyKind::RigidTy(RigidTy::Ref(_, pointee_ty, _) | RigidTy::RawPtr(pointee_ty, _)) =
            rust_ty.kind()
        else {
            return self
                .read_composite_from_allocation(alloc, offset, sort)
                .map(|expr| AllocScalar::Value(Val::of_value(expr)));
        };

        let width = sort.bitvec_width()?;
        let Some(ptr) = alloc.stored_pointer(offset) else {
            // No relocation: an integer address (null, dangling), plain data.
            return self.read_scalar_from_allocation(alloc, offset, width);
        };
        let data_ptr = self.const_ptr_address(&ptr)?;
        if let Some(key) = ptr.key() {
            self.note_object_read(key, pointee_ty);
        }

        match PtrSlot::of_sort(sort) {
            Some(PtrSlot::Thin) => Some(AllocScalar::Ptr(PtrRepr::Thin(data_ptr))),
            Some(PtrSlot::Fat) => {
                // The metadata half is a length read out of plain bytes right
                // after the relocation — a value, and the only thing that keeps
                // it on the correct side of the packed word is
                // `PtrRepr::into_packed`, which states the byte order once.
                let len = alloc.stored_word(offset + const_pointer::PTR_BYTES)?;
                let meta = Val::of_value(ay_bindings::Expr::bitvec_const(
                    u128::from(len),
                    crate::codegen_ay::types::POINTER_WIDTH,
                ));
                Some(AllocScalar::Ptr(PtrRepr::from_declared_roles(data_ptr, meta)))
            }
            None => None,
        }
    }

    /// Resolve a pointer-typed static's initial value: the pointer its own
    /// bytes hold at offset 0 (`ptr`), which is the target's ONE object base
    /// plus the pointer's offset — never the target's base.
    ///
    /// For a FIXED pointer static whose target is fixed, the pointee's
    /// initial value (the WINDOW at the pointer's offset, decoded as
    /// `pointee_ty`) is recorded for the pointer-static load; a `static mut`
    /// pointer may be repointed and a live target may change, so neither
    /// records one (D7(c)).
    pub(in crate::codegen_ay::chc) fn resolve_pointer_static_init(
        &mut self,
        static_bytes: &dyn ConstRead,
        pointee_ty: rustc_public::ty::Ty,
        static_name: &str,
        vec_idx: usize,
        pointer_static_fixed: bool,
    ) -> Option<Loc> {
        let ptr = static_bytes.stored_pointer(0)?;
        let target_addr = self.const_ptr_address(&ptr)?;
        if let Some(key) = ptr.key() {
            self.note_object_read(key, pointee_ty);
        }
        // D7(c): only a FIXED pointer static still points where its
        // initializer pointed when it is loaded; a `static mut` pointer may
        // have been repointed (`PX2 = &raw mut Y2; *PX2 = 7` wrote X2's
        // allocation on this record), so it records neither its pointee's
        // allocation nor its value.
        if pointer_static_fixed {
            self.ref_resolution.static_pointee_addrs.insert(vec_idx, target_addr.as_expr().clone());
        }
        if pointer_static_fixed
            && let Some((_, init)) = self.fixed_window_value(static_bytes, 0, pointee_ty)
        {
            self.ref_resolution.static_pointee_init_values.insert(vec_idx, init);
        }
        tracing::debug!(
            vec_idx,
            static_name = %static_name,
            ?ptr,
            "CHC: resolved pointer static to its target object plus offset (#3496)"
        );
        Some(target_addr)
    }
}

/// The declared field types behind a Datatype sort's sole constructor, in the
/// constructor's field order — or `None` when the sort is not the generic
/// per-declared-field encoding of `ty`.
///
/// The name check is what makes the correspondence sound: `translate_adt_sort`
/// builds struct sorts by mapping declared field `f` to
/// `adt_struct_field_name(f)` in declaration order, and tuple sorts by mapping
/// element `i` to `tuple_field_name(i)`. Any sort whose field names do not
/// reproduce that mapping is a specialised encoding whose field `i` is NOT
/// declared field `i`, so its constant must not be decoded by ABI offsets.
pub(in crate::codegen_ay::chc) fn declared_field_tys_for_sort(
    ty: rustc_public::ty::Ty,
    ctor: &ay_bindings::DatatypeConstructor,
) -> Option<Vec<rustc_public::ty::Ty>> {
    use rustc_public::ty::{RigidTy, TyKind};

    match ty.kind() {
        TyKind::RigidTy(RigidTy::Adt(def, args)) => {
            let variants = def.variants();
            let [variant] = &variants[..] else { return None };
            let decl_fields = variant.fields();
            if ctor.fields.len() != decl_fields.len() {
                return None;
            }
            let matches = ctor.fields.iter().zip(decl_fields.iter()).all(|(sort_field, decl)| {
                *sort_field.name == *crate::codegen_ay::names::adt_struct_field_name(&decl.name)
            });
            if !matches {
                return None;
            }
            decl_fields.iter().map(|f| mono_ty::field_ty(f, &args)).collect::<Option<Vec<_>>>()
        }
        TyKind::RigidTy(RigidTy::Tuple(elem_tys)) => {
            if ctor.fields.len() != elem_tys.len() {
                return None;
            }
            let matches = ctor.fields.iter().enumerate().all(|(i, sort_field)| {
                *sort_field.name == *crate::codegen_ay::names::tuple_field_name(i)
            });
            if !matches {
                return None;
            }
            Some(elem_tys)
        }
        _ => None,
    }
}
