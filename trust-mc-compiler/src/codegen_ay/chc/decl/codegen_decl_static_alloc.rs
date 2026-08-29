// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Allocation-aware readers and sort utilities for static/const decoding.
//! Split from `codegen_decl_static.rs` for file-size compliance (Part of #4196).
//! Contains: provenance-aware readers, `scalar_from_alloc`, `read_composite_from_bytes`,
//! `sort_byte_width`, `sort_alignment`, `sort_default_expr`, pointer resolution helpers.

use rustc_public::mir::alloc::{AllocId, GlobalAlloc};

use crate::codegen_ay::provenance::{Loc, Val};
use crate::codegen_ay::ptr_repr::{PtrRepr, PtrSlot};

use super::ChcCtx;
use super::codegen_types::CodegenTypes;

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
    fn fn_ptr_identity_expr_from_key(key: &str) -> Loc {
        // Deterministic FNV-1a hash so const-provenance fn pointers get a
        // stable non-zero BV identity without depending on mutable ctx state.
        let mut hash: u64 = 0xcbf29ce484222325;
        for byte in key.as_bytes() {
            hash ^= u64::from(*byte);
            hash = hash.wrapping_mul(0x100000001b3);
        }
        if hash == 0 {
            hash = 1;
        }
        // A function's identity IS its address in this encoding: the hash is the
        // term every `fn` pointer to that instance compares equal to.
        Loc::of_address(ay_bindings::Expr::bitvec_const(
            hash as u128,
            crate::codegen_ay::types::POINTER_WIDTH,
        ))
    }

    pub(in crate::codegen_ay::chc) fn fn_ptr_identity_expr_from_alloc_id(
        alloc_id: AllocId,
    ) -> Option<Loc> {
        let GlobalAlloc::Function(instance) = GlobalAlloc::from(alloc_id) else {
            return None;
        };
        let key = format!("{:?}_{:?}", instance.def, instance.args());
        Some(Self::fn_ptr_identity_expr_from_key(&key))
    }

    /// The `AllocId` the allocation's provenance table records at `offset`, if
    /// any.
    ///
    /// This is the *recorded* answer to "does a pointer live at this byte
    /// offset?" — const-eval wrote it, and no width test is involved.
    fn allocation_pointer_target(
        alloc: &rustc_public::ty::Allocation,
        offset: usize,
    ) -> Option<AllocId> {
        alloc
            .provenance
            .ptrs
            .iter()
            .find(|(ptr_offset, _)| *ptr_offset == offset)
            .map(|(_, prov)| prov.0)
    }

    /// Reads `width` bits at byte `offset` out of a static/const allocation,
    /// tagged with the provenance the allocation itself declares.
    ///
    /// # What decides the tag
    ///
    /// The provenance table, not the width. A relocation entry at `offset` means
    /// const-eval put a pointer there; its absence means it put data there. The
    /// width comparison that survives below decides something else entirely —
    /// whether this read *covers* the pointer slot, since a narrower read
    /// (a `u8` field of a `#[repr(packed)]` struct overlapping the relocation)
    /// yields a byte of a pointer, which is a datum and not an address.
    pub(in crate::codegen_ay::chc) fn read_scalar_from_allocation(
        alloc: &rustc_public::ty::Allocation,
        offset: usize,
        width: u32,
    ) -> Option<AllocScalar> {
        let pointer_target = Self::allocation_pointer_target(alloc, offset)
            .filter(|_| width == crate::codegen_ay::types::POINTER_WIDTH);

        if let Some(target) = pointer_target
            && let Some(loc) = Self::fn_ptr_identity_expr_from_alloc_id(target)
        {
            return Some(AllocScalar::Ptr(PtrRepr::Thin(loc)));
        }

        let byte_width = width as usize / 8;
        let mut value: u128 = 0;
        for b in 0..byte_width {
            let byte_val: u8 = alloc.bytes.get(offset + b).copied()?.unwrap_or(0);
            value |= (byte_val as u128) << (b * 8);
        }
        let masked = if width >= 128 { value } else { value & ((1u128 << width) - 1) };
        let expr = ay_bindings::Expr::bitvec_const(masked, width);

        // A relocated slot whose bytes had to be read raw is still a pointer:
        // the bytes carry only the offset within the target object, and the
        // object's identity lives in the relocation entry. The expression is
        // byte-for-byte what it always was; what changes is that a consumer can
        // now see that this `0` is a pointer's offset and not the integer zero.
        Some(if pointer_target.is_some() {
            AllocScalar::Ptr(PtrRepr::Thin(Loc::of_address(expr)))
        } else {
            AllocScalar::Value(Val::of_value(expr))
        })
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
        alloc: &rustc_public::ty::Allocation,
        offset: usize,
        ty: rustc_public::ty::Ty,
        sort: &ay_bindings::Sort,
    ) -> Option<ay_bindings::Expr> {
        let sequential = || Self::read_composite_from_allocation(alloc, offset, sort);

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
            field_exprs.push(Self::read_adt_composite_from_allocation(
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

    /// Like `read_composite_from_bytes` but preserves function provenance.
    pub(in crate::codegen_ay::chc) fn read_composite_from_allocation(
        alloc: &rustc_public::ty::Allocation,
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
            let byte_val: u8 = match alloc.bytes.get(offset).copied() {
                Some(b) => b.unwrap_or(0),
                None => 0,
            };
            return Some(Expr::bool_const(byte_val != 0));
        }
        if let Some(width) = sort.bitvec_width() {
            // Boundary with the untyped recursive readers: a composite is
            // assembled out of leaves, and a datatype constructor has no slot to
            // record which of its fields were relocations.
            return Self::read_scalar_from_allocation(alloc, offset, width)
                .map(AllocScalar::into_expr);
        }

        if let Some(arr) = sort.array_sort() {
            let elem_width = Self::sort_byte_width(&arr.element_sort)?;
            if elem_width == 0 {
                return None;
            }
            let remaining = alloc.bytes.len().saturating_sub(offset);
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
                    Self::read_composite_from_allocation(alloc, elem_offset, &arr.element_sort)?;
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
                    Self::read_composite_from_allocation(alloc, field_offset, &field.sort)?;
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

    /// Read a AY expression from allocation + sort (scalar or composite).
    /// Part of #3496 Bug A.
    pub(in crate::codegen_ay::chc) fn scalar_from_alloc(
        alloc: &rustc_public::ty::Allocation,
        sort: &ay_bindings::Sort,
    ) -> Option<ay_bindings::Expr> {
        use ay_bindings::Expr;

        // Scalar types: use Allocation's built-in readers for whole-allocation values.
        if sort.is_bool() {
            let val = alloc.read_bool().ok()?;
            return Some(Expr::bool_const(val));
        }
        if let Some(width) = sort.bitvec_width() {
            if let Ok(value) = alloc.read_uint() {
                let masked = if width >= 128 { value } else { value & ((1u128 << width) - 1) };
                return Some(Expr::bitvec_const(masked, width));
            }
            // read_uint() errors on ANY uninit byte — which union statics
            // routinely contain (const-eval leaves padding uninit, e.g.
            // `static FOO: Data = Data { a: [0, 1, 0] }` in a 4-byte union).
            // For a provenance-free allocation the byte-wise reader below
            // zero-fills the uninit bytes, matching Kani/CBMC static-image
            // semantics (the zeroed binary image; union_transmute's oracle
            // y == 256 REQUIRES padding == 0). Provenance-bearing failures
            // still bail to the static_init_incomplete demotion.
            if alloc.provenance.ptrs.is_empty() {
                return Self::read_composite_from_bytes(&alloc.bytes, 0, sort);
            }
            return None;
        }
        if sort.is_int() {
            let value = alloc.read_int().ok()?;
            return Some(Expr::int_const(value));
        }

        // Composite types: read from allocation bytes at offsets.
        Self::read_composite_from_bytes(&alloc.bytes, 0, sort)
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
        alloc: &rustc_public::ty::Allocation,
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

    /// The address a relocated slot's own bytes denote, for a relocation whose
    /// target could not be resolved.
    ///
    /// # What establishes the address
    ///
    /// The provenance table, and only through a read that COVERS the pointer
    /// slot. [`ChcCtx::read_scalar_from_allocation`] is the one reader that
    /// consults that table, and it answers `Ptr` exactly when a relocation at
    /// `offset` is recorded *and* the read is [`POINTER_WIDTH`] wide — i.e. when
    /// the bytes are the pointer's own representation rather than a fragment of
    /// one. So this asks for exactly the pointer slot: `POINTER_WIDTH` bits at
    /// `offset`, the same slot the fat-pointer metadata read skips past.
    ///
    /// Asking for the *declared* slot width instead is what made the call site
    /// below a laundered tag. For a fat pointer that width is two words, so the
    /// reader's own filter reports `Value` — "a byte of a pointer, which is a
    /// datum and not an address", in its words — and the previous code tagged
    /// that datum `Loc::of_address` anyway, handing a `2 * POINTER_WIDTH` term
    /// to `PtrRepr::from_declared_roles` as the *data* half.
    ///
    /// `None` means no address is established here (a truncated initializer
    /// image, or a read the table declines to confirm). The caller demotes; it
    /// does not mint one.
    ///
    /// [`POINTER_WIDTH`]: crate::codegen_ay::types::POINTER_WIDTH
    fn unresolved_relocation_address(
        alloc: &rustc_public::ty::Allocation,
        offset: usize,
    ) -> Option<Loc> {
        match Self::read_scalar_from_allocation(
            alloc,
            offset,
            crate::codegen_ay::types::POINTER_WIDTH,
        )? {
            AllocScalar::Ptr(repr) => Some(repr.into_data()),
            AllocScalar::Value(_) => None,
        }
    }

    /// Decodes one reference/raw-pointer-typed slot of a static's initializer.
    ///
    /// # What decides thin vs fat
    ///
    /// [`PtrSlot`], read off the sort `translate_ty` produced for `rust_ty` —
    /// i.e. off the *declaration*. The two hand-written width comparisons this
    /// replaces asked the same question of the same sort, but separately and in
    /// the wrong register: written as `width == POINTER_WIDTH` next to an
    /// expression they read as "this looks like an address", which is the
    /// inference this campaign exists to delete. Nothing here infers
    /// address-ness at all: `rust_ty` is matched as `Ref`/`RawPtr` on the line
    /// above, the relocation table names the target, and the one lane that has
    /// to fall back on the initializer's own bytes goes through
    /// [`ChcCtx::unresolved_relocation_address`], which refuses to invent one.
    fn read_pointer_like_from_allocation(
        &mut self,
        alloc: &rustc_public::ty::Allocation,
        offset: usize,
        sort: &ay_bindings::Sort,
        rust_ty: rustc_public::ty::Ty,
    ) -> Option<AllocScalar> {
        use rustc_public::ty::{RigidTy, TyKind};

        let TyKind::RigidTy(RigidTy::Ref(_, pointee_ty, _) | RigidTy::RawPtr(pointee_ty, _)) =
            rust_ty.kind()
        else {
            return Self::read_composite_from_allocation(alloc, offset, sort)
                .map(|expr| AllocScalar::Value(Val::of_value(expr)));
        };

        let width = sort.bitvec_width()?;
        let ptr_bytes = (crate::codegen_ay::types::POINTER_WIDTH / 8) as usize;
        let provenance_target = Self::allocation_pointer_target(alloc, offset);

        let data_ptr: Loc = if let Some(target_alloc_id) = provenance_target {
            if let Some(fn_ptr) = Self::fn_ptr_identity_expr_from_alloc_id(target_alloc_id) {
                fn_ptr
            } else if let Some((_resolved_id, addr)) =
                self.resolve_static_target_init_expr(target_alloc_id, pointee_ty)
            {
                addr
            } else {
                // Pointee type can't be translated (e.g. `str` is DST). Allocate
                // an address for the target and seed backing memory if possible;
                // failing that, the relocation still says this slot holds a
                // pointer, so the pointer slot's own bytes are that pointer's
                // (unresolved) representation. `?` demotes when even that cannot
                // be established — the static is then left unconstrained, which
                // is booked as a sound widening, whereas a fabricated address is
                // not recoverable downstream.
                self.alloc_dst_pointer_fallback(target_alloc_id, pointee_ty)
                    .or_else(|| Self::unresolved_relocation_address(alloc, offset))?
            }
        } else {
            return Self::read_scalar_from_allocation(alloc, offset, width);
        };

        match PtrSlot::of_sort(sort) {
            Some(PtrSlot::Thin) => Some(AllocScalar::Ptr(PtrRepr::Thin(data_ptr))),
            Some(PtrSlot::Fat) => {
                // The metadata half is a length / vtable id read out of plain
                // bytes right after the relocation — a value, and the only thing
                // that keeps it on the correct side of the packed word is
                // `PtrRepr::into_packed`, which states the byte order once.
                let metadata = Self::read_scalar_from_allocation(
                    alloc,
                    offset + ptr_bytes,
                    crate::codegen_ay::types::POINTER_WIDTH,
                )?;
                let meta = Val::of_value(metadata.into_expr());
                Some(AllocScalar::Ptr(PtrRepr::from_declared_roles(data_ptr, meta)))
            }
            None => Self::read_scalar_from_allocation(alloc, offset, width),
        }
    }

    fn seed_static_str_backing_memory(
        &mut self,
        target_alloc_data: &rustc_public::ty::Allocation,
        target_addr: Loc,
    ) {
        // Elide long strings (panic messages). Same threshold as extract_str_from_const_ref.
        if target_alloc_data.bytes.len() > 64 {
            return;
        }
        let u8_ty = rustc_public::ty::Ty::unsigned_ty(rustc_public::ty::UintTy::U8);
        for (idx, byte) in target_alloc_data.bytes.iter().enumerate() {
            let Some(byte) = byte else { continue };
            let addr = Self::static_addr_with_offset(target_addr.clone(), idx as u64);
            self.push_static_memory_init_entry(
                u8_ty,
                Val::of_value(ay_bindings::Expr::bitvec_const(*byte as u128, 8)),
                addr,
            );
        }
    }

    /// The address already minted for `alloc_id`, if this body has minted one.
    ///
    /// `static_address_exprs` is written at exactly four sites, each of which
    /// stores a freshly allocated `obj_id ++ 0` object base — see
    /// [`ChcCtx::alloc_dst_pointer_fallback`],
    /// [`ChcCtx::resolve_static_target_init_expr`], `collect_static_state_vars`
    /// and `prescan_callee_statics`. The map is therefore an address producer by
    /// construction, and this accessor is the one place that says so, so the
    /// tag is not re-asserted at each lookup.
    fn static_address_loc(&self, alloc_id: AllocId) -> Option<Loc> {
        self.ref_resolution.static_address_exprs.get(&alloc_id).cloned().map(Loc::of_address)
    }

    /// Mints a fresh object base address for a static allocation and records it.
    fn mint_static_address(&mut self, resolved_alloc_id: AllocId) -> Option<Loc> {
        let obj_id = self.heap_state.next_alloc_id()?;
        let addr = ay_bindings::Expr::bitvec_const(obj_id as i128, 32)
            .concat(ay_bindings::Expr::bitvec_const(0i128, 32));
        self.ref_resolution.static_address_exprs.insert(resolved_alloc_id, addr.clone());
        Some(Loc::of_address(addr))
    }

    /// Allocate an address for a DST pointee (e.g. `str`) when
    /// `resolve_static_target_init_expr` fails because `translate_ty` can't
    /// handle the pointee type.
    fn alloc_dst_pointer_fallback(
        &mut self,
        target_alloc_id: AllocId,
        pointee_ty: rustc_public::ty::Ty,
    ) -> Option<Loc> {
        let (resolved_id, alloc_data) = self.canonical_static_seed_alloc(target_alloc_id)?;
        if let Some(addr) = self.static_address_loc(resolved_id) {
            return Some(addr);
        }
        let addr = self.mint_static_address(resolved_id)?;
        if matches!(
            pointee_ty.kind(),
            rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::Str)
        ) {
            self.seed_static_str_backing_memory(&alloc_data, addr.clone());
        }
        Some(addr)
    }

    fn resolve_static_target_init_expr(
        &mut self,
        target_alloc_id: AllocId,
        pointee_ty: rustc_public::ty::Ty,
    ) -> Option<(AllocId, Loc)> {
        use rustc_public::ty::{RigidTy, TyKind};

        let (resolved_target_alloc_id, target_alloc_data) =
            self.canonical_static_seed_alloc(target_alloc_id)?;

        if let Some(addr) = self.static_address_loc(resolved_target_alloc_id) {
            return Some((resolved_target_alloc_id, addr));
        }

        let pointee_sort = Self::translate_ty(pointee_ty)?;
        let target_addr = self.mint_static_address(resolved_target_alloc_id)?;

        // The pointee is its own allocation and needs its own layout record, or
        // `obj_size[obj]` stays unconstrained and every in-bounds obligation on
        // `*STATIC` is refutable.
        if let Some(obj_id) = Self::try_extract_obj_id(target_addr.as_expr())
            && let Some(size) = self.get_type_size(pointee_ty)
        {
            let align = self.get_type_align(pointee_ty).unwrap_or(1);
            self.ref_resolution.static_alloc_sizes.push((obj_id, size as u32, align));
        }

        if let Some(init_val) =
            self.static_init_from_alloc(&target_alloc_data, &pointee_sort, pointee_ty)
        {
            // Keep the pointee's initial value reachable by allocation id: the
            // static's own `static_initial_values` entry is the POINTER, so a
            // `*STATIC` read has nowhere else to find what it points at.
            self.ref_resolution
                .static_alloc_init_values
                .insert(resolved_target_alloc_id, init_val.as_expr().clone());
            self.register_static_memory_init_entries(pointee_ty, init_val, target_addr.clone());

            if matches!(pointee_ty.kind(), TyKind::RigidTy(RigidTy::Str)) {
                self.seed_static_str_backing_memory(&target_alloc_data, target_addr.clone());
            }
        }

        Some((resolved_target_alloc_id, target_addr))
    }

    /// Resolve a pointer-typed static's initial value from allocation provenance.
    /// Part of #3496: pointer-typed static provenance resolution.
    ///
    /// Returns the **address** of the referent object, minted by
    /// `resolve_static_target_init_expr` as `obj_id ++ 0`. It is the data half of
    /// the static's initial pointer value — never the whole value, which for an
    /// unsized referent also carries a length.
    pub(in crate::codegen_ay::chc) fn resolve_pointer_static_init(
        &mut self,
        target_alloc_id: AllocId,
        pointee_ty: rustc_public::ty::Ty,
        static_name: &str,
        vec_idx: usize,
    ) -> Option<Loc> {
        let (resolved_target_alloc_id, target_addr) =
            self.resolve_static_target_init_expr(target_alloc_id, pointee_ty)?;

        self.ref_resolution.static_pointee_addrs.insert(vec_idx, target_addr.as_expr().clone());
        if let Some(init) =
            self.ref_resolution.static_alloc_init_values.get(&resolved_target_alloc_id).cloned()
        {
            self.ref_resolution.static_pointee_init_values.insert(vec_idx, init);
        }

        tracing::debug!(
            vec_idx,
            static_name = %static_name,
            source_target_alloc_id = ?target_alloc_id,
            ?resolved_target_alloc_id,
            "CHC: resolved pointer static to concrete target address (#3496)"
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
fn declared_field_tys_for_sort(
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
            Some(decl_fields.iter().map(|f| f.ty_with_args(&args)).collect())
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
