// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Scalar constant extraction from MIR allocations.
//!
//! Extracts concrete scalar values (bool, int, uint, char, float, raw pointer, ADT, closure)
//! from MIR `Allocation` byte arrays and converts them to AY `Expr` nodes.
//! Split from operand.rs per #3214.
//!
//! Enum-specific extraction (unit enum, option-like, single-variant enum, float)
//! is in `operand_scalar_enum.rs`.

use super::{
    Allocation, CrateDef, Expr, GlobalAlloc, IndexedVal, IntoOption, LayoutOf, RigidTy, SortInner,
    StatementCodegen, TyKind,
};
use crate::codegen_ay::names::{self, struct_sort};
use crate::codegen_ay::types::{
    POINTER_WIDTH, int_ty_to_bitvec_width, ptr_sort, uint_ty_to_bitvec_width,
};
use rustc_public::ty::GenericArgKind;
use tracing::{debug, warn};

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Extract a scalar value (bool/int/uint) from an allocation.
    ///
    /// REQUIRES: alloc contains valid bytes for the given type
    /// ENSURES: On Some, result.sort() matches width/signedness of ty
    /// ENSURES: On None, allocation could not be interpreted as scalar
    pub(super) fn codegen_scalar_from_alloc(
        &self,
        alloc: &Allocation,
        ty: rustc_public::ty::Ty,
    ) -> Option<Expr> {
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Bool) => {
                Some(Expr::bool_const(alloc.read_bool().into_option()?))
            }
            TyKind::RigidTy(RigidTy::Int(int_ty)) => {
                let width = int_ty_to_bitvec_width(int_ty);
                let value = alloc.read_int().into_option()?;
                // Mask to the correct width for SMT bitvector
                let value_u128 = if width >= 128 {
                    value as u128
                } else {
                    (value as u128) & ((1u128 << width) - 1)
                };
                Some(Expr::bitvec_const(value_u128, width))
            }
            TyKind::RigidTy(RigidTy::Uint(uint_ty)) => {
                let width = uint_ty_to_bitvec_width(uint_ty);
                let value = alloc.read_uint().into_option()?;
                // Mask to the correct width for SMT bitvector
                let value_u128 = if width >= 128 { value } else { value & ((1u128 << width) - 1) };
                Some(Expr::bitvec_const(value_u128, width))
            }
            TyKind::RigidTy(RigidTy::Char) => {
                // Rust char is a 32-bit Unicode scalar value (0x0000 to 0xD7FF or 0xE000 to 0x10FFFF)
                let value = alloc.read_uint().into_option()?;
                // Mask to 32 bits - char is always 4 bytes in Rust
                let value_u128 = value & 0xFFFFFFFF;
                Some(Expr::bitvec_const(value_u128, 32))
            }
            // Part of #3094: Float constants modeled as bitvectors.
            TyKind::RigidTy(RigidTy::Float(float_ty)) => {
                Self::float_scalar_to_expr(alloc, float_ty)
            }
            // Raw pointer constants (#1039) - NonNull::dangling() and similar const-evaluated pointers
            // Read as usize (pointer-width bitvector)
            TyKind::RigidTy(RigidTy::RawPtr(..)) => self.codegen_raw_ptr_from_alloc(alloc),
            TyKind::RigidTy(RigidTy::Adt(adt_def, args)) => {
                self.codegen_adt_from_alloc(alloc, ty, adt_def, args)
            }
            TyKind::RigidTy(RigidTy::Array(elem_ty, len_const)) => {
                self.codegen_array_wrapper_from_alloc(alloc, elem_ty, len_const)
            }
            TyKind::RigidTy(RigidTy::FnPtr(..)) => {
                let value = alloc.read_uint().into_option()?;
                let value_u128 = value & ((1u128 << POINTER_WIDTH) - 1);
                debug!("codegen_scalar_from_alloc: FnPtr value={:#x}", value_u128);
                Some(Expr::bitvec_const(value_u128, POINTER_WIDTH))
            }
            TyKind::RigidTy(RigidTy::Tuple(tys)) if tys.len() > 1 => {
                self.codegen_tuple_from_alloc(alloc, ty, &tys)
            }
            TyKind::RigidTy(RigidTy::Closure(def, args)) => {
                self.codegen_closure_from_alloc(alloc, ty, def, args)
            }
            _ => None, // external enum: TyKind
        }
    }

    /// Read a raw pointer constant from an allocation.
    fn codegen_raw_ptr_from_alloc(&self, alloc: &Allocation) -> Option<Expr> {
        let value = alloc.read_uint().into_option()?;
        let value_u128 = value & ((1u128 << POINTER_WIDTH) - 1);
        // Part of #3094: Raw pointer constants to statics have provenance
        // but offset 0. read_uint() returns just the offset, ignoring
        // provenance, so `&raw const STATIC_VAR` produces bitvec(0) — NULL.
        // This triggers false null-check violations in place_deref.rs.
        // When provenance points to a real allocation (Static or Memory),
        // use a non-zero page-aligned sentinel address instead of the raw
        // offset. The BMC path identifies memory locations by variable name,
        // not address, so the specific non-zero value is immaterial.
        if value_u128 == 0 && !alloc.provenance.ptrs.is_empty() {
            let (_, prov) = &alloc.provenance.ptrs[0];
            let alloc_id = prov.0;
            let has_real_provenance = matches!(
                GlobalAlloc::from(alloc_id),
                GlobalAlloc::Static(_) | GlobalAlloc::Memory(_)
            );
            if has_real_provenance {
                tracing::debug!(
                    "codegen_scalar_from_alloc: RawPtr offset=0 with provenance, sentinel=0x1000"
                );
                return Some(Expr::bitvec_const(0x1000u128, POINTER_WIDTH));
            }
        }
        tracing::debug!("codegen_scalar_from_alloc: RawPtr value={:#x}", value_u128);
        Some(Expr::bitvec_const(value_u128, POINTER_WIDTH))
    }

    /// Extract an ADT (struct/enum) constant from an allocation.
    fn codegen_adt_from_alloc(
        &self,
        alloc: &Allocation,
        ty: rustc_public::ty::Ty,
        adt_def: rustc_public::ty::AdtDef,
        args: rustc_public::ty::GenericArgs,
    ) -> Option<Expr> {
        // Handle ADT types using trimmed_name() to avoid format!("{:?}") allocation.
        // Full debug name is only computed lazily when needed for Option-like enum paths.
        let base_name = adt_def.trimmed_name();

        // #1524: Layout constants appear as ADT allocations.
        if base_name == "Layout" {
            return self.codegen_layout_from_alloc(alloc);
        }

        // #1039: Handle Alignment type - wrapper used by NonNull::dangling()
        if base_name == "Alignment" {
            return self.codegen_alignment_from_alloc(alloc, adt_def, args);
        }

        // #1039: Handle NonNull<T> - single field wrapper around raw pointer
        if base_name == "NonNull" {
            let value = alloc.read_uint().into_option()?;
            let value_u128 = value & ((1u128 << POINTER_WIDTH) - 1);
            tracing::debug!("codegen_scalar_from_alloc: NonNull value={:#x}", value_u128);
            return Some(Expr::bitvec_const(value_u128, POINTER_WIDTH));
        }

        // Part of #3367: TypeId is a wrapper around u128 (internal type identity).
        // Extract the raw 128-bit value so Transmute(TypeId → u128) is identity
        // and Any::downcast_ref type equality checks resolve concretely.
        if base_name == "TypeId" {
            let value = alloc.read_uint().into_option().unwrap_or_else(|| {
                // Part of #1739: TypeId allocations may carry provenance markers
                // that cause read_uint() to fail. Read raw bytes directly.
                let mut v: u128 = 0;
                for (i, byte) in alloc.bytes.iter().take(16).enumerate() {
                    if let Some(b) = byte {
                        v |= (*b as u128) << (i * 8);
                    }
                }
                tracing::debug!("codegen_scalar_from_alloc: TypeId read_uint failed, raw bytes fallback value={:#x}", v);
                v
            });
            tracing::debug!("codegen_scalar_from_alloc: TypeId value={:#x}", value);
            return Some(Expr::bitvec_const(value, 128));
        }

        let variants = adt_def.variants();
        // Check if this is a unit enum (all variants have no fields)
        let is_unit_enum = variants.iter().all(|v| v.fields().is_empty());
        if is_unit_enum {
            return self.codegen_unit_enum_from_alloc(alloc, adt_def, &variants);
        }

        // Handle Option-like enums (2 variants, one with 0 fields, one with 1 field) (#407)
        let is_option_like = variants.len() == 2 && {
            let empty_count = variants.iter().filter(|v| v.fields().is_empty()).count();
            let one_field_count = variants.iter().filter(|v| v.fields().len() == 1).count();
            empty_count == 1 && one_field_count == 1
        };
        if is_option_like {
            return self.codegen_option_like_from_alloc(alloc, ty, adt_def, args, &variants);
        }

        // Part of #4086: Single-field array wrapper ADTs (#[repr(simd)] types like i64x2).
        // These are transparent to Array sort (codegen_types_adt.rs line 297-302), but
        // codegen_scalar_from_alloc sees TyKind::Adt. Extract elements from the allocation
        // bytes and build an SMT Array constant directly.
        if variants.len() == 1 && variants[0].fields().len() == 1 {
            let field_ty = variants[0].fields()[0].ty_with_args(&args);
            if let TyKind::RigidTy(RigidTy::Array(elem_ty, len_const)) = field_ty.kind() {
                if let Some(result) =
                    self.codegen_array_wrapper_from_alloc(alloc, elem_ty, len_const)
                {
                    return Some(result);
                }
            }
        }

        // Part of #3094: Handle single-variant enums with data fields
        if variants.len() == 1 && !variants[0].fields().is_empty() {
            return self
                .codegen_single_variant_enum_from_alloc(alloc, ty, adt_def, args, &variants);
        }

        // Phase 1b (#4244): Multi-variant enums with data fields (Result, custom enums).
        if variants.len() >= 2 && variants.iter().any(|v| !v.fields().is_empty()) {
            return self.codegen_multi_variant_enum_from_alloc(alloc, ty, adt_def, args, &variants);
        }

        None
    }

    /// Extract an array wrapper ADT from an allocation (#4086).
    ///
    /// Handles element types whose SMT sort is either a BitVec (integers,
    /// `char`, raw pointers) or `Bool`. The layout size of the element is
    /// taken from `LayoutOf` rather than deriving it from the bitvec width,
    /// since Bool elements occupy 1 byte in MIR allocations but have no
    /// intrinsic width in the SMT sort. Without the Bool branch, this
    /// function returned `None` for `&[bool; N]` constants and the caller
    /// fell through to `codegen_assign`'s unconstrained fallback (#4530).
    fn codegen_array_wrapper_from_alloc(
        &self,
        alloc: &Allocation,
        elem_ty: rustc_public::ty::Ty,
        len_const: rustc_public::ty::TyConst,
    ) -> Option<Expr> {
        let len = len_const.eval_target_usize().into_option()? as usize;
        let elem_sort = Self::infer_sort_from_ty(elem_ty)?;
        // Physical element size from the Rust layout — covers Bool (1 byte),
        // BitVec (width/8), and preserves padding for fixed-width types.
        let elem_bytes = LayoutOf::new(elem_ty).size_of()?;
        if elem_bytes == 0 {
            return None;
        }

        // Verify allocation has enough bytes
        if alloc.bytes.len() < len * elem_bytes {
            return None;
        }

        // Build per-element reader + default value for the ElemSort.
        let read_elem = |i: usize| -> Option<Expr> {
            let offset = i * elem_bytes;
            let bytes = alloc.bytes.get(offset..offset + elem_bytes)?;
            if elem_sort.is_bool() {
                // Rust represents bool as a single byte: 0 → false, 1 → true.
                // MIR rejects any other bit pattern, so we treat non-zero as
                // true without diagnosing invalid allocations here.
                let raw = bytes.first()?.unwrap_or(0);
                Some(Expr::bool_const(raw != 0))
            } else if let Some(width) = elem_sort.bitvec_width() {
                let read_bytes = ((width as usize) / 8).min(elem_bytes);
                let mut value: u128 = 0;
                for (j, byte) in bytes.iter().take(read_bytes).enumerate() {
                    if let Some(b) = byte {
                        value |= (*b as u128) << (j * 8);
                    }
                }
                Some(Expr::bitvec_const(value, width))
            } else {
                // Compound element (nested array / fieldless-enum-as-array / struct):
                // recurse via a sub-allocation over this element's bytes, reusing the
                // per-type codegen. Without this, a const `[[E; N]; M]` lookup table
                // (e.g. aterm's `OriginTag` join table — array OF arrays of fieldless
                // enums) returned None, the caller fell through to codegen_assign's
                // unconstrained-array fallback, and every downstream `discriminant`
                // read was unconstrained (INCONCLUSIVE). The recursion is well-typed:
                // `infer_sort_from_ty([T; N]) == Sort::array(ptr_sort(), sort(T))`,
                // exactly what this fn builds.
                let sub_alloc = Allocation {
                    bytes: bytes.to_vec(),
                    provenance: rustc_public::ty::ProvenanceMap { ptrs: vec![] },
                    align: alloc.align,
                    mutability: alloc.mutability,
                };
                self.codegen_scalar_from_alloc(&sub_alloc, elem_ty)
            }
        };

        // Default seed for the const-array. Every in-bounds index is overwritten by
        // the loop below, so this only fills out-of-bounds slots; it must still match
        // the element sort, recursively for nested arrays. Returns None (sound,
        // unconstrained fallback in the caller) for elements with no canonical
        // default (e.g. a data-carrying-enum datatype).
        let zero_elem = Self::array_default_for_sort(&elem_sort)?;
        let mut result = Expr::const_array(ptr_sort(), zero_elem);

        // Store each element
        for i in 0..len {
            let elem = read_elem(i)?;
            let idx = Expr::bitvec_const(i as u128, POINTER_WIDTH);
            result = result.store(idx, elem);
        }

        debug!(
            "codegen_array_wrapper_from_alloc: {} elements of sort {:?}, {} bytes each, total {} bytes",
            len,
            elem_sort,
            elem_bytes,
            len * elem_bytes
        );
        Some(result)
    }

    /// A canonical default `Expr` of `sort`, used to seed a const-array before each
    /// element is stored. Recurses through nested array sorts so a `[[T; N]; M]`
    /// constant gets a `[T; N]`-shaped default whose index sort (`ptr_sort()`)
    /// matches what `infer_sort_from_ty`/`codegen_array_wrapper_from_alloc` build.
    /// Returns `None` for sorts with no canonical default (e.g. datatypes),
    /// preserving the prior fail-to-`None` (sound, unconstrained) caller behavior.
    fn array_default_for_sort(sort: &ay_bindings::Sort) -> Option<Expr> {
        match sort.inner() {
            SortInner::Bool => Some(Expr::bool_const(false)),
            SortInner::BitVec(bv) => Some(Expr::bitvec_const(0u128, bv.width)),
            SortInner::Array(arr) => Some(Expr::const_array(
                arr.index_sort.clone(),
                Self::array_default_for_sort(&arr.element_sort)?,
            )),
            _ => None,
        }
    }

    /// Extract a Layout constant from an allocation (#1524).
    /// Layout struct: { size: usize, align: Alignment }
    fn codegen_layout_from_alloc(&self, alloc: &Allocation) -> Option<Expr> {
        // Read raw bytes: first 8 bytes = size, next 8 bytes = alignment
        let size_value = if alloc.bytes.len() >= 8 {
            let mut size_bytes = [0u8; 8];
            for (i, b) in alloc.bytes.iter().take(8).enumerate() {
                size_bytes[i] = b.unwrap_or(0);
            }
            u64::from_le_bytes(size_bytes) as u128
        } else {
            // Fallback: use read_uint for smaller allocations
            alloc.read_uint().into_option()? & ((1u128 << POINTER_WIDTH) - 1)
        };

        // Read alignment from bytes 8-16 (or default to size alignment)
        let align_value = if alloc.bytes.len() >= 16 {
            let mut align_bytes = [0u8; 8];
            for (i, b) in alloc.bytes.iter().skip(8).take(8).enumerate() {
                align_bytes[i] = b.unwrap_or(0);
            }
            u64::from_le_bytes(align_bytes) as u128
        } else {
            // Default alignment: use size as hint, minimum 1
            if size_value == 0 { 1 } else { size_value.min(8) }
        };

        debug!("codegen_scalar_from_alloc: Layout size={} align={}", size_value, align_value);

        // Create Layout datatype with fld_size and fld_align
        let size_expr = Expr::bitvec_const(size_value, POINTER_WIDTH);
        let align_expr = Expr::bitvec_const(align_value, POINTER_WIDTH);
        let layout_sort = struct_sort("Layout", crate::codegen_ay::names::layout_fields());
        let layout = Expr::datatype_constructor(
            "Layout",
            "Layout_mk",
            vec![size_expr, align_expr],
            layout_sort,
        );
        Some(layout)
    }

    /// Extract an Alignment constant from an allocation (#1039).
    /// Types: std::ptr::Alignment, core::ptr::Alignment
    fn codegen_alignment_from_alloc(
        &self,
        alloc: &Allocation,
        adt_def: rustc_public::ty::AdtDef,
        args: rustc_public::ty::GenericArgs,
    ) -> Option<Expr> {
        // Use the standard sort inference to get consistent sort with codegen_place
        if let Some(alignment_sort) = Self::infer_adt_sort(adt_def, args)
            && let SortInner::Datatype(dt) = alignment_sort.inner()
            && let Some(cons) = dt.constructors.first()
            && let Some(field) = cons.fields.first()
        {
            // Read the allocation value with proper width
            let value = alloc.read_uint().into_option()?;
            let field_width = field.sort.bitvec_width().unwrap_or(POINTER_WIDTH);
            let value_u128 =
                if field_width >= 128 { value } else { value & ((1u128 << field_width) - 1) };
            debug!(
                "codegen_scalar_from_alloc: Alignment value={:#x}, width={}",
                value_u128, field_width
            );
            let field_expr = Expr::bitvec_const(value_u128, field_width);
            let result = Expr::datatype_constructor(
                &dt.name,
                &cons.name,
                vec![field_expr],
                alignment_sort.clone(),
            );
            return Some(result);
        }
        // Fallback: couldn't infer sort, skip Alignment handling.
        // Part of #3211: Upgraded to warn! for visibility. Counter call blocked
        // by &self signature; would need method signature change to &mut self.
        warn!("codegen_scalar_from_alloc: Alignment sort inference failed, skipping");
        None
    }

    /// Extract a multi-field tuple constant from an allocation.
    fn codegen_tuple_from_alloc(
        &self,
        alloc: &Allocation,
        ty: rustc_public::ty::Ty,
        tys: &[rustc_public::ty::Ty],
    ) -> Option<Expr> {
        let layout = LayoutOf::new(ty);
        let mut field_exprs = Vec::with_capacity(tys.len());
        let mut fields = Vec::with_capacity(tys.len());

        for (idx, elem_ty) in tys.iter().enumerate() {
            let field_sort = Self::infer_sort_from_ty(*elem_ty)?;
            let offset = layout.field_offset(idx)?;

            let field_expr = self.read_field_from_alloc(alloc, *elem_ty, &field_sort, offset)?;

            fields.push((names::tuple_field_name(idx), field_sort));
            field_exprs.push(field_expr);
        }

        let tuple_name = Self::tuple_sort_name(&fields);
        let tuple_sort = struct_sort(&tuple_name, fields);
        let cons_name = names::resolve_ctor_name(&tuple_sort, &tuple_name);
        debug!(
            "codegen_tuple_from_alloc: {} -> {}({} fields)",
            tuple_name,
            cons_name,
            field_exprs.len()
        );
        Some(Expr::datatype_constructor(tuple_name, cons_name, field_exprs, tuple_sort))
    }

    /// Extract a closure constant from an allocation.
    /// ZST closures -> Bool(true) per CHC convention. Capturing -> Datatype.
    pub(super) fn codegen_closure_from_alloc(
        &self,
        alloc: &Allocation,
        ty: rustc_public::ty::Ty,
        def: rustc_public::ty::ClosureDef,
        args: rustc_public::ty::GenericArgs,
    ) -> Option<Expr> {
        let closure_id = def.0.to_index();
        let closure_name = names::closure_sort_name(closure_id);
        let upvar_tys = Self::closure_upvar_tys_from_args(&args);

        if upvar_tys.is_empty() {
            debug!(closure_name, "non-capturing closure constant -> Bool(true)");
            return Some(Expr::bool_const(true));
        }

        let layout = LayoutOf::new(ty);
        let mut field_exprs = Vec::with_capacity(upvar_tys.len());
        let mut fields = Vec::with_capacity(upvar_tys.len());

        for (idx, upvar_ty) in upvar_tys.iter().enumerate() {
            let field_sort = Self::infer_sort_from_ty(*upvar_ty).unwrap_or_else(ptr_sort);
            let offset = layout.field_offset(idx)?;
            let field_expr = self.read_field_from_alloc(alloc, *upvar_ty, &field_sort, offset)?;
            fields.push((names::capture_field_name(idx), field_sort));
            field_exprs.push(field_expr);
        }

        let sort = struct_sort(&closure_name, fields);
        let cons_name = names::resolve_ctor_name(&sort, &closure_name);
        debug!(closure_name, num_captures = upvar_tys.len(), "closure constant -> Datatype");
        Some(Expr::datatype_constructor(closure_name, cons_name, field_exprs, sort))
    }

    /// Extract upvar types: tuple after FnPtr in args, or last tuple as fallback.
    fn closure_upvar_tys_from_args(
        args: &rustc_public::ty::GenericArgs,
    ) -> Vec<rustc_public::ty::Ty> {
        args.0
            .iter()
            .enumerate()
            .find_map(|(pos, arg)| {
                if matches!(
                    arg,
                    GenericArgKind::Type(ty)
                        if matches!(ty.kind(), TyKind::RigidTy(RigidTy::FnPtr(_)))
                ) {
                    match args.0.get(pos + 1) {
                        Some(GenericArgKind::Type(ty)) => match ty.kind() {
                            TyKind::RigidTy(RigidTy::Tuple(tys)) => Some(tys),
                            _ => None,
                        },
                        _ => None,
                    }
                } else {
                    None
                }
            })
            .or_else(|| {
                args.0.iter().rev().find_map(|arg| match arg {
                    GenericArgKind::Type(ty) => match ty.kind() {
                        TyKind::RigidTy(RigidTy::Tuple(tys)) => Some(tys),
                        _ => None,
                    },
                    _ => None,
                })
            })
            .unwrap_or_default()
    }

    /// Read a single field value from allocation bytes at a given offset.
    pub(super) fn read_field_from_alloc(
        &self,
        alloc: &Allocation,
        field_ty: rustc_public::ty::Ty,
        field_sort: &ay_bindings::Sort,
        offset: usize,
    ) -> Option<Expr> {
        if let Some(bv_width) = field_sort.bitvec_width() {
            // BitVec field: read raw bytes at offset
            let field_size = (bv_width as usize) / 8;
            let bytes = alloc.bytes.get(offset..offset + field_size)?;
            let mut value: u128 = 0;
            for (i, byte) in bytes.iter().enumerate() {
                if let Some(b) = byte {
                    value |= (*b as u128) << (i * 8);
                }
            }
            Some(Expr::bitvec_const(value, bv_width))
        } else if field_sort.is_bool() {
            // Bool field: read 1 byte at offset
            let byte = alloc.bytes.get(offset)?;
            let val = byte.unwrap_or(0);
            Some(Expr::bool_const(val != 0))
        } else {
            // Compound sort (Datatype, Array, etc.): attempt recursive extraction
            // by constructing a sub-allocation from the field's bytes.
            let field_size = LayoutOf::new(field_ty).size_of()?;
            let bytes = alloc.bytes.get(offset..offset + field_size)?;
            let sub_alloc = Allocation {
                bytes: bytes.to_vec(),
                provenance: rustc_public::ty::ProvenanceMap { ptrs: vec![] },
                align: alloc.align,
                mutability: alloc.mutability,
            };
            self.codegen_scalar_from_alloc(&sub_alloc, field_ty)
        }
    }
}

// Enum/float scalar extraction moved to operand_scalar_enum.rs per #4206.
