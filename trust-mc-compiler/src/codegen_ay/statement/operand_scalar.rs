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
    CrateDef, Expr, IndexedVal, IntoOption, LayoutOf, RigidTy, SortInner, StatementCodegen, TyKind,
};
use crate::codegen_ay::names::{self, struct_sort};
use crate::codegen_ay::shared::const_pointer::{ConstPtr, ConstRead, Slot};
use crate::codegen_ay::shared::mono_ty;
use crate::codegen_ay::types::{
    POINTER_WIDTH, int_ty_to_bitvec_width, ptr_sort, uint_ty_to_bitvec_width,
};
#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use rustc_public::ty::GenericArgKind;
use tracing::{debug, warn};

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Decode the constant VALUE of type `ty` held by `bytes` (a constant's
    /// own bytes, `const_pointer::const_bytes`, or a window of a target).
    ///
    /// Every byte access goes through the slot clause (`shared::const_pointer`):
    /// a pointer-typed slot is the address of its relocation's target plus the
    /// offset its bytes carry ([`Self::const_ptr_value`]), never those bytes as
    /// an integer; an uninitialized byte or a partial pointer declines. A
    /// top-level reference is not decoded here (`codegen_const_ref` reads its
    /// pointee), but a reference INSIDE a value is a pointer slot like any
    /// other.
    ///
    /// ENSURES: On Some, result.sort() matches width/signedness of ty
    /// ENSURES: On None, the bytes could not be interpreted (caller leaves the
    /// value unconstrained)
    pub(super) fn codegen_scalar_from_bytes(
        &self,
        bytes: &dyn ConstRead,
        ty: rustc_public::ty::Ty,
    ) -> Option<Expr> {
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Bool) => Some(Expr::bool_const(bytes.read_bool_at(0)?)),
            TyKind::RigidTy(RigidTy::Int(int_ty)) => {
                let width = int_ty_to_bitvec_width(int_ty);
                let value = bytes.read_uint_at(0, (width / 8) as usize)?;
                Some(Expr::bitvec_const(value, width))
            }
            TyKind::RigidTy(RigidTy::Uint(uint_ty)) => {
                let width = uint_ty_to_bitvec_width(uint_ty);
                let value = bytes.read_uint_at(0, (width / 8) as usize)?;
                Some(Expr::bitvec_const(value, width))
            }
            TyKind::RigidTy(RigidTy::Char) => {
                // A Rust char is a 32-bit Unicode scalar value.
                let value = bytes.read_uint_at(0, 4)?;
                Some(Expr::bitvec_const(value, 32))
            }
            // Part of #3094: Float constants modeled as bitvectors.
            TyKind::RigidTy(RigidTy::Float(float_ty)) => {
                Self::float_scalar_to_expr(bytes, float_ty)
            }
            // Raw pointer constants (#1039): `NonNull::dangling()`, `&raw const S`.
            // Only a THIN pointer has the pointer sort; a fat one's sort is a
            // datatype this reader does not build.
            TyKind::RigidTy(RigidTy::RawPtr(..))
                if Self::infer_sort_from_ty(ty).as_ref() == Some(&ptr_sort()) =>
            {
                self.const_pointer_slot(bytes, 0)
            }
            TyKind::RigidTy(RigidTy::Adt(adt_def, args)) => {
                self.codegen_adt_from_alloc(bytes, ty, adt_def, args)
            }
            TyKind::RigidTy(RigidTy::Array(elem_ty, len_const)) => {
                self.codegen_array_wrapper_from_alloc(bytes, elem_ty, len_const)
            }
            // A function pointer is its function's identity (a relocation to
            // a function at offset 0), or plain data (null is not a fn value,
            // but a const-eval'd integer is kept as it was).
            TyKind::RigidTy(RigidTy::FnPtr(..)) => self.const_pointer_slot(bytes, 0),
            TyKind::RigidTy(RigidTy::Tuple(tys)) if tys.len() > 1 => {
                self.codegen_tuple_from_alloc(bytes, ty, &tys)
            }
            TyKind::RigidTy(RigidTy::Closure(def, args)) => {
                self.codegen_closure_from_alloc(bytes, ty, def, args)
            }
            _ => None, // external enum: TyKind
        }
    }

    /// The pointer-width value stored at `at` under the slot clause.
    ///
    /// Plain data (an address const-eval produced without provenance: null,
    /// `NonNull::dangling()`) is that integer. A relocation is the pointer it
    /// records ([`Self::const_ptr_value`]). An uninitialized word, a partial
    /// pointer, or a target this lane never named declines.
    pub(super) fn const_pointer_slot(&self, bytes: &dyn ConstRead, at: usize) -> Option<Expr> {
        match bytes.read_slot(at, POINTER_WIDTH) {
            Slot::Data(value) => Some(Expr::bitvec_const(value, POINTER_WIDTH)),
            Slot::Pointer(ptr) => self.const_ptr_value(&ptr),
            Slot::Uninit | Slot::PartialPointer | Slot::OutOfBounds => None,
        }
    }

    /// The value of a constant pointer in this lane: `base(T) + k`, `base(T)`
    /// being the ONE address symbol `global_alloc_addrs` holds for its target
    /// (materialized when the body was entered, `global_alloc.rs`), or a
    /// function's identity (`fn_ptr_identity`, the value a reification of
    /// the same instance gets) when it names one at offset 0. `None` for a
    /// vtable, a target the body never materialized, or a function pointer
    /// at a nonzero offset: the caller leaves the value unconstrained.
    ///
    /// Before this, a pointer inside a constant VALUE (`[&raw const P.0, &raw
    /// const P.1]`, a struct's raw-pointer field) decoded to the offset its
    /// bytes carry, so `PTRS[0].is_null()` PROVED
    /// (tools/soundness-duals/const_pointer_value_slots_dual.rs).
    pub(super) fn const_ptr_value(&self, ptr: &ConstPtr) -> Option<Expr> {
        if let Some(instance) = ptr.function() {
            let id = crate::codegen_ay::fn_ptr_identity::fn_ptr_identity_of_instance(&instance);
            return Some(Expr::bitvec_const(u128::from(id), POINTER_WIDTH));
        }
        let key = ptr.key()?;
        let Some(base) = self.ctx.global_alloc_addrs.get(&key) else {
            debug!(?key, "constant pointer into an allocation this body never named: declined");
            return None;
        };
        ptr.address(base, POINTER_WIDTH)
    }

    /// A `width`-bit bitvector slot at `at`: plain data, or (pointer width
    /// only) a stored pointer's value. Anything else declines.
    fn read_bv_slot(&self, bytes: &dyn ConstRead, at: usize, width: u32) -> Option<Expr> {
        if width == POINTER_WIDTH {
            return self.const_pointer_slot(bytes, at);
        }
        let value = bytes.read_uint_at(at, (width / 8) as usize)?;
        Some(Expr::bitvec_const(value, width))
    }

    /// A `TypeId` at `at`: its 128-bit hash. Rustc stores it as pointers into
    /// a type-id segment whose OFFSETS are the hash words (`ConstPtr::offset`,
    /// the pointer's k); older layouts store plain data.
    fn type_id_value(bytes: &dyn ConstRead, at: usize) -> Option<u128> {
        if let (Some(lo), Some(hi)) =
            (bytes.stored_pointer(at), bytes.stored_pointer(at + POINTER_WIDTH as usize / 8))
        {
            return Some(u128::from(lo.offset()) | (u128::from(hi.offset()) << 64));
        }
        bytes.read_uint_at(at, 16)
    }

    /// Extract an ADT (struct/enum) constant from an allocation.
    fn codegen_adt_from_alloc(
        &self,
        alloc: &dyn ConstRead,
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

        // #1039: Handle NonNull<T> - single field wrapper around raw pointer.
        // Its word is a pointer slot: `NonNull::from(&S)` is S's address, not
        // the offset its bytes carry.
        if base_name == "NonNull" {
            return self.const_pointer_slot(alloc, 0);
        }

        // Part of #3367: TypeId is a wrapper around u128 (internal type identity).
        // Extract the raw 128-bit value so Transmute(TypeId → u128) is identity
        // and Any::downcast_ref type equality checks resolve concretely.
        if base_name == "TypeId" {
            let value = Self::type_id_value(alloc, 0)?;
            tracing::debug!("codegen_scalar_from_alloc: TypeId value={:#x}", value);
            return Some(Expr::bitvec_const(value, 128));
        }

        let variants = adt_def.variants();
        // Check if this is a unit enum (all variants have no fields). Only an ENUM: a unit
        // struct (`struct Mild;`) also has a single fieldless variant, and asking rustc for its
        // discriminant ICEs (`assertion failed: self.is_enum()`), e.g. for `&Mild as &dyn Tick`.
        let is_unit_enum = adt_def.kind() == rustc_public::ty::AdtKind::Enum
            && variants.iter().all(|v| v.fields().is_empty());
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
            let field_ty = mono_ty::field_ty(&variants[0].fields()[0], &args)?;
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
        alloc: &dyn ConstRead,
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
        if alloc.len() < len.checked_mul(elem_bytes)? {
            return None;
        }

        // Each element is read at its own offset through the per-field reader
        // (`read_field_from_alloc`): the slot clause throughout, so a pointer
        // element is its target's address and a compound element (a const
        // `[[E; N]; M]` lookup table, a struct element) recurses over its own
        // window with its relocations kept (`sub_window`). Without the
        // recursion such a table fell through to codegen_assign's
        // unconstrained-array fallback; without the window a pointer element
        // decoded to the offset its bytes carry.
        let read_elem = |i: usize| -> Option<Expr> {
            self.read_field_from_alloc(alloc, elem_ty, &elem_sort, i * elem_bytes)
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
    fn codegen_layout_from_alloc(&self, alloc: &dyn ConstRead) -> Option<Expr> {
        // `Layout { size: usize, align: Alignment }`: two data words.
        let size_value = alloc.read_uint_at(0, 8)?;
        let align_value = alloc.read_uint_at(8, 8)?;

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
        alloc: &dyn ConstRead,
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
            let value = alloc.read_uint_at(0, alloc.len())?;
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
        alloc: &dyn ConstRead,
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
        alloc: &dyn ConstRead,
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

    /// Read the value of type `field_ty` (sort `field_sort`) stored at
    /// `offset` in `alloc`, under the slot clause: a fieldless enum is its
    /// discriminant decoded from its own tag bytes, a bitvector slot is data
    /// or (pointer width) a stored pointer's value, a `bool` is a 0/1 byte,
    /// and a compound value recurses over its own window (`sub_window`, which
    /// rebases the relocations inside it). An uninitialized byte declines:
    /// it is not 0.
    pub(super) fn read_field_from_alloc(
        &self,
        alloc: &dyn ConstRead,
        field_ty: rustc_public::ty::Ty,
        field_sort: &ay_bindings::Sort,
        offset: usize,
    ) -> Option<Expr> {
        if let Some(bv_width) = field_sort.bitvec_width()
            && crate::codegen_ay::chc::expr::codegen_expr_constant_payload::ty_is_fieldless_enum(
                field_ty,
            )
        {
            // A fieldless enum field is its discriminant at the sort's width,
            // decoded from its own tag bytes (one byte for `Ordering`).
            let value =
                crate::codegen_ay::chc::expr::codegen_expr_constant_payload::fieldless_enum_const_bits(
                    field_ty, alloc, offset, bv_width,
                )?;
            return Some(Expr::bitvec_const(value, bv_width));
        }
        if let TyKind::RigidTy(RigidTy::Adt(def, _)) = field_ty.kind()
            && def.trimmed_name() == "TypeId"
            && field_sort.bitvec_width() == Some(128)
        {
            return Some(Expr::bitvec_const(Self::type_id_value(alloc, offset)?, 128));
        }
        if let Some(bv_width) = field_sort.bitvec_width() {
            self.read_bv_slot(alloc, offset, bv_width)
        } else if field_sort.is_bool() {
            Some(Expr::bool_const(alloc.read_bool_at(offset)?))
        } else {
            // Compound sort (Datatype, Array, etc.): recurse over the field's
            // own window, its relocations kept.
            let field_size = LayoutOf::new(field_ty).size_of()?;
            let window = alloc.sub_window(offset, field_size)?;
            self.codegen_scalar_from_bytes(&window, field_ty)
        }
    }
}

// Enum/float scalar extraction moved to operand_scalar_enum.rs per #4206.
