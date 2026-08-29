// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! ADT-type (enum, struct, Option-like, Result-like) extraction from constant
//! reference allocations.
//!
//! Extracted from codegen_decl_ref_const_extract.rs per #4147 (large-file decomposition).

use std::sync::Arc;

use super::ChcCtx;
use super::codegen_decl_flatten::byte_size_to_bv_width;
use super::codegen_expr_constant::{
    decode_non_unit_enum_variant_index, decode_option_like_variant_index,
    extract_payload_from_alloc,
};
use super::codegen_types::CodegenTypes;
use super::codegen_types_adt_sort::CodegenTypesAdtSort;
use crate::codegen_ay::chc::expr::codegen_expr_constant_payload::{
    const_payload_is_fat_ref, decode_fat_ref_const_parts,
};
use crate::codegen_ay::names;
use crate::kani_middle::abi::LayoutOf;
use ay_bindings::{Expr, Sort};
use tracing::debug;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Extract an ADT constant from a target allocation.
    ///
    /// Handles unit enums, single-variant structs, multi-variant enums,
    /// and Option-like 2-variant enums.
    pub(super) fn extract_adt_from_const_ref(
        target_alloc: &rustc_public::ty::Allocation,
        inner_ty: rustc_public::ty::Ty,
        def: rustc_public::ty::AdtDef,
        args: &rustc_public::ty::GenericArgs,
        memory_inits: &mut Vec<(Arc<str>, Sort, Expr, u32, u64)>,
        promoted_obj_id: u32,
    ) -> Option<Expr> {
        let variants = def.variants();
        if variants.iter().all(|v| v.fields().is_empty()) {
            return Self::extract_unit_enum_from_const_ref(target_alloc, def);
        }
        if variants.len() == 1 {
            return Self::extract_single_variant_adt_from_const_ref(
                target_alloc,
                inner_ty,
                args,
                &variants,
                memory_inits,
                promoted_obj_id,
            );
        }
        if let Some(expr) = Self::try_extract_multi_variant_enum(
            target_alloc,
            inner_ty,
            &variants,
            memory_inits,
            promoted_obj_id,
        ) {
            return Some(expr);
        }
        Self::dispatch_two_variant_enum(
            target_alloc,
            inner_ty,
            def,
            args,
            &variants,
            memory_inits,
            promoted_obj_id,
        )
    }

    /// Try multi-variant enum extraction (3+ variants or non-specialized 2-variant).
    fn try_extract_multi_variant_enum(
        target_alloc: &rustc_public::ty::Allocation,
        inner_ty: rustc_public::ty::Ty,
        variants: &[rustc_public::ty::VariantDef],
        memory_inits: &mut Vec<(Arc<str>, Sort, Expr, u32, u64)>,
        promoted_obj_id: u32,
    ) -> Option<Expr> {
        // Skip Option-like and Result-like 2-variant enums for specialized handlers.
        let skip_for_specialized = variants.len() == 2 && {
            let (v0, v1) = (variants[0].fields().len(), variants[1].fields().len());
            (v0 == 0 && v1 == 1) || (v0 == 1 && v1 == 0) || (v0 > 0 && v1 > 0)
        };
        if skip_for_specialized {
            return None;
        }
        let sort = Self::translate_ty(inner_ty)?;
        let dt = sort.datatype_sort()?;
        if dt.constructors.len() <= 1 {
            return None;
        }
        let variant_idx =
            decode_non_unit_enum_variant_index(target_alloc, inner_ty, variants.len())?;
        if variant_idx >= dt.constructors.len() {
            return None;
        }
        // READ the active variant's payload from the allocation. Zero-filling
        // the fields (the previous behavior) fabricated a value: `E::D(true)`
        // came back as `E::D(false)`, so `x == E::D(true)` was refutable — and
        // the reverse mistake would have PROVED a false equality. A field the
        // reader cannot decode aborts the whole extraction (fail-closed: the
        // caller then leaves the promoted object unconstrained).
        let mir_fields = variants.get(variant_idx)?.fields();
        let mut field_exprs: Vec<Expr> =
            Vec::with_capacity(dt.constructors[variant_idx].fields.len());
        for (field_idx, dt_field) in dt.constructors[variant_idx].fields.iter().enumerate() {
            let field_ty = mir_fields.get(field_idx)?.ty();
            field_exprs.push(read_variant_field_const(
                target_alloc,
                inner_ty,
                variant_idx,
                field_idx,
                field_ty,
                &dt_field.sort,
            )?);
        }
        let ctor_name = dt.constructors[variant_idx].name.clone();
        let dt_name = dt.name.clone();
        let expr = Expr::datatype_constructor(dt_name, ctor_name, field_exprs, sort);
        // Seed the promoted object's byte image so a reference to this constant
        // dereferences to the constant, not to an unconstrained memory cell.
        Self::seed_flattened_memory_init(
            target_alloc.bytes.len(),
            &expr,
            inner_ty,
            memory_inits,
            promoted_obj_id,
            0u64,
        );
        Some(expr)
    }

    /// Dispatch between Option-like and Result-like 2-variant enums.
    fn dispatch_two_variant_enum(
        target_alloc: &rustc_public::ty::Allocation,
        inner_ty: rustc_public::ty::Ty,
        def: rustc_public::ty::AdtDef,
        args: &rustc_public::ty::GenericArgs,
        variants: &[rustc_public::ty::VariantDef],
        memory_inits: &mut Vec<(Arc<str>, Sort, Expr, u32, u64)>,
        promoted_obj_id: u32,
    ) -> Option<Expr> {
        if variants.len() != 2 {
            return None;
        }
        let (v0, v1) = (variants[0].fields().len(), variants[1].fields().len());
        if v0 > 0 && v1 > 0 {
            return Self::extract_result_like_from_const_ref(
                target_alloc,
                inner_ty,
                def,
                args,
                variants,
                memory_inits,
                promoted_obj_id,
            );
        }
        if !((v0 == 0 && v1 == 1) || (v0 == 1 && v1 == 0)) {
            return None;
        }
        Self::extract_option_like_from_const_ref(
            target_alloc,
            inner_ty,
            def,
            args,
            variants,
            memory_inits,
            promoted_obj_id,
        )
    }

    /// Extract a unit enum discriminant as BV32 from a target allocation.
    fn extract_unit_enum_from_const_ref(
        target_alloc: &rustc_public::ty::Allocation,
        def: rustc_public::ty::AdtDef,
    ) -> Option<Expr> {
        use rustc_public::abi::IntegerType;
        let value = target_alloc.read_uint().ok()?;
        let discr_type = def.repr().int.unwrap_or(IntegerType::Pointer { is_signed: true });
        let is_signed = matches!(
            discr_type,
            IntegerType::Fixed { is_signed: true, .. } | IntegerType::Pointer { is_signed: true }
        );
        let repr_w = byte_size_to_bv_width(target_alloc.bytes.len());
        let masked = if repr_w < 128 { value & ((1u128 << repr_w) - 1) } else { value };
        let final_val =
            if is_signed && repr_w > 0 && repr_w < 32 && (masked & (1u128 << (repr_w - 1))) != 0 {
                masked | (0xFFFFFFFF & !((1u128 << repr_w) - 1))
            } else {
                masked & 0xFFFFFFFF
            };
        Some(Expr::bitvec_const(final_val, 32))
    }

    /// Extract a single-variant ADT (struct or single-variant enum).
    fn extract_single_variant_adt_from_const_ref(
        target_alloc: &rustc_public::ty::Allocation,
        inner_ty: rustc_public::ty::Ty,
        args: &rustc_public::ty::GenericArgs,
        variants: &[rustc_public::ty::VariantDef],
        memory_inits: &mut Vec<(Arc<str>, Sort, Expr, u32, u64)>,
        promoted_obj_id: u32,
    ) -> Option<Expr> {
        let sort = Self::translate_ty(inner_ty)?;
        // Layout-aware: rustc reorders `repr(Rust)` fields, so the constant's
        // bytes must be read at `field_offset(i)` and not at a running
        // declaration-order cursor. `RangeInclusive<u8>` is laid out
        // `start@0, exhausted@1, end@2`, and the sequential reader decoded
        // `&(0..=1)` as `start=0, end=0, exhausted=true`.
        let expr = Self::read_adt_composite_from_allocation(target_alloc, 0, inner_ty, &sort)?;
        debug!(?inner_ty, "const ref: multi-field struct extracted (#3470)");

        let adt_byte_width = target_alloc.bytes.len();
        Self::seed_single_variant_top_level(
            &sort,
            &expr,
            target_alloc,
            inner_ty,
            adt_byte_width,
            memory_inits,
            promoted_obj_id,
        );
        Self::seed_variant_fields(
            target_alloc,
            inner_ty,
            args,
            &variants[0],
            memory_inits,
            promoted_obj_id,
        );
        Some(expr)
    }

    /// Seed top-level memory init for a single-variant ADT (array or datatype).
    fn seed_single_variant_top_level(
        sort: &Sort,
        expr: &Expr,
        target_alloc: &rustc_public::ty::Allocation,
        inner_ty: rustc_public::ty::Ty,
        adt_byte_width: usize,
        memory_inits: &mut Vec<(Arc<str>, Sort, Expr, u32, u64)>,
        promoted_obj_id: u32,
    ) {
        if let Some(arr_sort) = sort.array_sort() {
            Self::seed_array_wrapper_memory_init(
                target_alloc,
                inner_ty,
                arr_sort,
                adt_byte_width,
                memory_inits,
                promoted_obj_id,
            );
        } else {
            Self::seed_flattened_memory_init(
                adt_byte_width,
                expr,
                inner_ty,
                memory_inits,
                promoted_obj_id,
                0u64,
            );
        }
    }

    /// Seed per-element memory for transparent array wrapper ADTs (e.g. SIMD).
    fn seed_array_wrapper_memory_init(
        target_alloc: &rustc_public::ty::Allocation,
        inner_ty: rustc_public::ty::Ty,
        arr_sort: &ay_bindings::ArraySort,
        adt_byte_width: usize,
        memory_inits: &mut Vec<(Arc<str>, Sort, Expr, u32, u64)>,
        promoted_obj_id: u32,
    ) {
        let Some(elem_bw) = arr_sort.element_sort.bitvec_width() else { return };
        let elem_byte_width = (elem_bw as usize) / 8;
        if elem_byte_width == 0 {
            return;
        }
        let array_len = adt_byte_width / elem_byte_width;
        let adt_type_key: Arc<str> = Arc::from(&*Self::type_key_for_ty(inner_ty));
        for i in 0..array_len {
            let offset = i * elem_byte_width;
            let mut value: u128 = 0;
            for b in 0..elem_byte_width {
                if let Some(Some(byte)) = target_alloc.bytes.get(offset + b) {
                    value |= (*byte as u128) << (b * 8);
                }
            }
            memory_inits.push((
                adt_type_key.clone(),
                arr_sort.element_sort.clone(),
                Expr::bitvec_const(value, elem_bw),
                promoted_obj_id,
                offset as u64,
            ));
        }
    }

    /// Seed per-field memory inits for a variant's fields from an allocation.
    fn seed_variant_fields(
        target_alloc: &rustc_public::ty::Allocation,
        inner_ty: rustc_public::ty::Ty,
        args: &rustc_public::ty::GenericArgs,
        variant: &rustc_public::ty::VariantDef,
        memory_inits: &mut Vec<(Arc<str>, Sort, Expr, u32, u64)>,
        promoted_obj_id: u32,
    ) {
        let inner_layout = LayoutOf::new(inner_ty);
        for (field_idx, field) in variant.fields().iter().enumerate() {
            let field_ty = field.ty();
            let Some(concrete_ty) =
                <ChcCtx as CodegenTypesAdtSort>::resolve_generic_ty(field_ty, args)
            else {
                continue;
            };
            let Some(field_sort) = Self::translate_ty(concrete_ty) else { continue };
            let Some(field_offset) = inner_layout.field_offset(field_idx) else { continue };
            let Some(field_expr) =
                Self::read_composite_from_allocation(target_alloc, field_offset, &field_sort)
            else {
                continue;
            };
            let Some((mem_sort, mem_expr)) =
                Self::flatten_field_for_memory_init(&field_expr, &field_sort, concrete_ty)
            else {
                continue;
            };
            let field_type_key = Self::type_key_for_ty(concrete_ty);
            memory_inits.push((
                Arc::from(&*field_type_key),
                mem_sort,
                mem_expr,
                promoted_obj_id,
                field_offset as u64,
            ));
        }
    }

    /// Extract an Option-like 2-variant enum constant from a target allocation.
    fn extract_option_like_from_const_ref(
        target_alloc: &rustc_public::ty::Allocation,
        inner_ty: rustc_public::ty::Ty,
        def: rustc_public::ty::AdtDef,
        args: &rustc_public::ty::GenericArgs,
        variants: &[rustc_public::ty::VariantDef],
        memory_inits: &mut Vec<(Arc<str>, Sort, Expr, u32, u64)>,
        promoted_obj_id: u32,
    ) -> Option<Expr> {
        let v0_fields = variants[0].fields().len();
        let some_idx = if v0_fields > 0 { 0usize } else { 1 };
        let some_fields = variants[some_idx].fields();
        let field = some_fields.first()?;
        let concrete_ty = <ChcCtx as CodegenTypesAdtSort>::resolve_generic_ty(field.ty(), args)?;
        // Sized-only deref: Option<&str> / Option<&[T]> payloads keep the
        // BV128 fat-pointer representation, matching the declared sort.
        let (payload_ty, _) = ChcCtx::deref_ref_ty_sized_only(concrete_ty);
        let payload_sort = ChcCtx::translate_ty(payload_ty)?;

        let option_name = ChcCtx::option_like_sort_name(def, args, payload_ty);
        let some_ctor = names::option_some_constructor_name(&option_name);
        let none_ctor = names::option_none_constructor_name(&option_name);
        let dt_sort = names::enum_sort(
            &option_name,
            names::option_constructors(&option_name, payload_sort.clone()),
        );
        let discriminant = decode_option_like_variant_index(
            target_alloc,
            inner_ty,
            concrete_ty,
            some_idx,
            variants.len(),
        )?;
        let dt_expr = Self::build_option_like_expr(
            target_alloc,
            inner_ty,
            concrete_ty,
            payload_ty,
            &payload_sort,
            &option_name,
            &some_ctor,
            &none_ctor,
            dt_sort,
            discriminant,
            some_idx,
            memory_inits,
            promoted_obj_id,
        )?;
        Self::seed_flattened_memory_init(
            target_alloc.bytes.len(),
            &dt_expr,
            inner_ty,
            memory_inits,
            promoted_obj_id,
            0u64,
        );
        Some(dt_expr)
    }

    /// Build the DT expression for an Option-like Some or None variant.
    #[allow(clippy::too_many_arguments)]
    fn build_option_like_expr(
        target_alloc: &rustc_public::ty::Allocation,
        inner_ty: rustc_public::ty::Ty,
        concrete_ty: rustc_public::ty::Ty,
        payload_ty: rustc_public::ty::Ty,
        payload_sort: &Sort,
        option_name: &str,
        some_ctor: &str,
        none_ctor: &str,
        dt_sort: Sort,
        discriminant: usize,
        some_idx: usize,
        memory_inits: &mut Vec<(Arc<str>, Sort, Expr, u32, u64)>,
        promoted_obj_id: u32,
    ) -> Option<Expr> {
        if discriminant == some_idx {
            let payload_expr = if const_payload_is_fat_ref(concrete_ty, payload_sort) {
                Self::extract_fat_ref_payload_from_const_ref(
                    target_alloc,
                    concrete_ty,
                    memory_inits,
                    promoted_obj_id,
                )?
            } else {
                extract_payload_from_alloc(target_alloc, concrete_ty, payload_sort)?
            };
            let payload_byte_offset =
                LayoutOf::new(inner_ty).variant_field_offset(some_idx, 0)? as u64;
            let payload_type_key = Self::type_key_for_ty(payload_ty);
            memory_inits.push((
                Arc::from(&*payload_type_key),
                payload_sort.clone(),
                payload_expr.clone(),
                promoted_obj_id,
                payload_byte_offset,
            ));
            let expr =
                Expr::datatype_constructor(option_name, some_ctor, vec![payload_expr], dt_sort);
            debug!(?option_name, discriminant, "const_ref_value: Option-like Some");
            Some(expr)
        } else {
            let expr = Expr::datatype_constructor(option_name, none_ctor, vec![], dt_sort);
            debug!(?option_name, discriminant, "const_ref_value: Option-like None");
            Some(expr)
        }
    }

    /// Extract a BV128 fat-pointer payload (`&str` / `&[T]`) from a constant
    /// enum allocation, seeding the literal's backing bytes into the promoted
    /// object's byte memory lane so the data pointer has real provenance.
    ///
    /// Returns `concat(len, data_ptr)` with `data_ptr = concat(obj_id, 0)`,
    /// mirroring the `&&str` handling of `extract_nested_str_from_const_ref`
    /// (#3607) which reuses the promoted object id for the transitively
    /// referenced literal bytes. Byte content is seeded only for `str` /
    /// `[u8]` pointees up to the same 64-byte elision threshold used by
    /// `extract_str_from_const_ref`; longer or non-byte content stays
    /// unconstrained (sound), while the length remains precise.
    fn extract_fat_ref_payload_from_const_ref(
        target_alloc: &rustc_public::ty::Allocation,
        concrete_ty: rustc_public::ty::Ty,
        memory_inits: &mut Vec<(Arc<str>, Sort, Expr, u32, u64)>,
        promoted_obj_id: u32,
    ) -> Option<Expr> {
        use rustc_public::ty::{RigidTy, TyKind, UintTy};

        let parts = decode_fat_ref_const_parts(target_alloc)?;
        let data_ptr =
            Expr::bitvec_const(promoted_obj_id as i128, 32).concat(Expr::bitvec_const(0i128, 32));

        let pointee_ty = match concrete_ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(_, inner, _) | RigidTy::RawPtr(inner, _)) => inner,
            _ => return None,
        };
        let is_byte_content = match pointee_ty.kind() {
            TyKind::RigidTy(RigidTy::Str) => true,
            TyKind::RigidTy(RigidTy::Slice(elem)) => {
                matches!(elem.kind(), TyKind::RigidTy(RigidTy::Uint(UintTy::U8)))
            }
            _ => false,
        };

        // Same elision threshold as extract_str_from_const_ref (#3617).
        const MAX_CONST_STR_INIT_BYTES: usize = 64;
        let len = usize::try_from(parts.len).ok()?;
        if is_byte_content && len <= MAX_CONST_STR_INIT_BYTES {
            let elem_type_key: Arc<str> = Arc::from("u8");
            for i in 0..len {
                let Some(byte) = parts.target_alloc.bytes.get(i).copied().flatten() else {
                    continue;
                };
                memory_inits.push((
                    Arc::clone(&elem_type_key),
                    Sort::bitvec(8),
                    Expr::bitvec_const(byte as u128, 8),
                    promoted_obj_id,
                    i as u64,
                ));
            }
        }

        let len_expr =
            Expr::bitvec_const(parts.len as u128, crate::codegen_ay::types::POINTER_WIDTH);
        debug!(
            len = parts.len,
            promoted_obj_id,
            byte_seeded = is_byte_content && len <= MAX_CONST_STR_INIT_BYTES,
            "const_ref_value: fat-pointer payload (concat(len, data_ptr))"
        );
        Some(len_expr.concat(data_ptr))
    }

    /// Extract a Result-like enum constant from a promoted allocation.
    ///
    /// Part of #3507: Handles 2-variant enums where both variants have fields.
    pub(super) fn extract_result_like_from_const_ref(
        target_alloc: &rustc_public::ty::Allocation,
        inner_ty: rustc_public::ty::Ty,
        def: rustc_public::ty::AdtDef,
        args: &rustc_public::ty::GenericArgs,
        variants: &[rustc_public::ty::VariantDef],
        memory_inits: &mut Vec<(Arc<str>, Sort, Expr, u32, u64)>,
        promoted_obj_id: u32,
    ) -> Option<Expr> {
        let adt_name = names::adt_sort_name(def, args);
        let (constructors_for_sort, variant_field_sorts) =
            Self::build_result_variant_sorts(&adt_name, variants, args)?;
        let dt_sort = names::enum_sort(&adt_name, constructors_for_sort);

        let discriminant = (*target_alloc.bytes.first()?)? as usize;
        if discriminant >= variants.len() {
            return None;
        }
        let active_ctor = names::scope_option_ctor(variants[discriminant].name(), &adt_name);
        let active_fields = &variant_field_sorts[discriminant];

        let payload_exprs = Self::extract_result_payload(
            target_alloc,
            inner_ty,
            args,
            &variants[discriminant],
            active_fields,
            discriminant,
            memory_inits,
            promoted_obj_id,
        )?;
        let dt_expr = Expr::datatype_constructor(&adt_name, &active_ctor, payload_exprs, dt_sort);
        debug!(adt_name = %adt_name, discriminant, active_ctor = %active_ctor,
            "const_ref_value: Result-like enum");
        Self::seed_flattened_memory_init(
            target_alloc.bytes.len(),
            &dt_expr,
            inner_ty,
            memory_inits,
            promoted_obj_id,
            0u64,
        );
        Some(dt_expr)
    }

    /// Build the DT sort info (constructor names + field sorts) for all variants.
    fn build_result_variant_sorts(
        adt_name: &str,
        variants: &[rustc_public::ty::VariantDef],
        args: &rustc_public::ty::GenericArgs,
    ) -> Option<(Vec<(String, Vec<(String, Sort)>)>, Vec<Vec<(String, Sort)>>)> {
        let mut ctors = Vec::with_capacity(variants.len());
        let mut field_sorts = Vec::with_capacity(variants.len());
        for variant in variants {
            let v_name = variant.name();
            let mut fields = Vec::with_capacity(variant.fields().len());
            for (idx, field) in variant.fields().iter().enumerate() {
                let concrete_ty =
                    <ChcCtx as CodegenTypesAdtSort>::resolve_generic_ty(field.ty(), args)?;
                let sort = ChcCtx::translate_ty(concrete_ty)?;
                fields.push((names::variant_field_name(&v_name, idx), sort));
            }
            ctors.push((names::scope_option_ctor(v_name, adt_name), fields.clone()));
            field_sorts.push(fields);
        }
        Some((ctors, field_sorts))
    }

    /// Extract payload expressions for the active variant of a Result-like enum.
    #[allow(clippy::too_many_arguments)]
    fn extract_result_payload(
        target_alloc: &rustc_public::ty::Allocation,
        inner_ty: rustc_public::ty::Ty,
        args: &rustc_public::ty::GenericArgs,
        active_variant: &rustc_public::ty::VariantDef,
        active_fields: &[(String, Sort)],
        discriminant: usize,
        memory_inits: &mut Vec<(Arc<str>, Sort, Expr, u32, u64)>,
        promoted_obj_id: u32,
    ) -> Option<Vec<Expr>> {
        if active_fields.len() == 1 {
            Self::extract_result_single_field_payload(
                target_alloc,
                inner_ty,
                args,
                active_variant,
                &active_fields[0],
                discriminant,
                memory_inits,
                promoted_obj_id,
            )
        } else {
            Self::extract_result_multi_field_payload(
                target_alloc,
                inner_ty,
                active_fields,
                discriminant,
            )
        }
    }

    /// Single-field variant payload extraction.
    #[allow(clippy::too_many_arguments)]
    fn extract_result_single_field_payload(
        target_alloc: &rustc_public::ty::Allocation,
        inner_ty: rustc_public::ty::Ty,
        args: &rustc_public::ty::GenericArgs,
        active_variant: &rustc_public::ty::VariantDef,
        (_, field_sort): &(String, Sort),
        discriminant: usize,
        memory_inits: &mut Vec<(Arc<str>, Sort, Expr, u32, u64)>,
        promoted_obj_id: u32,
    ) -> Option<Vec<Expr>> {
        let field_ty = active_variant.fields().first()?.ty();
        let concrete_ty = <ChcCtx as CodegenTypesAdtSort>::resolve_generic_ty(field_ty, args)?;
        // Sized-only deref: Result<&str, E> / Result<&[T], E> payloads keep
        // the BV128 fat-pointer representation, matching the declared sort.
        let (payload_ty, _) = ChcCtx::deref_ref_ty_sized_only(concrete_ty);
        let payload_sort = ChcCtx::translate_ty(payload_ty)?;
        let payload_expr = if const_payload_is_fat_ref(concrete_ty, &payload_sort) {
            Self::extract_fat_ref_payload_from_const_ref(
                target_alloc,
                concrete_ty,
                memory_inits,
                promoted_obj_id,
            )?
        } else {
            extract_payload_from_alloc(target_alloc, concrete_ty, &payload_sort)?
        };
        let payload_byte_offset =
            LayoutOf::new(inner_ty).variant_field_offset(discriminant, 0)? as u64;
        let payload_type_key = Self::type_key_for_ty(payload_ty);
        memory_inits.push((
            Arc::from(&*payload_type_key),
            field_sort.clone(),
            payload_expr.clone(),
            promoted_obj_id,
            payload_byte_offset,
        ));
        Some(vec![payload_expr])
    }

    /// Multi-field variant payload: read fields at layout-computed offsets.
    fn extract_result_multi_field_payload(
        target_alloc: &rustc_public::ty::Allocation,
        inner_ty: rustc_public::ty::Ty,
        active_fields: &[(String, Sort)],
        discriminant: usize,
    ) -> Option<Vec<Expr>> {
        let inner_layout = LayoutOf::new(inner_ty);
        let mut payload_exprs = Vec::with_capacity(active_fields.len());
        for (field_idx, (_field_name, field_sort)) in active_fields.iter().enumerate() {
            let fld_offset = inner_layout.variant_field_offset(discriminant, field_idx)?;
            if field_sort.is_bool() {
                let byte_val: u8 = target_alloc.bytes.get(fld_offset).copied()??;
                payload_exprs.push(Expr::bool_const(byte_val != 0));
            } else if let Some(bits) = field_sort.bitvec_width() {
                let fw = (bits as usize / 8).max(1);
                let mut value: u128 = 0;
                for b in 0..fw {
                    let byte_val: u8 = target_alloc.bytes.get(fld_offset + b).copied()??;
                    value |= (byte_val as u128) << (b * 8);
                }
                payload_exprs.push(Expr::bitvec_const(value, bits));
            } else {
                return None;
            }
        }
        Some(payload_exprs)
    }
}

/// Read ONE field of an enum variant out of a constant allocation.
///
/// ZST fields carry no bytes: the CHC model represents them with the canonical
/// `true` Bool sentinel (matching `extract_payload_from_alloc`), so reading
/// bytes for them would materialize a spurious `false`. Every other field is
/// read little-endian at the field's own layout offset within the variant.
/// Sorts the reader does not decode (datatypes, arrays) return `None` so the
/// caller drops the whole constant rather than inventing a value.
fn read_variant_field_const(
    alloc: &rustc_public::ty::Allocation,
    inner_ty: rustc_public::ty::Ty,
    variant_idx: usize,
    field_idx: usize,
    field_ty: rustc_public::ty::Ty,
    sort: &Sort,
) -> Option<Expr> {
    if LayoutOf::new(field_ty).size_of() == Some(0) {
        return if sort.is_bool() {
            Some(Expr::bool_const(true))
        } else {
            sort.bitvec_width().map(|w| Expr::bitvec_const(0u128, w))
        };
    }
    let offset = LayoutOf::new(inner_ty).variant_field_offset(variant_idx, field_idx)?;
    let byte_size = if sort.is_bool() { 1usize } else { (sort.bitvec_width()? / 8) as usize };
    if byte_size == 0 || offset + byte_size > alloc.bytes.len() {
        return None;
    }
    let mut value: u128 = 0;
    for (i, byte) in alloc.bytes.get(offset..offset + byte_size)?.iter().enumerate() {
        value |= ((*byte)? as u128) << (i * 8);
    }
    if sort.is_bool() {
        return Some(Expr::bool_const(value != 0));
    }
    let width = sort.bitvec_width()?;
    let masked = if width >= 128 { value } else { value & ((1u128 << width) - 1) };
    Some(Expr::bitvec_const(masked, width))
}
