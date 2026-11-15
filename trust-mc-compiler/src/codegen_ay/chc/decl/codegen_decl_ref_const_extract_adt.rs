// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! ADT-type (enum, struct, Option-like, Result-like) extraction from constant
//! reference allocations.
//!
//! Extracted from codegen_decl_ref_const_extract.rs per #4147 (large-file decomposition).

use crate::codegen_ay::shared::mono_ty;
#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use std::sync::Arc;

use super::ChcCtx;
use super::codegen_decl_flatten::byte_size_to_bv_width;
use super::codegen_expr_constant::{
    decode_non_unit_enum_variant_index, decode_option_like_variant_index,
    extract_payload_from_alloc,
};
use super::codegen_types::CodegenTypes;
use super::global_objects::InitSite;
use crate::codegen_ay::chc::expr::codegen_expr_constant_payload::{
    const_payload_is_fat_ref, fat_ref_const_ref, read_enum_variant_field_const,
};
use crate::codegen_ay::names;
use crate::codegen_ay::shared::const_pointer::{ConstPtr, ConstRead};
use crate::kani_middle::abi::LayoutOf;
use ay_bindings::{Expr, Sort};
use rustc_public::ty::{RigidTy, TyKind};
use tracing::debug;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Extract an ADT constant from a target allocation.
    ///
    /// Handles unit enums, single-variant structs, multi-variant enums,
    /// and Option-like 2-variant enums.
    pub(super) fn extract_adt_from_const_ref(
        &self,
        target_alloc: &dyn ConstRead,
        inner_ty: rustc_public::ty::Ty,
        def: rustc_public::ty::AdtDef,
        args: &rustc_public::ty::GenericArgs,
        memory_inits: &mut Vec<(Arc<str>, Sort, Expr, u32, u64)>,
        site: InitSite,
    ) -> Option<Expr> {
        let variants = def.variants();
        // Existing primitive Option payloads keep their established path.
        // Composite payloads previously could not be read by that scalar
        // extractor; admit them only with complete exact typed-memory seeds.
        if self.const_safe_value_supported(inner_ty, 0)
            && variants.iter().any(|variant| {
                variant.fields().iter().any(|field| {
                    mono_ty::field_ty(field, args).is_some_and(|ty| {
                        matches!(ty.kind(), TyKind::RigidTy(RigidTy::Tuple(_) | RigidTy::Adt(..)))
                    })
                })
            })
        {
            return self.decode_const_safe_window(target_alloc, inner_ty, memory_inits, site);
        }
        if variants.iter().all(|v| v.fields().is_empty()) {
            let expr = Self::extract_unit_enum_from_const_ref(target_alloc, def)?;
            // Seed the object's memory with the discriminant at the window's
            // offset (`InitSite`), as every other decoded constant does. `*r`
            // resolves through `const_ref_values` only while `r` is known to be
            // this one constant; a reference JOINED from two (`if b {
            // &Color::R } else { &Color::G }`) reads the typed memory at the
            // joined address, and with no seed that cell was unconstrained:
            // const_unit_enum_ref_safe (review_r01_const_ref_join.rs) FAILED
            // certified Genuine.
            if let Some(sort) = Self::translate_ty(inner_ty)
                && sort == *expr.sort()
            {
                memory_inits.push((
                    Arc::from(&*Self::type_key_for_ty(inner_ty)),
                    sort,
                    expr.clone(),
                    site.obj_id,
                    site.at(0),
                ));
            }
            return Some(expr);
        }
        if variants.len() == 1 {
            return self.extract_single_variant_adt_from_const_ref(
                target_alloc,
                inner_ty,
                args,
                &variants,
                memory_inits,
                site,
            );
        }
        if let Some(expr) = self.try_extract_multi_variant_enum(
            target_alloc,
            inner_ty,
            &variants,
            memory_inits,
            site,
        ) {
            return Some(expr);
        }
        self.dispatch_two_variant_enum(
            target_alloc,
            inner_ty,
            def,
            args,
            &variants,
            memory_inits,
            site,
        )
    }

    /// Try multi-variant enum extraction (3+ variants or non-specialized 2-variant).
    fn try_extract_multi_variant_enum(
        &self,
        target_alloc: &dyn ConstRead,
        inner_ty: rustc_public::ty::Ty,
        variants: &[rustc_public::ty::VariantDef],
        memory_inits: &mut Vec<(Arc<str>, Sort, Expr, u32, u64)>,
        site: InitSite,
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
            mir_fields.get(field_idx)?;
            let resolve = |ptr: &ConstPtr| self.const_ptr_address(ptr).map(|a| a.into_expr());
            field_exprs.push(read_enum_variant_field_const(
                target_alloc,
                inner_ty,
                variant_idx,
                field_idx,
                &dt_field.sort,
                &resolve,
            )?);
        }
        let ctor_name = dt.constructors[variant_idx].name.clone();
        let dt_name = dt.name.clone();
        let expr = Expr::datatype_constructor(dt_name, ctor_name, field_exprs, sort);
        // Seed the promoted object's byte image so a reference to this constant
        // dereferences to the constant, not to an unconstrained memory cell.
        Self::seed_flattened_memory_init(
            target_alloc.len(),
            &expr,
            inner_ty,
            memory_inits,
            site,
            0u64,
        );
        Some(expr)
    }

    /// Dispatch between Option-like and Result-like 2-variant enums.
    fn dispatch_two_variant_enum(
        &self,
        target_alloc: &dyn ConstRead,
        inner_ty: rustc_public::ty::Ty,
        def: rustc_public::ty::AdtDef,
        args: &rustc_public::ty::GenericArgs,
        variants: &[rustc_public::ty::VariantDef],
        memory_inits: &mut Vec<(Arc<str>, Sort, Expr, u32, u64)>,
        site: InitSite,
    ) -> Option<Expr> {
        if variants.len() != 2 {
            return None;
        }
        let (v0, v1) = (variants[0].fields().len(), variants[1].fields().len());
        if v0 > 0 && v1 > 0 {
            return self.extract_result_like_from_const_ref(
                target_alloc,
                inner_ty,
                def,
                args,
                variants,
                memory_inits,
                site,
            );
        }
        if !((v0 == 0 && v1 == 1) || (v0 == 1 && v1 == 0)) {
            return None;
        }
        self.extract_option_like_from_const_ref(
            target_alloc,
            inner_ty,
            def,
            args,
            variants,
            memory_inits,
            site,
        )
    }

    /// Extract a unit enum discriminant as BV32 from a target allocation.
    fn extract_unit_enum_from_const_ref(
        target_alloc: &dyn ConstRead,
        def: rustc_public::ty::AdtDef,
    ) -> Option<Expr> {
        use rustc_public::abi::IntegerType;
        let value = target_alloc.read_uint_at(0, target_alloc.len())?;
        let discr_type = def.repr().int.unwrap_or(IntegerType::Pointer { is_signed: true });
        let is_signed = matches!(
            discr_type,
            IntegerType::Fixed { is_signed: true, .. } | IntegerType::Pointer { is_signed: true }
        );
        let repr_w = byte_size_to_bv_width(target_alloc.len());
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
        &self,
        target_alloc: &dyn ConstRead,
        inner_ty: rustc_public::ty::Ty,
        args: &rustc_public::ty::GenericArgs,
        variants: &[rustc_public::ty::VariantDef],
        memory_inits: &mut Vec<(Arc<str>, Sort, Expr, u32, u64)>,
        site: InitSite,
    ) -> Option<Expr> {
        let sort = Self::translate_ty(inner_ty)?;
        // Layout-aware: rustc reorders `repr(Rust)` fields, so the constant's
        // bytes must be read at `field_offset(i)` and not at a running
        // declaration-order cursor. `RangeInclusive<u8>` is laid out
        // `start@0, exhausted@1, end@2`, and the sequential reader decoded
        // `&(0..=1)` as `start=0, end=0, exhausted=true`.
        let expr = self.read_adt_composite_from_allocation(target_alloc, 0, inner_ty, &sort)?;
        debug!(?inner_ty, "const ref: multi-field struct extracted (#3470)");

        let adt_byte_width = target_alloc.len();
        Self::seed_single_variant_top_level(
            &sort,
            &expr,
            target_alloc,
            inner_ty,
            adt_byte_width,
            memory_inits,
            site,
        );
        self.seed_variant_fields(target_alloc, inner_ty, args, &variants[0], memory_inits, site);
        Some(expr)
    }

    /// Seed top-level memory init for a single-variant ADT (array or datatype).
    fn seed_single_variant_top_level(
        sort: &Sort,
        expr: &Expr,
        target_alloc: &dyn ConstRead,
        inner_ty: rustc_public::ty::Ty,
        adt_byte_width: usize,
        memory_inits: &mut Vec<(Arc<str>, Sort, Expr, u32, u64)>,
        site: InitSite,
    ) {
        if let Some(arr_sort) = sort.array_sort() {
            Self::seed_array_wrapper_memory_init(
                target_alloc,
                inner_ty,
                arr_sort,
                adt_byte_width,
                memory_inits,
                site,
            );
        } else {
            Self::seed_flattened_memory_init(
                adt_byte_width,
                expr,
                inner_ty,
                memory_inits,
                site,
                0u64,
            );
        }
    }

    /// Seed per-element memory for transparent array wrapper ADTs (e.g. SIMD).
    fn seed_array_wrapper_memory_init(
        target_alloc: &dyn ConstRead,
        inner_ty: rustc_public::ty::Ty,
        arr_sort: &ay_bindings::ArraySort,
        adt_byte_width: usize,
        memory_inits: &mut Vec<(Arc<str>, Sort, Expr, u32, u64)>,
        site: InitSite,
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
            // Slot clause: an element that is not data (uninitialized, or under
            // a relocation) stays free; it was read as 0.
            let Some(value) = target_alloc.read_uint_at(offset, elem_byte_width) else {
                continue;
            };
            memory_inits.push((
                adt_type_key.clone(),
                arr_sort.element_sort.clone(),
                Expr::bitvec_const(value, elem_bw),
                site.obj_id,
                site.at(offset as u64),
            ));
        }
    }

    /// Seed per-field memory inits for a variant's fields from an allocation.
    fn seed_variant_fields(
        &self,
        target_alloc: &dyn ConstRead,
        inner_ty: rustc_public::ty::Ty,
        args: &rustc_public::ty::GenericArgs,
        variant: &rustc_public::ty::VariantDef,
        memory_inits: &mut Vec<(Arc<str>, Sort, Expr, u32, u64)>,
        site: InitSite,
    ) {
        let inner_layout = LayoutOf::new(inner_ty);
        for (field_idx, field) in variant.fields().iter().enumerate() {
            // The field's type with EVERY parameter substituted, at any depth
            // (Rule A, `shared::mono_ty::field_ty`). A shallow substitution
            // replaced only a field whose whole type is a parameter, so a field
            // typed `MaybeDangling<T>` kept its `T`, and the layout query in
            // `flatten_field_for_memory_init` panicked (`LayoutOf::new requires
            // layout for MaybeDangling<T>`) once the constant-pointer rule's
            // whole-object seeding (D2, `decl::global_objects`) decoded the
            // constants of `vec![10i32, 20].into_iter()` through this reader
            // (test_call_drop_terminator::test_vec_iter_concrete_elements_no_
            // unhandled_calls).
            let Some(concrete_ty) = mono_ty::field_ty(field, args) else { continue };
            let Some(field_sort) = Self::translate_ty(concrete_ty) else { continue };
            let Some(field_offset) = inner_layout.field_offset(field_idx) else { continue };
            let Some(field_expr) =
                self.read_composite_from_allocation(target_alloc, field_offset, &field_sort)
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
                site.obj_id,
                site.at(field_offset as u64),
            ));
        }
    }

    /// Extract an Option-like 2-variant enum constant from a target allocation.
    fn extract_option_like_from_const_ref(
        &self,
        target_alloc: &dyn ConstRead,
        inner_ty: rustc_public::ty::Ty,
        def: rustc_public::ty::AdtDef,
        args: &rustc_public::ty::GenericArgs,
        variants: &[rustc_public::ty::VariantDef],
        memory_inits: &mut Vec<(Arc<str>, Sort, Expr, u32, u64)>,
        site: InitSite,
    ) -> Option<Expr> {
        let v0_fields = variants[0].fields().len();
        let some_idx = if v0_fields > 0 { 0usize } else { 1 };
        let some_fields = variants[some_idx].fields();
        let field = some_fields.first()?;
        let concrete_ty = mono_ty::field_ty(field, args)?;
        // Sized-only deref: Option<&str> / Option<&[T]> payloads keep the
        // BV128 fat-pointer representation, matching the declared sort.
        let (payload_ty, _) = ChcCtx::deref_ref_ty_sized_only(concrete_ty);
        let payload_sort = ChcCtx::translate_ty(payload_ty)?;

        let option_name = ChcCtx::option_like_sort_name(def, args, payload_ty);
        let some_ctor = names::option_some_constructor_name(&option_name);
        let none_ctor = names::option_none_constructor_name(&option_name);
        let dt_sort = names::enum_sort(
            &option_name,
            ChcCtx::option_like_constructors(def, &option_name, payload_sort.clone()),
        );
        let discriminant = decode_option_like_variant_index(
            target_alloc,
            inner_ty,
            concrete_ty,
            some_idx,
            variants.len(),
        )?;
        let dt_expr = self.build_option_like_expr(
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
            site,
        )?;
        Self::seed_flattened_memory_init(
            target_alloc.len(),
            &dt_expr,
            inner_ty,
            memory_inits,
            site,
            0u64,
        );
        Some(dt_expr)
    }

    /// Build the DT expression for an Option-like Some or None variant.
    #[allow(clippy::too_many_arguments)]
    fn build_option_like_expr(
        &self,
        target_alloc: &dyn ConstRead,
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
        site: InitSite,
    ) -> Option<Expr> {
        if discriminant == some_idx {
            let payload_expr = if const_payload_is_fat_ref(concrete_ty, payload_sort) {
                self.extract_fat_ref_payload_from_const_ref(
                    target_alloc,
                    inner_ty,
                    some_idx,
                    concrete_ty,
                )?
            } else {
                let resolve = |ptr: &ConstPtr| self.const_ptr_address(ptr).map(|a| a.into_expr());
                extract_payload_from_alloc(
                    target_alloc,
                    inner_ty,
                    some_idx,
                    concrete_ty,
                    payload_sort,
                    &resolve,
                )?
            };
            let payload_byte_offset =
                LayoutOf::new(inner_ty).variant_field_offset(some_idx, 0)? as u64;
            let payload_type_key = Self::type_key_for_ty(payload_ty);
            memory_inits.push((
                Arc::from(&*payload_type_key),
                payload_sort.clone(),
                payload_expr.clone(),
                site.obj_id,
                site.at(payload_byte_offset),
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

    /// Extract a BV128 fat-pointer payload (`&str` / `&[T]`) of variant
    /// `variant_idx` from a constant enum window: `concat(len, data_ptr)`.
    ///
    /// The payload is the fat pointer stored at its variant field's offset:
    /// the data pointer is that relocation's target's OWN object plus its
    /// offset (`const_ptr_address`), and the length is the word beside it
    /// (`fat_ref_const_ref`). The literal's bytes are seeded at the literal's
    /// own object by D2 (`note_object_read`), never at the enclosing
    /// constant's object (which gave one allocation two objects).
    fn extract_fat_ref_payload_from_const_ref(
        &self,
        target_alloc: &dyn ConstRead,
        enum_ty: rustc_public::ty::Ty,
        variant_idx: usize,
        concrete_ty: rustc_public::ty::Ty,
    ) -> Option<Expr> {
        use rustc_public::ty::{RigidTy, TyKind};

        let pointee_ty = match concrete_ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(_, inner, _) | RigidTy::RawPtr(inner, _)) => inner,
            _ => return None,
        };
        let slot = LayoutOf::new(enum_ty).variant_field_offset(variant_idx, 0).unwrap_or(0);
        let r = fat_ref_const_ref(target_alloc, slot, pointee_ty)?;
        let data_ptr = self.const_ptr_address(&r.ptr)?.into_expr();
        let len = r.metadata?;
        if let Some(key) = r.ptr.key() {
            self.note_object_read_deferred(key, pointee_ty);
        }
        debug!(len, "const_ref_value: fat-pointer payload (concat(len, data_ptr))");
        Some(
            Expr::bitvec_const(u128::from(len), crate::codegen_ay::types::POINTER_WIDTH)
                .concat(data_ptr),
        )
    }

    /// Extract a Result-like enum constant from a promoted allocation.
    ///
    /// Part of #3507: Handles 2-variant enums where both variants have fields.
    pub(super) fn extract_result_like_from_const_ref(
        &self,
        target_alloc: &dyn ConstRead,
        inner_ty: rustc_public::ty::Ty,
        def: rustc_public::ty::AdtDef,
        args: &rustc_public::ty::GenericArgs,
        variants: &[rustc_public::ty::VariantDef],
        memory_inits: &mut Vec<(Arc<str>, Sort, Expr, u32, u64)>,
        site: InitSite,
    ) -> Option<Expr> {
        let adt_name = names::adt_sort_name(def, args);
        let (constructors_for_sort, variant_field_sorts) =
            Self::build_result_variant_sorts(&adt_name, variants, args)?;
        let dt_sort = names::enum_sort(&adt_name, constructors_for_sort);

        // The tag at the layout's tag field, under the slot clause — not the
        // raw byte 0 (a niche-encoded Result-like has no tag byte there).
        let discriminant =
            decode_non_unit_enum_variant_index(target_alloc, inner_ty, variants.len())?;
        if discriminant >= variants.len() {
            return None;
        }
        let active_ctor = names::scope_option_ctor(variants[discriminant].name(), &adt_name);
        let active_fields = &variant_field_sorts[discriminant];

        let payload_exprs = self.extract_result_payload(
            target_alloc,
            inner_ty,
            args,
            &variants[discriminant],
            active_fields,
            discriminant,
            memory_inits,
            site,
        )?;
        let dt_expr = Expr::datatype_constructor(&adt_name, &active_ctor, payload_exprs, dt_sort);
        debug!(adt_name = %adt_name, discriminant, active_ctor = %active_ctor,
            "const_ref_value: Result-like enum");
        Self::seed_flattened_memory_init(
            target_alloc.len(),
            &dt_expr,
            inner_ty,
            memory_inits,
            site,
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
                let concrete_ty = mono_ty::field_ty(field, args)?;
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
        &self,
        target_alloc: &dyn ConstRead,
        inner_ty: rustc_public::ty::Ty,
        args: &rustc_public::ty::GenericArgs,
        active_variant: &rustc_public::ty::VariantDef,
        active_fields: &[(String, Sort)],
        discriminant: usize,
        memory_inits: &mut Vec<(Arc<str>, Sort, Expr, u32, u64)>,
        site: InitSite,
    ) -> Option<Vec<Expr>> {
        if active_fields.len() == 1 {
            self.extract_result_single_field_payload(
                target_alloc,
                inner_ty,
                args,
                active_variant,
                &active_fields[0],
                discriminant,
                memory_inits,
                site,
            )
        } else {
            self.extract_result_multi_field_payload(
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
        &self,
        target_alloc: &dyn ConstRead,
        inner_ty: rustc_public::ty::Ty,
        args: &rustc_public::ty::GenericArgs,
        active_variant: &rustc_public::ty::VariantDef,
        (_, field_sort): &(String, Sort),
        discriminant: usize,
        memory_inits: &mut Vec<(Arc<str>, Sort, Expr, u32, u64)>,
        site: InitSite,
    ) -> Option<Vec<Expr>> {
        let concrete_ty = mono_ty::field_ty(active_variant.fields().first()?, args)?;
        // Sized-only deref: Result<&str, E> / Result<&[T], E> payloads keep
        // the BV128 fat-pointer representation, matching the declared sort.
        let (payload_ty, _) = ChcCtx::deref_ref_ty_sized_only(concrete_ty);
        let payload_sort = ChcCtx::translate_ty(payload_ty)?;
        let payload_expr = if const_payload_is_fat_ref(concrete_ty, &payload_sort) {
            self.extract_fat_ref_payload_from_const_ref(
                target_alloc,
                inner_ty,
                discriminant,
                concrete_ty,
            )?
        } else {
            let resolve = |ptr: &ConstPtr| self.const_ptr_address(ptr).map(|a| a.into_expr());
            extract_payload_from_alloc(
                target_alloc,
                inner_ty,
                discriminant,
                concrete_ty,
                &payload_sort,
                &resolve,
            )?
        };
        let payload_byte_offset =
            LayoutOf::new(inner_ty).variant_field_offset(discriminant, 0)? as u64;
        let payload_type_key = Self::type_key_for_ty(payload_ty);
        memory_inits.push((
            Arc::from(&*payload_type_key),
            field_sort.clone(),
            payload_expr.clone(),
            site.obj_id,
            site.at(payload_byte_offset),
        ));
        Some(vec![payload_expr])
    }

    /// Multi-field variant payload: read fields at layout-computed offsets.
    fn extract_result_multi_field_payload(
        &self,
        target_alloc: &dyn ConstRead,
        inner_ty: rustc_public::ty::Ty,
        active_fields: &[(String, Sort)],
        discriminant: usize,
    ) -> Option<Vec<Expr>> {
        // Each field at its own layout offset over exactly its own bytes; a
        // fieldless enum field as its sign-extended discriminant.
        let mut payload_exprs = Vec::with_capacity(active_fields.len());
        for (field_idx, (_field_name, field_sort)) in active_fields.iter().enumerate() {
            let resolve = |ptr: &ConstPtr| self.const_ptr_address(ptr).map(|a| a.into_expr());
            payload_exprs.push(read_enum_variant_field_const(
                target_alloc,
                inner_ty,
                discriminant,
                field_idx,
                field_sort,
                &resolve,
            )?);
        }
        Some(payload_exprs)
    }
}
