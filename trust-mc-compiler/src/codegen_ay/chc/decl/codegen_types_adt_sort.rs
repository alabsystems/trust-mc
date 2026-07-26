// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! ADT field-based sort construction and iterator type translation.
//!
//! Contains:
//! - `translate_into_iter_sort`: IntoIter variant dispatch (Vec, Array, HashMap, HashSet)
//! - `translate_adt_sort`: generic ADT field-by-field sort construction
//! - `resolve_generic_ty`: Param type resolution from generic args
//! - `adt_sort_name`: unique SMT sort name for generic ADT
//! - `is_opaque_alloc_infra`: allocator/fmt infrastructure detection
//!
//! Extracted from include!() to proper module via extension trait pattern.
//! Part of #2306: include!() to proper module migration.

use ay_bindings::Sort;
use rustc_public::CrateDef;
use rustc_public::ty::{AdtDef, AdtKind, GenericArgKind, GenericArgs, RigidTy, TyKind};
use tracing::debug;

use crate::codegen_ay::types::{bool_sort, bv8_sort, flatten_dt_array_element, ptr_sort};

use super::ChcCtx;
use super::codegen_decl_flatten::byte_size_to_bv_width;
use super::codegen_types::CodegenTypes;
use super::codegen_types_adt::CodegenTypesAdt;
use super::names::{self, enum_sort, struct_sort};

/// Extension trait for ADT field-based sort construction on `ChcCtx`.
pub(in crate::codegen_ay::chc) trait CodegenTypesAdtSort<'tcx, 'body> {
    #[must_use]
    fn translate_into_iter_sort(def: AdtDef, args: &GenericArgs) -> Option<Sort>;
    #[must_use]
    fn translate_adt_sort(def: AdtDef, args: GenericArgs) -> Option<Sort>;
    fn resolve_generic_ty(
        ty: rustc_public::ty::Ty,
        args: &GenericArgs,
    ) -> Option<rustc_public::ty::Ty>;
    fn adt_sort_name(def: AdtDef, args: &GenericArgs) -> String;
    fn is_opaque_alloc_infra(def: AdtDef) -> bool;
    fn is_hashbrown_internal(def: AdtDef) -> bool;
}

impl<'tcx, 'body> CodegenTypesAdtSort<'tcx, 'body> for ChcCtx<'tcx, 'body> {
    /// Translates standard-library IntoIter variants (Vec, Array, HashMap, HashSet).
    fn translate_into_iter_sort(def: AdtDef, args: &GenericArgs) -> Option<Sort> {
        let full_name = def.0.name();

        // HashMap/HashSet IntoIter
        let is_hashset_into_iter = full_name.contains("hash_set") || full_name.contains("HashSet");
        let is_hashmap_into_iter = full_name.contains("hash_map") || full_name.contains("HashMap");

        if is_hashset_into_iter {
            debug!(full_name = ?full_name, "HashSet IntoIter -> HashSetIntoIter sort");
            let key_sort = Self::translate_type_arg_sort_or_param_bv(
                Self::nth_type_arg(args, 0),
                "HashSet IntoIter key sort",
                ptr_sort(),
            );
            // Part of #2267: Cow<str> auto-derefs to &str for name functions.
            let type_suffix = names::sort_short_name(&key_sort);
            let set_sort = Sort::array(key_sort.clone(), bool_sort());
            let keys_sort = Sort::array(ptr_sort(), key_sort);

            return Some(struct_sort(
                names::hashset_into_iter_sort_name(&type_suffix),
                names::hashset_iter_fields(set_sort, keys_sort),
            ));
        }

        if is_hashmap_into_iter {
            debug!(full_name = ?full_name, "HashMap IntoIter -> HashMapIntoIter sort");
            let key_sort = Self::translate_type_arg_sort_or_param_bv(
                Self::nth_type_arg(args, 0),
                "HashMap IntoIter key sort",
                ptr_sort(),
            );
            let val_sort = Self::translate_type_arg_sort_or_param_bv(
                Self::nth_type_arg(args, 1),
                "HashMap IntoIter value sort",
                ptr_sort(),
            );
            // Part of #2267: Cow<str> auto-derefs to &str for name functions.
            let key_type_suffix = names::sort_short_name(&key_sort);
            let val_type_suffix = names::sort_short_name(&val_sort);

            // Part of #3057: DT-free parallel-array encoding.
            let data_sort = Sort::array(key_sort.clone(), val_sort);
            let present_sort = Sort::array(key_sort.clone(), bool_sort());
            let keys_sort = Sort::array(ptr_sort(), key_sort);

            return Some(struct_sort(
                names::hashmap_into_iter_sort_name(&key_type_suffix, &val_type_suffix),
                names::hashmap_iter_fields(data_sort, present_sort, keys_sort),
            ));
        }

        // Vec IntoIter
        let is_vec_into_iter = full_name.contains("vec::into_iter")
            || full_name.contains("vec::IntoIter")
            || full_name.contains("alloc::vec")
            || full_name.starts_with("alloc::vec")
            || full_name.contains("std::vec");

        if is_vec_into_iter {
            debug!(full_name = ?full_name, "Vec IntoIter -> VecIntoIter sort");
            let elem_sort = Self::translate_type_arg_sort_or_param_bv(
                Self::nth_type_arg(args, 0),
                "Vec IntoIter element sort",
                Sort::bitvec(32),
            );
            // Part of #2990: flatten DT elements to BV for PDR compatibility.
            let elem_sort = flatten_dt_array_element(elem_sort);
            // Part of #2267: Cow<str> auto-derefs to &str for name functions.
            let type_suffix = names::sort_short_name(&elem_sort);
            let array_sort = Sort::array(ptr_sort(), elem_sort);
            let vec_sort =
                struct_sort(names::vec_sort_name(&type_suffix), names::vec_fields(array_sort));

            return Some(struct_sort(
                names::vec_into_iter_sort_name(&type_suffix),
                names::vec_into_iter_fields(vec_sort),
            ));
        }

        let is_array_into_iter = full_name.contains("core::array::")
            || full_name.contains("std::array::")
            || full_name.contains("array::iter::IntoIter")
            || full_name.contains("array::IntoIter");
        if !is_array_into_iter {
            debug!(
                full_name = ?full_name,
                "unrecognized IntoIter path -> generic ADT translation"
            );
            return None;
        }

        // Array IntoIter: wraps PolymorphicIter
        debug!(full_name = ?full_name, "Array IntoIter -> Datatype sort");
        let elem_sort = Self::translate_type_arg_sort_or_param_bv(
            Self::nth_type_arg(args, 0),
            "Array IntoIter element sort",
            bv8_sort(),
        );
        // Part of #2990: flatten DT elements to BV for PDR compatibility.
        let elem_sort = flatten_dt_array_element(elem_sort);
        let data_sort = Sort::array(ptr_sort(), elem_sort);
        let poly_iter_sort = struct_sort(
            "PolymorphicIter",
            [("fld_alive", names::index_range_sort()), ("fld_data", data_sort)],
        );
        Some(struct_sort("IntoIter", [("fld_inner", poly_iter_sort)]))
    }

    /// Translates an ADT (struct/enum) to a AY sort via field inspection.
    ///
    /// Handles: unit enums, Option-like enums, structs, general enums.
    fn translate_adt_sort(def: AdtDef, args: GenericArgs) -> Option<Sort> {
        let variants = def.variants();
        let adt_name = Self::adt_sort_name(def, &args);

        // Unit enum: all variants have no fields (only applies to actual enums,
        // not structs — 0-field structs are ZSTs handled below).
        let is_unit_enum =
            def.kind() == AdtKind::Enum && variants.iter().all(|v| v.fields().is_empty());
        if is_unit_enum {
            let num_variants = variants.len();
            let bits = if num_variants <= 65536 { 32 } else { 64 };
            return Some(Sort::bitvec(bits));
        }

        // Option-like enum: 2 variants, one empty + one with 1 field
        if variants.len() == 2 {
            let v0_fields = variants[0].fields().len();
            let v1_fields = variants[1].fields().len();

            if (v0_fields == 0 && v1_fields == 1) || (v0_fields == 1 && v1_fields == 0) {
                let some_idx = if v0_fields > 0 { 0 } else { 1 };
                let some_variant = &variants[some_idx];

                if let Some(field) = some_variant.fields().first() {
                    // Part of #4114: Use ty_with_args for associated type projection resolution.
                    let concrete_ty = field.ty_with_args(&args);
                    {
                        // Keep refs to unsized fat-pointer pointees (&str, &[T])
                        // intact: their payload is the BV128 fat-pointer value,
                        // matching the value path (translate_ty on Ref).
                        let (payload_ty, _payload_is_ref) =
                            Self::deref_ref_ty_sized_only(concrete_ty);
                        if let Some(payload_sort) = Self::translate_ty(payload_ty) {
                            // Part of #3945: When the payload is a hashbrown internal
                            // (Bucket, RawTable, etc.), derive the Option name from the
                            // payload *sort* (bv64) rather than the type name. This produces
                            // `Option_bv64` instead of `Option_hashbrown_raw_Bucket_K_V`,
                            // avoiding a duplicate datatype whose `value` accessor triggers
                            // Z3 PDR's "Uninterpreted 'value'" error.
                            let option_name = if matches!(payload_ty.kind(), TyKind::RigidTy(RigidTy::Adt(inner_def, _)) if Self::is_hashbrown_internal(inner_def))
                            {
                                names::option_sort_name(&names::sort_short_name(&payload_sort))
                            } else {
                                Self::option_like_sort_name(def, &args, payload_ty)
                            };
                            return Some(enum_sort(
                                &option_name,
                                names::option_constructors(&option_name, payload_sort),
                            ));
                        }
                    }
                }
            }
        }

        // Structs: single variant with named fields
        if def.kind() == AdtKind::Struct && !variants.is_empty() {
            let variant = &variants[0];

            // Part of #3041: ZST structs (0 fields) encode as Bool, matching
            // the convention for () (unit type). Without this, empty Datatypes
            // get converted to BitVec(32) by AY/Z3, causing sort mismatches
            // in enum BV-flattening and inconsistent ZST value representation.
            // Extended: also collapse a 1+-field struct that is itself a ZST (every
            // field a ZST, e.g. `TryFromIntError(())`), so the CHC sort agrees with the
            // BMC path (sort_inference_adt.rs) and the value-side Bool sentinel — without
            // it, `Result<_, TryFromIntError>` is malformed and unwrap_or is unsolvable.
            let is_zst_struct = variant.fields().is_empty()
                || rustc_public::ty::Ty::from_rigid_kind(RigidTy::Adt(def, args.clone()))
                    .layout()
                    .ok()
                    .is_some_and(|l| l.shape().is_sized() && l.shape().size.bytes() == 0);
            if is_zst_struct {
                return Some(bool_sort());
            }

            let mut fields = Vec::with_capacity(variant.fields().len());

            for field in variant.fields() {
                // Part of #4114: Use ty_with_args to resolve associated type
                // projections (e.g., <Chars as IntoIterator>::IntoIter → Chars).
                // field.ty() returns the raw definition type which may contain
                // unresolved projections; resolve_generic_ty only handles Param.
                let concrete_ty = field.ty_with_args(&args);
                let field_ty = concrete_ty;
                // Part of #3883: References/raw pointers to dyn Trait are fat pointers
                // (data ptr + vtable ptr). translate_ty maps all Ref/RawPtr to
                // ptr_sort() (BV64), but dyn coercion produces Dyn_Trait{BV64, BV64}.
                // Use the fat pointer sort so collect_leaf_sorts flattens to 2 slots,
                // matching the actual coerced value and enabling reconstruction.
                // resolve_generic_ty only resolves top-level Param types,
                // not params nested inside Ref/RawPtr. For `&'a T` where
                // T = dyn Trait, the pointee is still Param. Resolve it here.
                let is_dyn_fat_ptr = match concrete_ty.kind() {
                    TyKind::RigidTy(RigidTy::Ref(_, pointee, _))
                    | TyKind::RigidTy(RigidTy::RawPtr(pointee, _)) => {
                        let resolved_pointee =
                            Self::resolve_generic_ty(pointee, &args).unwrap_or(pointee);
                        matches!(resolved_pointee.kind(), TyKind::RigidTy(RigidTy::Dynamic(..)))
                    }
                    _ => false,
                };
                let sort = if is_dyn_fat_ptr {
                    let dyn_name = names::dyn_sort_name("Trait");
                    struct_sort(dyn_name, [("fld_ptr", ptr_sort()), ("fld_vtable", ptr_sort())])
                } else {
                    Self::translate_ty(concrete_ty).or_else(|| {
                        // Part of #3596: Handle parameterized array fields like [T; N]
                        // where T is a generic param. resolve_generic_ty only resolves
                        // top-level Param types but not params nested inside Array types.
                        // For #[repr(simd)] structs (e.g., CustomSimd<T, N>([T; N])),
                        // the field type [T; N] has an unresolved elem param that
                        // translate_ty cannot process, causing BV32 fallback.
                        if let TyKind::RigidTy(RigidTy::Array(elem_ty, _)) = field_ty.kind() {
                            let resolved_elem = Self::resolve_generic_ty(elem_ty, &args)?;
                            let elem_sort = Self::translate_ty(resolved_elem)?;
                            let elem_sort = flatten_dt_array_element(elem_sort);
                            Some(Sort::array(ptr_sort(), elem_sort))
                        } else {
                            None
                        }
                    })?
                };
                fields.push((names::adt_struct_field_name(&field.name), sort));
            }

            return Some(struct_sort(adt_name, fields));
        }

        // General enums
        if def.kind() == AdtKind::Enum {
            let mut constructors = Vec::with_capacity(variants.len());

            for variant in &variants {
                // Cache per-variant: avoids N+1 String allocations per variant
                // (N field iterations + 1 for constructor name). Part of #2267.
                let v_name = variant.name();
                let mut fields = Vec::with_capacity(variant.fields().len());
                for (idx, field) in variant.fields().iter().enumerate() {
                    // Part of #4114: Use ty_with_args for associated type projection resolution.
                    let concrete_ty = field.ty_with_args(&args);
                    // Apply deref_ref_ty for &[T; N] fields so that general enum
                    // paths (Result<&[T; N], E>) use Array sort, matching the
                    // Option-like path. Without this, Option uses Array(BV64, BV8)
                    // but Result uses BV64 for the same `&[u8; 8]` field, causing
                    // Z3 "unknown constant" errors when values flow between them.
                    // Sized-only: &str / &[T] stay BV128 fat pointers.
                    let (deref_ty, _is_ref) = Self::deref_ref_ty_sized_only(concrete_ty);
                    let use_deref = matches!(deref_ty.kind(), TyKind::RigidTy(RigidTy::Array(..)))
                        && deref_ty != concrete_ty;
                    let field_ty = if use_deref { deref_ty } else { concrete_ty };
                    let sort = Self::translate_ty(field_ty).or_else(|| {
                        // Part of #3596: same parameterized-array fallback as structs.
                        if let TyKind::RigidTy(RigidTy::Array(elem_ty, _)) = field_ty.kind() {
                            let resolved_elem = Self::resolve_generic_ty(elem_ty, &args)?;
                            let elem_sort = Self::translate_ty(resolved_elem)?;
                            let elem_sort = flatten_dt_array_element(elem_sort);
                            Some(Sort::array(ptr_sort(), elem_sort))
                        } else {
                            None
                        }
                    })?;
                    fields.push((names::variant_field_name(&v_name, idx), sort));
                }
                // Part of #2549: Scope Option constructor names.
                constructors.push((names::scope_option_ctor(v_name, &adt_name), fields));
            }

            return Some(enum_sort(adt_name, constructors));
        }

        // Part of #3669: Union types — model as bitvector of the union's byte size.
        // Unions overlay all variants in the same memory, so the sort must represent
        // the full allocation. MaybeUninit<T> is the primary consumer (array iterators).
        // Name-based transparent wrappers (codegen_types_adt.rs) catch MaybeUninit
        // before reaching here, but this handles the general case.
        if def.kind() == AdtKind::Union {
            if let Ok(layout) =
                rustc_public::ty::Ty::from_rigid_kind(RigidTy::Adt(def, args)).layout()
            {
                let byte_size = layout.shape().size.bytes();
                if byte_size == 0 {
                    debug!(adt_name, "union ADT (0 bytes) -> Bool (ZST)");
                    return Some(bool_sort());
                }
                let bits = byte_size_to_bv_width(byte_size);
                debug!(adt_name, byte_size, bits, "union ADT -> bitvec");
                return Some(Sort::bitvec(bits));
            }
            // Layout unavailable — fall through to None
            debug!(adt_name, "union ADT layout unavailable");
        }

        None
    }

    /// Resolves a generic type parameter using the provided generic arguments.
    fn resolve_generic_ty(
        ty: rustc_public::ty::Ty,
        args: &GenericArgs,
    ) -> Option<rustc_public::ty::Ty> {
        match ty.kind() {
            TyKind::Param(param_ty) => {
                let idx = param_ty.index as usize;
                if let Some(arg) = args.0.get(idx) {
                    match arg {
                        GenericArgKind::Type(resolved_ty) => Some(*resolved_ty),
                        _ => None, // external enum: GenericArgKind
                    }
                } else {
                    None
                }
            }
            _ => Some(ty), // external enum: TyKind
        }
    }

    /// Build a unique SMT sort name for a generic enum ADT.
    fn adt_sort_name(def: AdtDef, args: &GenericArgs) -> String {
        names::adt_sort_name(def, args)
    }

    /// Returns true if this ADT is from allocator/fmt infrastructure and should
    /// be modeled as an opaque bitvector instead of an SMT datatype.
    fn is_opaque_alloc_infra(def: AdtDef) -> bool {
        let name = def.trimmed_name();
        let full_path = def.0.name();

        if matches!(name.as_str(), "Layout" | "Alignment" | "AllocError" | "Infallible" | "NonNull")
        {
            return true;
        }
        if name == "Arguments" && full_path.contains("fmt") {
            return true;
        }
        // Part of #3521: ControlFlow is now a proper Datatype (not opaque BV128).
        // Removed from opaque alloc infra to allow Datatype encoding.

        let is_alloc_module = full_path.contains("alloc::alloc::")
            || full_path.contains("alloc::raw_vec::")
            || full_path.contains("core::alloc::")
            || full_path.contains("std::alloc::");
        let is_fmt_module = full_path.contains("core::fmt::") || full_path.contains("std::fmt::");

        is_alloc_module || is_fmt_module
    }

    /// Returns true if this ADT is a hashbrown internal type that should be
    /// modeled as an opaque pointer instead of an SMT datatype.
    ///
    /// Part of #3945: hashbrown types like Bucket, RawTable, RawTableInner leak
    /// through drop glue into the CHC encoding. Without interception, they become
    /// Datatype sorts that are referenced in rule bodies but never declared,
    /// causing Z3 "unknown sort" errors.
    fn is_hashbrown_internal(def: AdtDef) -> bool {
        let full_path = def.0.name();
        full_path.contains("hashbrown::raw::")
            || full_path.contains("hashbrown::map::")
            || full_path.contains("hashbrown::set::")
    }
}
