// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! AY Sort inference from Rust types.
//!
//! This module provides functions to infer AY SMT sorts from Rust type
//! information (MIR types, ADT definitions, generic arguments).
//!
//! Key functions:
//! - `infer_sort_from_ty` - Main entry point for type-to-sort conversion
//! - `infer_adt_sort` - ADT (enum/struct) sort inference (in sort_inference_adt.rs)
//! - `infer_tuple_sort` - Tuple sort inference
//! - `slice_sort` - Fat pointer (slice) sort construction
//! - `dyn_sort` - Fat pointer (trait object) sort construction (#1140)
//! - `resolve_generic_ty` - Generic parameter resolution
//! - `try_infer_sort_from_compound_ty` - Compound type inference
//! - `tuple_sort_name` - Tuple sort naming
//!
//! Note: `sort_short_name` has been consolidated into `names.rs` (Fix #817)
//! ADT-specific sort inference extracted to `sort_inference_adt.rs` (Part of #2246)

use crate::codegen_ay::coroutine_layout::build_coroutine_sort_info;
use crate::codegen_ay::names::{self, struct_sort};
use crate::codegen_ay::type_depth_guard::TypeDepthGuard;
use crate::codegen_ay::types::{
    bool_sort, bv8_sort, float_ty_to_bitvec_width, int_sort, int_ty_to_bitvec_width, ptr_sort,
    uint_ty_to_bitvec_width,
};
use ay_bindings::{Sort, SortInner};
use rustc_middle::ty::tls;
use rustc_public::CrateDef;
use rustc_public::ty::{AdtDef, GenericArgs, RigidTy, TyKind};

use super::StatementCodegen;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Infer AY sort from a Rust type.
    ///
    /// This is the main entry point for converting Rust types to AY SMT sorts.
    /// Handles primitives (bool, integers, floats), pointers, tuples, arrays,
    /// slices, and ADTs (enums/structs).
    /// Protected by `TypeDepthGuard` to prevent stack overflow on deeply
    /// nested or self-referential types.
    #[must_use]
    pub(super) fn infer_sort_from_ty(ty: rustc_public::ty::Ty) -> Option<Sort> {
        let _depth_guard = TypeDepthGuard::acquire()?;
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Bool) => Some(bool_sort()),
            TyKind::RigidTy(RigidTy::Int(k)) => Some(Sort::bitvec(int_ty_to_bitvec_width(k))),
            TyKind::RigidTy(RigidTy::Uint(k)) => Some(Sort::bitvec(uint_ty_to_bitvec_width(k))),
            TyKind::RigidTy(RigidTy::Float(k)) => Some(Sort::bitvec(float_ty_to_bitvec_width(k))),
            TyKind::RigidTy(RigidTy::RawPtr(inner, _) | RigidTy::Ref(_, inner, _)) => {
                match inner.kind() {
                    TyKind::RigidTy(RigidTy::Slice(elem)) => {
                        let elem_sort = Self::infer_sort_from_ty(elem)?;
                        Some(Self::slice_sort(elem_sort))
                    }
                    TyKind::RigidTy(RigidTy::Str) => Some(Self::slice_sort(bv8_sort())),
                    // Part of #1140: Trait object fat pointers (&dyn Trait, *dyn Trait)
                    TyKind::RigidTy(RigidTy::Dynamic(..)) => Some(Self::dyn_sort("Trait")),
                    _ => Some(ptr_sort()), // external enum: TyKind
                }
            }
            TyKind::RigidTy(RigidTy::Char) => Some(Sort::bitvec(32)),
            TyKind::RigidTy(RigidTy::Tuple(tys)) => Self::infer_tuple_sort(&tys),
            TyKind::RigidTy(RigidTy::Array(elem, len)) => {
                let elem_sort = Self::infer_sort_from_ty(elem)?;
                // SMT arrays have arbitrary index domains; Rust array length is tracked separately
                let _ = len;
                Some(Sort::array(ptr_sort(), elem_sort))
            }
            TyKind::RigidTy(RigidTy::Slice(elem)) => {
                let elem_sort = Self::infer_sort_from_ty(elem)?;
                Some(Self::slice_sort(elem_sort))
            }
            TyKind::RigidTy(RigidTy::Str) => Some(Self::slice_sort(bv8_sort())),
            // ADT handling is centralized in infer_adt_sort, including well-known types.
            TyKind::RigidTy(RigidTy::Adt(def, args)) => Self::infer_adt_sort(def, args),
            TyKind::RigidTy(RigidTy::Coroutine(def, args)) => tls::with(|tcx| {
                let coroutine_ty =
                    rustc_public::ty::Ty::from_rigid_kind(RigidTy::Coroutine(def, args.clone()));
                let info = build_coroutine_sort_info(tcx, coroutine_ty, |field_ty| {
                    Self::infer_sort_from_ty(field_ty).unwrap_or_else(ptr_sort)
                })?;
                Some(info.root_sort)
            }),
            // Part of #3159: Foreign types (extern type) like std::ptr::metadata::VTable.
            // Opaque unsized types that appear behind pointers; encode as pointer-width.
            TyKind::RigidTy(RigidTy::Foreign(_)) => Some(ptr_sort()),
            _ => None, // external enum: TyKind
        }
    }

    /// Construct a slice (fat pointer) sort with pointer, length, and backing-data fields.
    ///
    /// Slice values are represented as `(fld_ptr, fld_len, fld_data)` where:
    /// - `fld_ptr` is the data pointer for pointer casts/layout operations
    /// - `fld_len` is fat-pointer metadata used by `len()`/bounds checks
    /// - `fld_data` is `Array<usize, T>` used for element-level indexing semantics
    ///
    /// Part of #1607: Use `fld_` prefix for consistency with Vec naming convention.
    /// Part of #1632: Include `fld_data` in inferred slice sorts so intermediate
    /// slice-typed temporaries can preserve concrete element backing.
    #[must_use]
    pub(super) fn slice_sort(elem_sort: Sort) -> Sort {
        let name = names::slice_sort_name(&names::sort_short_name(&elem_sort));
        let data_sort = Sort::array(ptr_sort(), elem_sort);
        struct_sort(
            name,
            [("fld_ptr", ptr_sort()), ("fld_len", ptr_sort()), ("fld_data", data_sort)],
        )
    }

    /// Construct a trait object (dyn Trait) fat pointer sort with pointer and vtable fields.
    ///
    /// Part of #1140: Trait object fat pointers are represented as (fld_ptr, fld_vtable) pairs,
    /// where vtable is a pointer to the trait's virtual method table.
    /// Part of #1607: Use fld_ prefix for consistency with Vec/Slice naming convention.
    #[must_use]
    pub(super) fn dyn_sort(trait_name: &str) -> Sort {
        let name = names::dyn_sort_name(trait_name);
        struct_sort(name, [("fld_ptr", ptr_sort()), ("fld_vtable", ptr_sort())])
    }

    /// Resolve a potentially generic type using generic arguments.
    ///
    /// If the type is a generic parameter (e.g., T), looks up the concrete type
    /// in the provided generic args. Otherwise returns the type as-is.
    pub(super) fn resolve_generic_ty(
        ty: rustc_public::ty::Ty,
        args: &GenericArgs,
    ) -> Option<rustc_public::ty::Ty> {
        match ty.kind() {
            TyKind::Param(param_ty) => {
                let idx = param_ty.index as usize;
                if let Some(arg) = args.0.get(idx) {
                    match arg {
                        rustc_public::ty::GenericArgKind::Type(resolved_ty) => Some(*resolved_ty),
                        _ => None, // external enum: GenericArgKind
                    }
                } else {
                    None
                }
            }
            _ => Some(ty), // external enum: TyKind
        }
    }

    /// Infer AY sort for tuple types from Rust type information.
    ///
    /// Produces an SMT struct type with:
    /// - Name: `Tuple_<sort1>_<sort2>_...` using concise sort names (e.g., `Tuple_bv32_bool`)
    /// - Fields: `fld_0`, `fld_1`, ... with sorts inferred from Rust types
    ///
    /// Empty tuples produce a `Unit` struct type.
    #[must_use]
    pub(super) fn infer_tuple_sort(tys: &[rustc_public::ty::Ty]) -> Option<Sort> {
        if tys.is_empty() {
            return Some(struct_sort("Unit", Vec::<(&str, Sort)>::new()));
        }
        let mut fields = Vec::with_capacity(tys.len());
        for (i, ty) in tys.iter().enumerate() {
            let sort = Self::infer_sort_from_ty(*ty)?;
            fields.push((names::tuple_field_name(i), sort));
        }
        let name = Self::tuple_sort_name(&fields);
        Some(struct_sort(name, fields))
    }

    /// Infer sort for compound types (tuples with special patterns).
    #[must_use]
    pub(super) fn try_infer_sort_from_compound_ty(ty: rustc_public::ty::Ty) -> Option<Sort> {
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Tuple(tys)) if tys.len() == 2 => {
                // Special case: (T, bool) as packed bitvector for CheckedBinaryOp
                if let TyKind::RigidTy(RigidTy::Bool) = tys[1].kind()
                    && let Some(s) = Self::infer_sort_from_ty(tys[0])
                    && let SortInner::BitVec(bv) = s.inner()
                {
                    return Some(Sort::bitvec(bv.width + 1));
                }
                Self::infer_tuple_sort(&tys)
            }
            TyKind::RigidTy(RigidTy::Tuple(tys)) => Self::infer_tuple_sort(&tys),
            _ => None, // external enum: TyKind
        }
    }

    /// Generate a concise tuple sort name from field sorts.
    /// Accepts any field name type (the name component is ignored; only sorts matter).
    pub(super) fn tuple_sort_name<N>(fields: &[(N, Sort)]) -> String {
        let mut name = String::from("Tuple");
        for (_, s) in fields {
            name.push('_');
            name.push_str(&names::sort_short_name(s));
        }
        name
    }

    /// Build a unique SMT sort name for a generic ADT.
    ///
    /// This prevents collisions between different instantiations like `Option<u32>` and `Option<u64>`.
    pub(super) fn adt_sort_name(def: AdtDef, args: &GenericArgs) -> String {
        names::adt_sort_name(def, args)
    }

    /// Part of #1906: Determine the mathematical "view" sort for a Rust type.
    /// Returns (Sort, is_signed) if viewable, None otherwise.
    pub(super) fn view_sort_from_ty(ty: rustc_public::ty::Ty) -> Option<(Sort, bool)> {
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Int(_)) => Some((int_sort(), true)),
            TyKind::RigidTy(RigidTy::Uint(_)) => Some((int_sort(), false)),
            TyKind::RigidTy(RigidTy::Char) => Some((int_sort(), false)),
            TyKind::RigidTy(RigidTy::Bool) => Some((bool_sort(), false)),
            TyKind::RigidTy(RigidTy::Adt(def, _))
                if def.trimmed_name() == "BigInt" || def.trimmed_name() == "BigUint" =>
            {
                Some((int_sort(), false))
            }
            _ => None, // external enum: TyKind
        }
    }
}
