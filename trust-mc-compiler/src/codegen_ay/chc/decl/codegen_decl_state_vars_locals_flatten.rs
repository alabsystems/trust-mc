// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Type-specific local flattening helpers for CHC state variable collection.
//!
//! Extracted from `codegen_decl_state_vars_locals.rs` for 500-LOC compliance.
//! Part of #4119.
//!
//! Contains flatten dispatch helpers for Range, RangeInclusive, IndexRange,
//! Option (scalar, tuple, struct), and Result locals.

use ay_bindings::Sort;
use rustc_abi::VariantIdx as InternalVariantIdx;
use rustc_public::rustc_internal;
use rustc_public::ty::{GenericArgKind, RigidTy, TyKind};
use tracing::{debug, warn};

use crate::codegen_ay::types::ptr_sort;

use super::ChcCtx;
use super::codegen_decl_flatten::collect_leaf_sorts;
use super::codegen_types::CodegenTypes;
use crate::codegen_ay::chc::codegen_ctx::clusters::EnumBvLayout;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Flatten a Range<T> local into two scalar state variables (start, end).
    pub(super) fn collect_range_local(
        &mut self,
        local_idx: usize,
        in_name: &str,
        args: &rustc_public::ty::GenericArgs,
        ty: rustc_public::ty::Ty,
    ) {
        let Some(elem_sort) = args.0.first().and_then(|arg| match arg {
            GenericArgKind::Type(ty) => Self::translate_ty(*ty),
            _ => None,
        }) else {
            warn!(local_idx, ty = ?ty, "CHC: Range guard passed but translate_ty returned None");
            return;
        };
        let (fld_sort, orig_bv_width) = self.lift_bv_sort_recording_width(elem_sort);
        let vec_idx = self.state_var_mgr.state_vars.len();
        self.flatten_local_2field(local_idx, in_name, fld_sort.clone(), fld_sort, None);
        if let Some(width) = orig_bv_width {
            let is_signed = args
                .0
                .first()
                .and_then(|arg| match arg {
                    GenericArgKind::Type(ty) => trust_mc_codegen_shared::ty_signedness_shallow(*ty),
                    _ => None,
                })
                .unwrap_or(false);
            self.int_lifted_vars.insert(vec_idx, (width, is_signed));
            self.int_lifted_vars.insert(vec_idx + 1, (width, is_signed));
        }
        debug!(local_idx, ty = ?ty, "CHC: flattened Range<T> (start, end)");
    }

    /// Flatten a RangeInclusive<T> local into three scalar state variables
    /// (start, end, exhausted).
    pub(super) fn collect_range_inclusive_local(
        &mut self,
        local_idx: usize,
        in_name: &str,
        args: &rustc_public::ty::GenericArgs,
        ty: rustc_public::ty::Ty,
    ) {
        let Some(elem_sort) = args.0.first().and_then(|arg| match arg {
            GenericArgKind::Type(ty) => Self::translate_ty(*ty),
            _ => None,
        }) else {
            warn!(
                local_idx,
                ty = ?ty,
                "CHC: RangeInclusive guard passed but translate_ty returned None"
            );
            return;
        };
        let (fld_sort, orig_bv_width) = self.lift_bv_sort_recording_width(elem_sort);
        let vec_idx = self.state_var_mgr.state_vars.len();
        self.flatten_local_nfield(
            local_idx,
            in_name,
            &[fld_sort.clone(), fld_sort, Sort::bool()],
            None,
        );
        if let Some(width) = orig_bv_width {
            let is_signed = args
                .0
                .first()
                .and_then(|arg| match arg {
                    GenericArgKind::Type(ty) => trust_mc_codegen_shared::ty_signedness_shallow(*ty),
                    _ => None,
                })
                .unwrap_or(false);
            self.int_lifted_vars.insert(vec_idx, (width, is_signed));
            self.int_lifted_vars.insert(vec_idx + 1, (width, is_signed));
        }
        debug!(
            local_idx,
            ty = ?ty,
            "CHC: flattened RangeInclusive<T> (start, end, exhausted)"
        );
    }

    /// Flatten an IndexRange local into two bv64 state variables (start, end).
    pub(super) fn collect_index_range_local(
        &mut self,
        local_idx: usize,
        in_name: &str,
        ty: rustc_public::ty::Ty,
    ) {
        let index_sort = ptr_sort();
        let (fld_sort, orig_bv_width) = self.lift_bv_sort_recording_width(index_sort);
        let vec_idx = self.state_var_mgr.state_vars.len();
        self.flatten_local_2field(local_idx, in_name, fld_sort.clone(), fld_sort, None);
        if let Some(width) = orig_bv_width {
            self.int_lifted_vars.insert(vec_idx, (width, false));
            self.int_lifted_vars.insert(vec_idx + 1, (width, false));
        }
        debug!(local_idx, ty = ?ty, "CHC: flattened IndexRange (start, end)");
    }

    /// Flatten an Option<T> local into (is_some: Bool, value: T).
    pub(super) fn collect_option_local(
        &mut self,
        local_idx: usize,
        in_name: &str,
        args: &rustc_public::ty::GenericArgs,
        ty: rustc_public::ty::Ty,
    ) {
        let Some(payload_sort) = args.0.first().and_then(|arg| match arg {
            GenericArgKind::Type(ty) => {
                // Keep flattened Option locals aligned with the datatype and
                // const-ref paths: Option<&T> / Option<*T> are modeled
                // value-semantically as Option<T>, not Option<ptr>.
                // Sized-only: &str / &[T] payloads stay BV128 fat pointers.
                let (payload_ty, _) = Self::deref_ref_ty_sized_only(*ty);
                Self::translate_ty(payload_ty)
            }
            _ => None,
        }) else {
            warn!(local_idx, ty = ?ty, "CHC: Option guard passed but translate_ty returned None");
            return;
        };
        let payload_sort = self.lift_bv_to_int_if_enabled(payload_sort);
        self.flatten_local_2field(local_idx, in_name, Sort::bool(), payload_sort, Some((1, 0)));

        // Part of #3984: Register EnumBvLayout for build_enum_bv_destination_values.
        let layout = EnumBvLayout {
            num_constructors: 2,
            tag_bits: 1,
            ctor_field_slot: vec![vec![], vec![0]],
            max_payload_slots: 1,
            discriminants: vec![0, 1],
        };
        self.flatten.enum_bv_layouts.insert(local_idx, layout);

        debug!(local_idx, ty = ?ty, "CHC: flattened Option<T> (is_some, value)");
    }

    /// Flatten an Option<(T1, T2, ...)> local into (is_some, fld1, fld2, ...).
    pub(super) fn collect_option_tuple_local(
        &mut self,
        local_idx: usize,
        in_name: &str,
        args: &rustc_public::ty::GenericArgs,
        ty: rustc_public::ty::Ty,
    ) {
        let Some(GenericArgKind::Type(inner_ty)) = args.0.first() else {
            return;
        };
        let (payload_ty, _) = Self::deref_ref_ty_sized_only(*inner_ty);
        let TyKind::RigidTy(RigidTy::Tuple(tys)) = payload_ty.kind() else {
            return;
        };
        let Some(field_sorts): Option<Vec<Sort>> =
            tys.iter().map(|ty| Self::translate_ty(*ty)).collect()
        else {
            warn!(local_idx, ty = ?ty,
                "CHC: Option<tuple> guard passed but translate_ty returned None for a field");
            return;
        };
        let max_payload_slots = field_sorts.len();
        let mut all_sorts = vec![Sort::bool()];
        all_sorts.extend(field_sorts.into_iter().map(|s| self.lift_bv_to_int_if_enabled(s)));
        self.flatten_local_nfield(local_idx, in_name, &all_sorts, Some((1, 0)));

        // Part of #3984: Register EnumBvLayout for build_enum_bv_destination_values.
        let layout = EnumBvLayout {
            num_constructors: 2,
            tag_bits: 1,
            ctor_field_slot: vec![vec![], vec![0]],
            max_payload_slots,
            discriminants: vec![0, 1],
        };
        self.flatten.enum_bv_layouts.insert(local_idx, layout);

        debug!(local_idx, ty = ?ty, num_fields = all_sorts.len(),
            "CHC: flattened Option<scalar-tuple> to {} state vars (#3057)",
            all_sorts.len());
    }

    /// Flatten an Option<T> local where T is a recursively flattenable struct.
    ///
    /// E.g., `Option<MyType { val: u8 }>` -> `[Bool, BitVec8]` (is_some + leaf sorts).
    /// This is the same layout as `Option<u8>` when the struct has a single scalar field,
    /// and extends to multi-field structs: `Option<Point { x: i32, y: i32 }>` -> `[Bool, BV32, BV32]`.
    ///
    /// Part of #3207: enables PDR to prove harnesses with custom Arbitrary impls
    /// by eliminating ADT accessor functions from CHC rules.
    pub(super) fn collect_option_struct_local(
        &mut self,
        local_idx: usize,
        in_name: &str,
        args: &rustc_public::ty::GenericArgs,
        ty: rustc_public::ty::Ty,
    ) {
        let Some(payload_sort) = args.0.first().and_then(|arg| match arg {
            GenericArgKind::Type(ty) => {
                let (payload_ty, _) = Self::deref_ref_ty_sized_only(*ty);
                Self::translate_ty(payload_ty)
            }
            _ => None,
        }) else {
            warn!(local_idx, ty = ?ty,
                "CHC: Option<struct> guard passed but translate_ty returned None");
            return;
        };
        let leaf_sorts = collect_leaf_sorts(&payload_sort, 0);
        let max_payload_slots = leaf_sorts.len();
        let mut all_sorts = vec![Sort::bool()];
        all_sorts.extend(leaf_sorts.into_iter().map(|s| self.lift_bv_to_int_if_enabled(s)));
        self.flatten_local_nfield(local_idx, in_name, &all_sorts, Some((1, 0)));

        // Part of #3984: Register EnumBvLayout so build_enum_bv_destination_values
        // can decompose Option<struct> call results into scalar tag + payload.
        // Without this, the flatten constrain pipeline falls through to
        // collect_leaf_exprs which can't handle multi-constructor DTs.
        let discriminants = match ty.kind() {
            TyKind::RigidTy(RigidTy::Adt(def, _)) => {
                let idef = rustc_internal::internal(self.tcx, def);
                (0..2)
                    .map(|i| {
                        idef.discriminant_for_variant(self.tcx, InternalVariantIdx::from_usize(i))
                            .val as u64
                    })
                    .collect()
            }
            _ => vec![0, 1],
        };
        let layout = EnumBvLayout {
            num_constructors: 2,
            tag_bits: 1,
            ctor_field_slot: vec![vec![], vec![0]],
            max_payload_slots,
            discriminants,
        };
        self.flatten.enum_bv_layouts.insert(local_idx, layout);

        debug!(local_idx, ty = ?ty, num_fields = all_sorts.len(),
            max_payload_slots,
            "CHC: flattened Option<struct> to {} state vars (#3207/#3984)",
            all_sorts.len());
    }

    /// Flatten a Result<T, E> local into scalar state vars.
    pub(super) fn collect_result_local(
        &mut self,
        local_idx: usize,
        in_name: &str,
        args: &rustc_public::ty::GenericArgs,
        ty: rustc_public::ty::Ty,
    ) {
        let (Some(ok_sort), Some(err_sort)) = (
            match &args.0[0] {
                GenericArgKind::Type(ty) => Self::translate_ty(*ty),
                _ => None,
            },
            match &args.0[1] {
                GenericArgKind::Type(ty) => Self::translate_ty(*ty),
                _ => None,
            },
        ) else {
            warn!(local_idx, ty = ?ty, "CHC: Result guard passed but translate_ty returned None");
            return;
        };
        let ok_sort = self.lift_bv_to_int_if_enabled(ok_sort);
        let err_sort = self.lift_bv_to_int_if_enabled(err_sort);
        if ok_sort == err_sort {
            self.flatten_local_2field(local_idx, in_name, Sort::bool(), ok_sort, Some((0, 1)));
            debug!(local_idx, ty = ?ty, "CHC: flattened Result<T,E> same-sort (is_ok, payload)");
        } else {
            self.flatten_local_nfield(
                local_idx,
                in_name,
                &[Sort::bool(), ok_sort, err_sort],
                Some((0, 1)),
            );
            debug!(local_idx, ty = ?ty, "CHC: flattened Result<T,E> hetero (is_ok, ok_val, err_val)");
        }
    }
}
