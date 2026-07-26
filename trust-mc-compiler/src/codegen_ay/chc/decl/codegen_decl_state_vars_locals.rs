// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Section 1: Scalar local state variable collection from MIR locals.
//!
//! Extracted from `codegen_decl_state_vars.rs` for 500-LOC compliance (Part of #3199, D1).
//! Handles the TyKind match dispatch that translates each MIR local to AY sorts:
//! BigInt/BigRational references, tuple flattening, Range/IndexRange, Option, Result,
//! and general struct flattening.

use ay_bindings::Sort;
use rustc_abi::VariantIdx as InternalVariantIdx;
use rustc_public::CrateDef;
use rustc_public::rustc_internal;
use rustc_public::ty::{GenericArgKind, RigidTy, TyKind};
use tracing::{debug, warn};

use super::ChcCtx;
use super::codegen_decl_flatten::{
    collect_leaf_sorts, enum_tag_bits, is_multi_ctor_flattenable, is_recursively_flattenable,
    unify_multi_ctor_leaf_sorts,
};
use super::codegen_decl_state_vars_enum_layout::try_flatten_unit_aware_multi_ctor_enum;
use super::codegen_types::CodegenTypes;
use crate::codegen_ay::chc::codegen_ctx::clusters::EnumBvLayout;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Section 1: Collect scalar locals by translating MIR local types to AY sorts.
    ///
    /// Each MIR local is either flattened (tuple, Range, Option, Result, struct) into
    /// multiple scalar state variables, or mapped to a single sort. Flattened locals
    /// `continue` past the trailing int-lift + push logic.
    pub(in crate::codegen_ay::chc) fn collect_state_vars_scalar_locals(&mut self) {
        for (local_idx, local_decl) in self.body.local_decls() {
            let vec_idx = self.state_var_mgr.state_vars.len();
            self.state_var_mgr.local_to_state_idx.insert(local_idx, vec_idx);
            let (in_name, out_name) =
                crate::codegen_ay::names::state_var_name_pair(&self.fn_name, local_idx);
            // Resolve through the shared body-local normalization helper which
            // handles coroutine-aware call-destination fallback (body_resolve.rs).
            let local_ty = self
                .resolve_inline_local_ty(self.body, local_idx)
                .unwrap_or_else(|| self.resolve_body_ty(local_decl.ty));
            let sort = match local_ty.kind() {
                // BigInt references are modeled with value semantics in CHC.
                TyKind::RigidTy(RigidTy::Ref(_, inner, _))
                    if Self::type_name_contains_bigint(&inner) =>
                {
                    debug!(
                        local_idx,
                        ty = ?local_ty,
                        "CHC: BigInt reference local uses Int sort"
                    );
                    Sort::int()
                }
                // BigRational references are modeled with value semantics in CHC.
                TyKind::RigidTy(RigidTy::Ref(_, inner, _))
                    if Self::type_name_contains_bigrational(&inner) =>
                {
                    debug!(
                        local_idx,
                        ty = ?local_ty,
                        "CHC: BigRational reference local uses Real sort"
                    );
                    Sort::real()
                }
                // Part of #2214: Flatten scalar tuples with arity >= 2.
                TyKind::RigidTy(RigidTy::Tuple(tys))
                    if tys.len() >= 2
                        && tys.iter().all(|ty| {
                            Self::translate_ty(*ty)
                                .is_some_and(|s| s.is_bitvec() || s.is_bool() || s.is_int())
                        }) =>
                {
                    let Some(field_sorts) = tys
                        .iter()
                        .map(|ty| Self::translate_ty(*ty))
                        .collect::<Option<Vec<Sort>>>()
                    else {
                        warn!(
                            local_idx,
                            ty = ?local_ty,
                            "CHC: tuple guard passed but translate_ty returned None for a field"
                        );
                        continue;
                    };
                    let field_sorts: Vec<Sort> = field_sorts
                        .into_iter()
                        .map(|s| self.lift_bv_to_int_if_enabled(s))
                        .collect();
                    let num_fields = field_sorts.len();
                    self.flatten_local_nfield(local_idx, &in_name, &field_sorts, None);
                    debug!(
                        local_idx,
                        ty = ?local_ty,
                        num_fields,
                        "CHC: flattened scalar tuple to {n} state vars",
                        n = num_fields
                    );
                    continue;
                }
                // Part of #2214: Flatten Range<T> structs into two scalar state variables.
                TyKind::RigidTy(RigidTy::Adt(def, args))
                    if def.trimmed_name() == "Range"
                        && args.0.first().is_some_and(|arg| matches!(
                            arg,
                            GenericArgKind::Type(ty) if Self::translate_ty(*ty).is_some_and(|s| s.is_bitvec())
                        )) =>
                {
                    self.collect_range_local(local_idx, &in_name, &args, local_ty);
                    continue;
                }
                // RangeInclusive<T> has the same scalar bounds plus an `exhausted`
                // flag in its local representation. Flatten all three fields so
                // constructor and contains stubs stay on scalar state vars.
                TyKind::RigidTy(RigidTy::Adt(def, args))
                    if def.trimmed_name() == "RangeInclusive"
                        && args.0.first().is_some_and(|arg| matches!(
                            arg,
                            GenericArgKind::Type(ty) if Self::translate_ty(*ty).is_some_and(|s| s.is_bitvec())
                        )) =>
                {
                    self.collect_range_inclusive_local(local_idx, &in_name, &args, local_ty);
                    continue;
                }
                // Part of #2214: Flatten IndexRange into two bv64 state variables.
                TyKind::RigidTy(RigidTy::Adt(def, _))
                    if def.trimmed_name() == "IndexRange" =>
                {
                    self.collect_index_range_local(local_idx, &in_name, local_ty);
                    continue;
                }
                // Part of #2214: Flatten Option<T> enum into (is_some: Bool, value: T).
                TyKind::RigidTy(RigidTy::Adt(def, args))
                    if def.trimmed_name() == "Option"
                        && args.0.first().is_some_and(|arg| matches!(
                            arg,
                            GenericArgKind::Type(ty) if {
                                // Sized-only: matches collect_option_local (#gate).
                                let (payload_ty, _) = Self::deref_ref_ty_sized_only(*ty);
                                Self::translate_ty(payload_ty).is_some_and(|s|
                                    s.is_bitvec() || s.is_bool() || s.is_int())
                            }
                        )) =>
                {
                    self.collect_option_local(local_idx, &in_name, &args, local_ty);
                    continue;
                }
                // Part of #3057: Flatten Option<(T1, T2, ...)> where Ti are scalar.
                TyKind::RigidTy(RigidTy::Adt(def, args))
                    if def.trimmed_name() == "Option"
                        && args.0.first().is_some_and(|arg| matches!(
                            arg,
                            GenericArgKind::Type(ty) if {
                                let (payload_ty, _) = Self::deref_ref_ty_sized_only(*ty);
                                matches!(
                                    payload_ty.kind(),
                                    TyKind::RigidTy(RigidTy::Tuple(tys))
                                    if tys.len() >= 2 && tys.iter().all(|t|
                                        Self::translate_ty(*t).is_some_and(|s|
                                            s.is_bitvec() || s.is_bool() || s.is_int()))
                                )
                            }
                        )) =>
                {
                    self.collect_option_tuple_local(local_idx, &in_name, &args, local_ty);
                    continue;
                }
                // Part of #3207: Flatten Option<T> where T is a recursively flattenable
                // struct. E.g., Option<MyType { val: u8 }> → [Bool, BitVec8].
                // Eliminates Z3 ADT accessors from CHC rules, enabling PDR proofs
                // for harnesses with custom Arbitrary impls.
                TyKind::RigidTy(RigidTy::Adt(def, args))
                    if def.trimmed_name() == "Option"
                        && args.0.first().is_some_and(|arg| matches!(
                            arg,
                            GenericArgKind::Type(ty) if {
                                // Sized-only: matches collect_option_struct_local.
                                let (payload_ty, _) = Self::deref_ref_ty_sized_only(*ty);
                                Self::translate_ty(payload_ty).is_some_and(|s|
                                    !s.is_bitvec() && !s.is_bool() && !s.is_int()
                                    && is_recursively_flattenable(&s, 0))
                            }
                        )) =>
                {
                    self.collect_option_struct_local(local_idx, &in_name, &args, local_ty);
                    continue;
                }
                // Part of #2214: Flatten Result<T, E> enum into scalar state vars.
                TyKind::RigidTy(RigidTy::Adt(def, args))
                    if def.trimmed_name() == "Result"
                        && args.0.len() >= 2
                        && {
                            let ok_sort = match &args.0[0] {
                                GenericArgKind::Type(ty) => Self::translate_ty(*ty),
                                _ => None,
                            };
                            let err_sort = match &args.0[1] {
                                GenericArgKind::Type(ty) => Self::translate_ty(*ty),
                                _ => None,
                            };
                            let is_scalar = |s: &Sort| s.is_bitvec() || s.is_bool() || s.is_int();
                            ok_sort.as_ref().is_some_and(is_scalar)
                                && err_sort.as_ref().is_some_and(is_scalar)
                        } =>
                {
                    self.collect_result_local(local_idx, &in_name, &args, local_ty);
                    continue;
                }
                _ => {
                    let sort = if let Some(s) = Self::translate_ty(local_ty) { s } else {
                        warn!(?local_idx, ty = ?local_ty, "CHC UNSOUND fallback: unknown type, defaulting to bv32");
                        self.record_fallback();
                        Sort::bitvec(32)
                    };
                    if let Some(dt) = sort.datatype_sort()
                        && dt.constructors.len() == 1
                    {
                        let fields = &dt.constructors[0].fields;
                        let recursively_flat = !fields.is_empty()
                            && fields
                                .iter()
                                .all(|f| is_recursively_flattenable(&f.sort, 0));
                        // Part of #3387: extract MIR ADT name for allow-list
                        // classification, eliminating the fragile deny-list.
                        let adt_name = match local_ty.kind() {
                            TyKind::RigidTy(RigidTy::Adt(def, _)) => {
                                Some(def.trimmed_name().clone())
                            }
                            _ => None,
                        };
                        let projection_kind = Self::classify_collection_projection(
                            &dt.name,
                            adt_name.as_deref(),
                        )
                        .or_else(|| Self::classify_wrapper_projection(&sort));
                        if recursively_flat {
                            let leaf_sorts = collect_leaf_sorts(&sort, 0);
                            let num_leaves = leaf_sorts.len();
                            self.flatten_local_nfield(local_idx, &in_name, &leaf_sorts, None);
                            if let Some(kind) = projection_kind {
                                self.collections.projection_locals.insert(local_idx, kind);
                                debug!(
                                    local_idx,
                                    ty = ?local_ty,
                                    num_fields = num_leaves,
                                    dt_name = %dt.name,
                                    ?kind,
                                    "CHC: flattened collection/iterator to {n} leaf state vars (#2989)",
                                    n = num_leaves
                                );
                            } else {
                                debug!(
                                    local_idx,
                                    ty = ?local_ty,
                                    num_fields = num_leaves,
                                    dt_name = %dt.name,
                                    "CHC: recursively flattened struct to {n} leaf state vars (#2989)",
                                    n = num_leaves
                                );
                            }
                            continue;
                        }
                    }
                    // Part of #3215: BV-flatten multi-constructor enums.
                    // Eliminates ADT accessor functions from CHC rules,
                    // enabling Z3 PDR to prove enum pattern-match harnesses.
                    if try_flatten_unit_aware_multi_ctor_enum(
                        self,
                        local_idx,
                        &in_name,
                        local_ty,
                    ) {
                        continue;
                    }
                    if let Some(dt) = sort.datatype_sort()
                        && dt.constructors.len() >= 2
                        && is_multi_ctor_flattenable(dt)
                    {
                        if let Some((ctor_field_slots, _ctor_leaf_counts, unified_sorts)) =
                            unify_multi_ctor_leaf_sorts(dt)
                        {
                            let n = dt.constructors.len();
                            let tag_bits = enum_tag_bits(n);
                            let tag_sort = if n == 2 {
                                Sort::bool()
                            } else {
                                Sort::bitvec(tag_bits)
                            };
                            let max_payload = unified_sorts.len();
                            // Prepend tag sort, then payload sorts
                            let mut all_sorts = Vec::with_capacity(1 + max_payload);
                            all_sorts.push(tag_sort);
                            all_sorts.extend(
                                unified_sorts
                                    .into_iter()
                                    .map(|s| self.lift_bv_to_int_if_enabled(s)),
                            );
                            self.flatten_local_nfield(
                                local_idx,
                                &in_name,
                                &all_sorts,
                                None,
                            );
                            // Part of #3242: use real discriminant values from the ADT
                            // definition instead of sequential [0, 1, ..., N-1].
                            // Explicit-discriminant enums (e.g., #[repr(u32)] with = 100)
                            // would get wrong tag-to-discriminant mappings otherwise.
                            let discriminants: Vec<u64> = match local_ty.kind() {
                                TyKind::RigidTy(RigidTy::Adt(def, _)) => {
                                    let idef = rustc_internal::internal(self.tcx, def);
                                    (0..n)
                                        .map(|i| {
                                            idef.discriminant_for_variant(
                                                self.tcx,
                                                InternalVariantIdx::from_usize(i),
                                            )
                                            .val as u64
                                        })
                                        .collect()
                                }
                                _ => (0..n as u64).collect(),
                            };
                            let layout = EnumBvLayout {
                                num_constructors: n,
                                tag_bits,
                                ctor_field_slot: ctor_field_slots,
                                max_payload_slots: max_payload,
                                discriminants,
                            };
                            self.flatten.enum_bv_layouts.insert(local_idx, layout);
                            debug!(
                                local_idx,
                                ty = ?local_ty,
                                num_constructors = n,
                                tag_bits,
                                max_payload,
                                total_state_vars = 1 + max_payload,
                                "CHC: BV-flattened multi-ctor enum (#3215)"
                            );
                            continue;
                        }
                    }
                    sort
                }
            };
            let (sort, orig_bv_width) = self.lift_bv_sort_recording_width(sort);
            let vec_idx = self.state_var_mgr.state_vars.len();
            self.push_state_var_pair(&in_name, &out_name, sort);
            if let Some(width) = orig_bv_width {
                let is_signed =
                    trust_mc_codegen_shared::ty_signedness_shallow(local_ty).unwrap_or(false);
                self.int_lifted_vars.insert(vec_idx, (width, is_signed));
            }
        }
    }

    // Type-specific flatten helpers extracted to codegen_decl_state_vars_locals_flatten.rs
    // per #4119: collect_range_local, collect_range_inclusive_local,
    // collect_index_range_local, collect_option_local, collect_option_tuple_local,
    // collect_option_struct_local, collect_result_local.
}
