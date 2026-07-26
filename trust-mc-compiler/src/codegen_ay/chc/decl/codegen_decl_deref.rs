// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Deref type array pre-declaration for CHC state variables.
//!
//! Extracted from codegen_decl.rs per #2246 decomposition.
//! Migrated from include!() to proper module.
//! Part of #2306: include!() to proper module migration.

use std::collections::BTreeMap;
use std::sync::Arc;

use ay_bindings::Sort;
use rustc_public::mir::{Operand, Place, ProjectionElem, Rvalue, StatementKind, TerminatorKind};
use rustc_public::ty::{RigidTy, TyKind};
use tracing::debug;

use crate::codegen_ay::types::ptr_sort;

use super::ChcCtx;
use super::codegen_decl_panic_filter::{
    compute_locals_in_relevant_blocks, compute_semantically_relevant_blocks,
};

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Pre-declares type-indexed memory arrays for deref targets.
    ///
    /// Scans MIR for places with Deref projections and declares type-indexed
    /// arrays as state variables. This ensures arrays are declared BEFORE rules
    /// are generated, avoiding undeclared variable errors in CHC output.
    ///
    /// Part of #892 audit: Fix undeclared type-indexed array variables.
    /// Part of #2244/#2280/#2323: Uses `elem_sort_for_memory_array` for
    /// size-based Datatype flattening (avoiding ay#1766 DT+BV regression).
    pub(in crate::codegen_ay::chc) fn collect_deref_type_arrays(&mut self) {
        // Collect (type_key, Ty) pairs from deref projections.
        // BTreeMap ensures deterministic ordering and dedup by type_key.
        let mut deref_types: BTreeMap<String, rustc_public::ty::Ty> = BTreeMap::new();

        // Part of #3436: Ignore blocks whose effects are irrelevant to the proof.
        // Part of #3886: panic-unwind cleanup blocks remain relevant even when
        // they cannot reach `Return`, because their `Drop`/assert effects must be
        // predeclared before rule generation.
        let relevant_blocks = compute_semantically_relevant_blocks(self.body);
        let irrelevant_count = relevant_blocks.iter().filter(|&&keep| !keep).count();
        if irrelevant_count > 0 {
            debug!(
                fn_name = %self.fn_name,
                total_blocks = self.body.blocks.len(),
                irrelevant_count,
                "CHC: skipping {} irrelevant blocks in deref type array collection (#3436, #3886)",
                irrelevant_count
            );
        }

        for (bb_idx, bb_data) in self.body.blocks.iter().enumerate() {
            // Part of #3436/#3886: skip only blocks with no proof-relevant effect.
            if !relevant_blocks[bb_idx] {
                continue;
            }
            // Check statements for places with deref projections
            for stmt in &bb_data.statements {
                if let StatementKind::Assign(lhs, rhs) = &stmt.kind {
                    // Check lhs place
                    self.collect_deref_types_from_place(lhs, &mut deref_types);
                    // Check rhs places
                    self.collect_deref_types_from_rvalue(rhs, &mut deref_types);
                }
            }

            // Check terminator for deref in call arguments
            if let TerminatorKind::Call { args, .. } = &bb_data.terminator.kind {
                for arg in args {
                    if let Operand::Copy(place) | Operand::Move(place) = arg {
                        self.collect_deref_types_from_place(place, &mut deref_types);
                    }
                }
            }
        }

        // Declare state variables for each collected type
        for (type_key, pointee_ty) in deref_types {
            // Skip if already in type_arrays (shouldn't happen but defensive)
            if self.heap_state.type_arrays.contains_key(type_key.as_str()) {
                continue;
            }
            // Part of #4066: skip uninit-check shadow memory types.
            if super::codegen_decl_static::is_uninit_shadow_type_key(&type_key) {
                debug!(
                    type_key = %type_key,
                    "CHC: skipping uninit shadow type in deref array collection (#4066)"
                );
                continue;
            }

            // Part of #2267: mem_array_name_pair generates both names from one buffer.
            let (arr_name, arr_out_name) =
                crate::codegen_ay::names::mem_array_name_pair(&self.fn_name, &type_key);

            // Part of #2244/#2280/#2323: Use elem_sort_for_memory_array for
            // size-based Datatype flattening instead of opaque fallback.
            let elem_sort = self.elem_sort_for_memory_array(pointee_ty);
            let arr_sort = Sort::array(ptr_sort(), elem_sort.clone());

            debug!(
                type_key = %type_key,
                arr_name = %arr_name,
                "CHC: pre-declared type-indexed array for deref"
            );

            self.heap_state
                .type_arrays
                .insert(type_key.into(), (Arc::clone(&arr_name), elem_sort.clone()));
            // Part of #2793: keep reverse index in sync with type_arrays.
            self.heap_state.array_name_to_elem_sort.insert(Arc::clone(&arr_name), elem_sort);
            self.push_state_var_pair_arc(arr_name, &arr_out_name, arr_sort);
        }
    }

    /// Pre-declares type-indexed memory arrays for local variable assignments.
    ///
    /// Covers Vector 1 of the late-creation bug (#2258): plain local assignments
    /// at Mem level call `build_memory_store(addr, value, local_ty)` which may
    /// create type arrays via `get_or_create_type_array`. Pre-declaring them
    /// ensures they appear in relation signatures and `declare-var` statements.
    ///
    /// Also covers Vectors 2-3 partially: pointer write targets and deref chain
    /// intermediate types are often visible as local types or pointee types.
    ///
    /// Part of #2244/#2280/#2323: Uses `elem_sort_for_memory_array` for
    /// size-based Datatype flattening (avoiding ay#1766 DT+BV regression).
    pub(in crate::codegen_ay::chc) fn collect_local_type_arrays(&mut self) {
        // Collect (type_key, elem_sort) pairs using translate_ty for sort accuracy.
        // BTreeMap ensures deterministic ordering by type_key.
        let mut local_types: BTreeMap<String, Sort> = BTreeMap::new();

        // Part of #3436: Skip locals whose values never affect the proof.
        // Part of #3886: locals used only on panic-unwind cleanup paths remain
        // relevant because retained cleanup blocks may read/write their typed
        // memory arrays during drop translation.
        let live_locals = compute_locals_in_relevant_blocks(self.body);
        let total_locals = self.body.locals().len();
        let skipped_locals = total_locals - live_locals.len();
        if skipped_locals > 0 {
            debug!(
                fn_name = %self.fn_name,
                total_locals,
                live_locals = live_locals.len(),
                skipped_locals,
                "CHC: skipping {} irrelevant locals in type array collection (#3436, #3886)",
                skipped_locals
            );
        }

        for (local_idx, local_decl) in self.body.locals().iter().enumerate() {
            // Part of #3436: skip locals only used in error-only blocks.
            if !live_locals.contains(&local_idx) {
                continue;
            }

            // Part of #3661: resolve body-local generic params before computing
            // type keys. Without this, Param(0) gets key "param_0" at declaration
            // time but "u32" (resolved) at runtime access — different arrays.
            let type_key = self.type_key_for_body_ty(local_decl.ty);

            // Part of #2244/#2280/#2323: Use elem_sort_for_memory_array for
            // size-based Datatype flattening instead of opaque fallback.
            let elem_sort = self.elem_sort_for_memory_array(local_decl.ty);

            local_types.entry(type_key.into_owned()).or_insert(elem_sort);

            // Also extract pointee types from reference/pointer locals (#2258 Vectors 2-3)
            if let TyKind::RigidTy(RigidTy::Ref(_, inner, _))
            | TyKind::RigidTy(RigidTy::RawPtr(inner, _)) = local_decl.ty.kind()
            {
                // Part of #3661: resolve pointee type for consistent type keys.
                let pointee_key = self.type_key_for_body_ty(inner);
                // Part of #2280/#2323: same Datatype→bitvec flattening
                let pointee_sort = self.elem_sort_for_memory_array(inner);
                local_types.entry(pointee_key.into_owned()).or_insert(pointee_sort);
            }
        }

        for (type_key, elem_sort) in local_types {
            // Skip if already pre-declared by collect_deref_type_arrays
            if self.heap_state.type_arrays.contains_key(type_key.as_str()) {
                continue;
            }
            // Part of #4066: skip uninit-check shadow memory types.
            if super::codegen_decl_static::is_uninit_shadow_type_key(&type_key) {
                debug!(
                    type_key = %type_key,
                    "CHC: skipping uninit shadow type in local array collection (#4066)"
                );
                continue;
            }

            // Part of #2267: mem_array_name_pair generates both names from one buffer.
            let (arr_name, arr_out_name) =
                crate::codegen_ay::names::mem_array_name_pair(&self.fn_name, &type_key);

            let arr_sort = Sort::array(ptr_sort(), elem_sort.clone());

            debug!(
                type_key = %type_key,
                arr_name = %arr_name,
                "CHC: pre-declared type-indexed array for local assignment (#2258)"
            );

            self.heap_state
                .type_arrays
                .insert(type_key.into(), (Arc::clone(&arr_name), elem_sort.clone()));
            // Part of #2793: keep reverse index in sync with type_arrays.
            self.heap_state.array_name_to_elem_sort.insert(Arc::clone(&arr_name), elem_sort);
            self.push_state_var_pair_arc(arr_name, &arr_out_name, arr_sort);
        }
    }

    /// Pre-declare pointer-wrapper alias arrays for type-indexed memory.
    ///
    /// Part of #2967: For each `ptr_T` type array already declared by
    /// `collect_deref_type_arrays()` or `collect_local_type_arrays()`,
    /// also pre-declare `std_ptr_NonNull_T` and `std_ptr_Unique_T` arrays.
    /// Without this, `mirror_pointer_wrapper_store_aliases()` creates these
    /// arrays at store time via `get_or_create_type_array()` but they are
    /// not in the relation signature, causing Z3 "unknown constant" errors
    /// when `drain_store_chains()` references their `__out` names.
    pub(in crate::codegen_ay::chc) fn predeclare_pointer_wrapper_alias_arrays(&mut self) {
        let ptr_inners: Vec<String> = self
            .heap_state
            .type_arrays
            .keys()
            .filter_map(|k| k.strip_prefix("ptr_").map(String::from))
            .filter(|inner| {
                !inner.starts_with("ptr_")
                    && !inner.contains("NonNull_")
                    && !inner.contains("Unique_")
                    && !inner.starts_with("ref_")
            })
            .collect();

        for inner in ptr_inners {
            let mut nn_key = String::with_capacity(17 + inner.len());
            nn_key.push_str("std_ptr_NonNull_");
            nn_key.push_str(&inner);
            let mut uq_key = String::with_capacity(16 + inner.len());
            uq_key.push_str("std_ptr_Unique_");
            uq_key.push_str(&inner);
            for alias_key in [nn_key, uq_key] {
                if self.heap_state.type_arrays.contains_key(alias_key.as_str()) {
                    continue;
                }

                let (arr_name, arr_out_name) =
                    crate::codegen_ay::names::mem_array_name_pair(&self.fn_name, &alias_key);
                let elem_sort = ptr_sort();
                let arr_sort = Sort::array(ptr_sort(), elem_sort.clone());

                debug!(
                    type_key = %alias_key,
                    arr_name = %arr_name,
                    "CHC: pre-declared pointer-wrapper alias array (#2967)"
                );

                self.heap_state
                    .type_arrays
                    .insert(alias_key.into(), (Arc::clone(&arr_name), elem_sort.clone()));
                self.heap_state.array_name_to_elem_sort.insert(Arc::clone(&arr_name), elem_sort);
                self.push_state_var_pair_arc(arr_name, &arr_out_name, arr_sort);
            }
        }
    }

    // Part of #3714: predeclare_stub_internal_type_arrays and
    // predeclare_type_array_if_missing moved to codegen_decl_stub_internal.rs.

    /// Pre-declares type-indexed memory arrays needed by promoted constant
    /// references so they are included in CHC relation signatures.
    ///
    /// Part of #3222: Fix PROOF→CTREX regression for promoted constant references.
    pub(in crate::codegen_ay::chc) fn predeclare_const_ref_type_arrays(&mut self) {
        let needed: Vec<(Arc<str>, Sort)> = self
            .ref_resolution
            .const_ref_memory_inits
            .iter()
            .filter(|(tk, _, _, _, _)| {
                !self.heap_state.type_arrays.contains_key(&**tk)
                    && !super::codegen_decl_static::is_uninit_shadow_type_key(tk) // Part of #4066
            })
            .map(|(tk, es, _, _, _)| (tk.clone(), es.clone()))
            .collect();

        for (type_key, elem_sort) in needed {
            let (arr_name, arr_out_name) =
                crate::codegen_ay::names::mem_array_name_pair(&self.fn_name, &type_key);
            let arr_sort = Sort::array(ptr_sort(), elem_sort.clone());

            debug!(
                type_key = %type_key,
                "CHC: pre-declared const-ref type array (#3222)"
            );

            self.heap_state
                .type_arrays
                .insert(type_key.clone(), (Arc::clone(&arr_name), elem_sort.clone()));
            self.heap_state
                .array_name_to_elem_sort
                .insert(Arc::clone(&arr_name), elem_sort.clone());
            self.push_state_var_pair_arc(arr_name, &arr_out_name, arr_sort);
        }
    }

    /// Pre-declares type-indexed memory arrays needed by static memory mirror
    /// entries so they are included in CHC relation signatures.
    ///
    /// Part of #3854: Static memory mirrors should use the same declaration
    /// contract as promoted-const memory (#3222).
    pub(in crate::codegen_ay::chc) fn predeclare_static_memory_type_arrays(&mut self) {
        let needed: Vec<(Arc<str>, Sort)> = self
            .ref_resolution
            .static_memory_inits
            .iter()
            .filter(|(tk, _, _, _)| {
                !self.heap_state.type_arrays.contains_key(&**tk)
                    && !super::codegen_decl_static::is_uninit_shadow_type_key(tk) // Part of #4066
            })
            .map(|(tk, es, _, _)| (tk.clone(), es.clone()))
            .collect();

        for (type_key, elem_sort) in needed {
            let (arr_name, arr_out_name) =
                crate::codegen_ay::names::mem_array_name_pair(&self.fn_name, &type_key);
            let arr_sort = Sort::array(ptr_sort(), elem_sort.clone());

            debug!(
                type_key = %type_key,
                "CHC: pre-declared static-memory type array (#3854)"
            );

            self.heap_state
                .type_arrays
                .insert(type_key.clone(), (Arc::clone(&arr_name), elem_sort.clone()));
            self.heap_state
                .array_name_to_elem_sort
                .insert(Arc::clone(&arr_name), elem_sort.clone());
            self.push_state_var_pair_arc(arr_name, &arr_out_name, arr_sort);
        }
    }

    /// Collects deref pointee types from an rvalue.
    pub(in crate::codegen_ay::chc) fn collect_deref_types_from_rvalue(
        &self,
        rvalue: &Rvalue,
        deref_types: &mut BTreeMap<String, rustc_public::ty::Ty>,
    ) {
        match rvalue {
            Rvalue::Use(op) | Rvalue::Repeat(op, _) | Rvalue::Cast(_, op, _) => {
                if let Operand::Copy(place) | Operand::Move(place) = op {
                    self.collect_deref_types_from_place(place, deref_types);
                }
            }
            Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place) => {
                self.collect_deref_types_from_place(place, deref_types);
            }
            Rvalue::BinaryOp(_, lhs, rhs) | Rvalue::CheckedBinaryOp(_, lhs, rhs) => {
                if let Operand::Copy(place) | Operand::Move(place) = lhs {
                    self.collect_deref_types_from_place(place, deref_types);
                }
                if let Operand::Copy(place) | Operand::Move(place) = rhs {
                    self.collect_deref_types_from_place(place, deref_types);
                }
            }
            Rvalue::UnaryOp(_, op) => {
                if let Operand::Copy(place) | Operand::Move(place) = op {
                    self.collect_deref_types_from_place(place, deref_types);
                }
            }
            Rvalue::CopyForDeref(place) => {
                self.collect_deref_types_from_place(place, deref_types);
            }
            Rvalue::Discriminant(place) | Rvalue::Len(place) => {
                self.collect_deref_types_from_place(place, deref_types);
            }
            Rvalue::Aggregate(_, ops) => {
                for op in ops {
                    if let Operand::Copy(place) | Operand::Move(place) = op {
                        self.collect_deref_types_from_place(place, deref_types);
                    }
                }
            }
            Rvalue::ShallowInitBox(op, _) => {
                if let Operand::Copy(place) | Operand::Move(place) = op {
                    self.collect_deref_types_from_place(place, deref_types);
                }
            }
            Rvalue::NullaryOp(_) | Rvalue::ThreadLocalRef(_) => {}
        }
    }

    /// Collects deref pointee types from a place.
    ///
    /// Part of #2244: Collects (type_key, Ty) pairs so that `translate_ty` can be
    /// used for accurate sort computation in pre-declaration.
    /// Part of #2258: Includes both deref carrier pointer/reference types and
    /// pointee types to avoid late `get_or_create_type_array` creation during
    /// `load_ptr_from_memory` deref-chain translation.
    pub(in crate::codegen_ay::chc) fn collect_deref_types_from_place(
        &self,
        place: &Place,
        deref_types: &mut BTreeMap<String, rustc_public::ty::Ty>,
    ) {
        let local_idx: usize = place.local;
        let mut current_ty = self.body.locals()[local_idx].ty;
        let mut saw_deref = false;

        for proj in &place.projection {
            match proj {
                ProjectionElem::Deref => {
                    // Get pointee type and add to map
                    if let TyKind::RigidTy(RigidTy::Ref(_, inner, _))
                    | TyKind::RigidTy(RigidTy::RawPtr(inner, _)) = current_ty.kind()
                    {
                        // Part of #3661: resolve generic params for consistent type keys.
                        let carrier_key = self.type_key_for_body_ty(current_ty);
                        deref_types.entry(carrier_key.into_owned()).or_insert(current_ty);

                        let type_key = self.type_key_for_body_ty(inner);
                        deref_types.entry(type_key.into_owned()).or_insert(inner);
                        current_ty = inner;
                        saw_deref = true;
                    }
                }
                ProjectionElem::Field(_, field_ty) => {
                    current_ty = *field_ty;
                    if saw_deref {
                        // Part of #3661: resolve generic params for consistent type keys.
                        let type_key = self.type_key_for_body_ty(current_ty);
                        deref_types.entry(type_key.into_owned()).or_insert(current_ty);
                    }
                }
                ProjectionElem::Index(_)
                | ProjectionElem::ConstantIndex { .. }
                | ProjectionElem::Subslice { .. } => {
                    if let Some(elem_ty) = self.get_array_element_ty(current_ty) {
                        current_ty = elem_ty;
                        if saw_deref {
                            // Part of #3661: resolve generic params for consistent type keys.
                            let type_key = self.type_key_for_body_ty(current_ty);
                            deref_types.entry(type_key.into_owned()).or_insert(current_ty);
                        }
                    }
                }
                ProjectionElem::Downcast(_) | ProjectionElem::OpaqueCast(_) => {}
            }
        }
    }
}
