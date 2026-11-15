// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Per-field decomposition of whole-struct deref stores.
//!
//! Bug 3a (#1739): When `*ptr = struct_value`, the Datatype guard in
//! `build_memory_store` replaces the struct with a lossy bitvec fallback.
//! This method decomposes the store into individual field stores at
//! `base_addr + field_offset`, each with a primitive sort that passes
//! the Datatype guard.

#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use ay_bindings::{Expr, Sort, SortInner};
use tracing::{debug, warn};

use crate::codegen_ay::shared::mono_ty;
use crate::codegen_ay::types::POINTER_WIDTH;

use super::super::ChcCtx;
use super::super::codegen_types::CodegenTypes;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Decompose a whole-struct deref store into per-field memory stores.
    ///
    /// Bug 3a (#1739): When `*ptr = struct_value`, the Datatype guard in
    /// `build_memory_store` replaces the struct with a lossy bitvec fallback.
    /// This method decomposes the store into individual field stores at
    /// `base_addr + field_offset`, each with a primitive sort that passes
    /// the Datatype guard.
    ///
    /// Part of #3589: Also handles bitvec RHS (flattened locals) by extracting
    /// per-field values using bit ranges instead of Datatype field_select. This
    /// fixes the Rc<dyn Trait> store-to-load type-key mismatch where stores go
    /// to `mem_Struct` but virtual dispatch reads from `mem_u8`.
    pub(in crate::codegen_ay::chc) fn try_decompose_struct_store(
        &mut self,
        addr_expr: &Expr,
        rhs_expr: &Expr,
        store_ty: rustc_public::ty::Ty,
        constraints: &mut Vec<Expr>,
    ) -> bool {
        use rustc_public::ty::{RigidTy, TyKind};

        // Only decompose if translate_ty would produce a Datatype sort
        let sort = match ChcCtx::translate_ty(store_ty) {
            Some(sort) if sort.is_datatype() => sort,
            _ => return false, // non-enum: Option<Sort> (translate_ty returns None or non-datatype)
        };

        // Extract single-constructor struct from the AY sort
        let SortInner::Datatype(ref dt) = *sort.inner() else {
            return false;
        };
        if dt.constructors.len() != 1 {
            return false; // Multi-constructor enums not decomposable
        }
        let cons = &dt.constructors[0];
        if cons.fields.is_empty() {
            return false;
        }

        // Get field types from rustc type system (needed by build_memory_store).
        // Part of #3675 and Rule A (`shared::mono_ty::field_ty`): a field's type
        // is instantiated at the ADT's OWN arguments (`[T; LANES]` of a
        // `repr(simd)` struct is `[u8; 10]`), never the body instance's.
        let field_tys: Vec<rustc_public::ty::Ty> = match store_ty.kind() {
            TyKind::RigidTy(RigidTy::Adt(def, ref args)) => {
                let variants = def.variants();
                if variants.is_empty() {
                    return false;
                }
                let Some(tys) = variants[0]
                    .fields()
                    .iter()
                    .map(|f| mono_ty::field_ty(f, args))
                    .collect::<Option<Vec<_>>>()
                else {
                    return false;
                };
                // A field type that still names a parameter would panic in
                // build_memory_store's layout queries: bail out.
                if tys.iter().any(|ty| mono_ty::has_unresolved_params(*ty)) {
                    return false;
                }
                tys
            }
            TyKind::RigidTy(RigidTy::Tuple(fields)) => fields,
            _ => return false, // external enum: TyKind
        };

        if field_tys.len() != cons.fields.len() {
            return false; // Mismatch between rustc and AY field counts
        }

        // Part of #3589: Support both Datatype and bitvec RHS expressions.
        // Datatype RHS: use field_select to extract fields (original path).
        // Bitvec RHS: use bit extraction with precomputed ranges (new path).
        // This handles flattened locals stored to heap memory (e.g., Rc::new).
        let rhs_is_datatype = rhs_expr.sort().is_datatype();
        let rhs_is_bitvec = !rhs_is_datatype && rhs_expr.sort().is_bitvec();
        if !rhs_is_datatype && !rhs_is_bitvec {
            return false;
        }

        // For bitvec path, precompute (high, low) bit ranges for each field.
        // The bitvec concat ordering puts field 0 at the MSB, matching the
        // memory layout where field 0 goes to the lowest byte address.
        let field_bit_ranges: Vec<(u32, u32)> = if rhs_is_bitvec {
            let Some(total_width) = rhs_expr.sort().bitvec_width() else {
                return false;
            };
            let mut ranges = Vec::with_capacity(cons.fields.len());
            let mut bit_pos = total_width;
            for ay_field in &cons.fields {
                let field_bits = Self::leaf_bitvec_width(&ay_field.sort);
                if field_bits == 0 || bit_pos < field_bits {
                    return false;
                }
                bit_pos -= field_bits;
                ranges.push((bit_pos + field_bits - 1, bit_pos));
            }
            if bit_pos != 0 {
                debug!(
                    remaining = bit_pos,
                    total_width, "CHC: bitvec struct decompose: bits remaining, aborting (#3589)"
                );
                return false;
            }
            ranges
        } else {
            Vec::new()
        };

        let dt_name = &dt.name;
        let mut stored_fields = 0u32;

        for (field_idx, (field_ty, ay_field)) in
            field_tys.iter().zip(cons.fields.iter()).enumerate()
        {
            let field_offset = if let Some(off) = self.get_field_offset(store_ty, field_idx) {
                off
            } else {
                // Fail closed: unknown field offset → skip this field's store.
                // Leaving memory unconstrained (over-approximation) is safe;
                // encoding a wrong offset (heuristic) is unsound (#2315).
                // Part of #3099: reclassified from record_fallback() (DEMOTED).
                // Skipping the store leaves memory nondet — sound over-approximation.
                warn!(
                    ?store_ty,
                    field_idx, "store_adt_to_heap: field offset unknown, skipping field store"
                );
                self.record_sound_fallback_reason("store_adt_field_offset_unknown");
                continue;
            };

            let field_addr = if field_offset > 0 {
                addr_expr.clone().bvadd(Expr::bitvec_const(field_offset as i64, POINTER_WIDTH))
            } else {
                addr_expr.clone()
            };

            // Extract the field value: Datatype → field_select, bitvec → extract.
            let field_val = if rhs_is_datatype {
                rhs_expr.clone().field_select(
                    dt_name.as_str(),
                    &*ay_field.name,
                    ay_field.sort.clone(),
                )
            } else {
                let (high, low) = field_bit_ranges[field_idx];
                rhs_expr.clone().extract(high, low)
            };

            // Part of #3108: Mirror array elements to flat memory when a struct
            // field is itself an array type (e.g. `(*ptr).data = [1, 2, 3]`).
            self.mirror_array_elements_to_flat_memory(
                &field_val,
                *field_ty,
                &field_addr,
                constraints,
            );
            // Part of #3589: Recursively decompose nested struct fields into
            // per-scalar stores. Without this, a field like `inner: Inner { id: u8 }`
            // gets stored as a whole to `mem_defs_Inner[addr]`, but the inline
            // virtual dispatch translator reads from `mem_u8[addr]` (per-scalar),
            // causing a store/load type-key mismatch and false CTREX.
            if self.try_decompose_struct_store(&field_addr, &field_val, *field_ty, constraints) {
                stored_fields += 1;
                continue;
            }
            constraints.extend(self.build_memory_store_untyped(field_addr, field_val, *field_ty));
            stored_fields += 1;
        }

        if stored_fields > 0 {
            debug!(
                fields = stored_fields,
                dt_name = %dt_name,
                bitvec_path = rhs_is_bitvec,
                "CHC: decomposed struct deref store into per-field stores (#1739, #3589)"
            );
        }
        stored_fields > 0
    }

    /// Compute the total bitvec width of a AY sort's leaf representation.
    ///
    /// Part of #3589: For bitvec sorts, returns the width directly. For
    /// single-constructor Datatype sorts, recursively sums the leaf bitvec
    /// widths of all fields. Returns 0 for sorts that can't be flattened.
    fn leaf_bitvec_width(sort: &Sort) -> u32 {
        if let Some(w) = sort.bitvec_width() {
            return w;
        }
        if sort.is_bool() {
            return 1;
        }
        if let Some(dt) = sort.datatype_sort() {
            if dt.constructors.len() == 1 {
                let total: u32 = dt.constructors[0]
                    .fields
                    .iter()
                    .map(|f| Self::leaf_bitvec_width(&f.sort))
                    .sum();
                if total > 0 {
                    return total;
                }
            }
        }
        0
    }
}
