// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Memory mirroring and collection propagation helpers for block statement encoding.
//!
//! Split from codegen_stmt.rs per #3199.
//! Contains: mirror_aggregate_field_stores_to_memory, mirror_array_elements_to_flat_memory,
//! propagate_collection_shadow_state.

use rustc_public::mir::{AggregateKind, Operand, Rvalue};
use rustc_public::ty::{RigidTy, TyKind};
use std::collections::HashSet;

use crate::rustc_public_bridge::IndexedVal;
use ay_bindings::{Expr, Sort};
use tracing::debug;

use crate::codegen_ay::types::{CtorFieldExt, POINTER_WIDTH, bool_sort, int_sort, ptr_sort};

use super::ChcCtx;
use super::codegen_decl_flatten::collect_leaf_sorts;
use super::codegen_types::CodegenTypes;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Mirror aggregate operand values into field-addressed memory slots.
    ///
    /// Part of #2912: aggregate assignment to a local writes the aggregate-typed
    /// slot, but casted deref loads can read individual field addresses with a
    /// different pointee key (e.g., `*const T` bytes reinterpreted as `NonNull<T>`).
    /// Mirroring per-field stores keeps those field-addressed loads constrained.
    pub(in crate::codegen_ay::chc) fn mirror_aggregate_field_stores_to_memory(
        &mut self,
        rhs: &Rvalue,
        aggregate_ty: rustc_public::ty::Ty,
        modified_locals: &HashSet<usize>,
        base_addr: Expr,
        constraints: &mut Vec<Expr>,
    ) {
        let (operands, variant_idx) = match rhs {
            Rvalue::Aggregate(kind, operands) => {
                // Part of #3041: Extract variant index from enum Aggregate kinds.
                // For `Adt(E, variant_idx, ...)`, field offsets must come from
                // the variant's layout, not the enum's top-level layout.
                let variant_idx = match kind {
                    AggregateKind::Adt(_, vi, _, _, _) => Some(vi.to_index()),
                    _ => None, // external enum: AggregateKind
                };
                (operands, variant_idx)
            }
            _ => return, // external enum: Rvalue
        };
        if operands.is_empty() {
            return;
        }
        if !matches!(aggregate_ty.kind(), TyKind::RigidTy(RigidTy::Adt(_, _) | RigidTy::Tuple(_))) {
            return;
        }

        for (field_idx, operand) in operands.iter().enumerate() {
            let Some(field_ty) = operand.ty(self.body.locals()).ok() else {
                continue;
            };
            if self.get_type_size(field_ty) == Some(0) {
                continue;
            }
            // Part of #3041: Use variant-specific field offsets for enum aggregates.
            let Some(offset) = (if let Some(vi) = variant_idx {
                self.get_variant_field_offset(aggregate_ty, vi, field_idx)
            } else {
                self.get_field_offset(aggregate_ty, field_idx)
            }) else {
                continue;
            };
            let Some(field_expr) = self.translate_operand_with_modified(operand, modified_locals)
            else {
                continue;
            };

            let field_addr = if offset == 0 {
                base_addr.clone()
            } else {
                base_addr.clone().bvadd(Expr::bitvec_const(offset as u128, POINTER_WIDTH))
            };
            // Part of #3108: Mirror array elements when a struct/tuple field is [T; N].
            self.mirror_array_elements_to_flat_memory(
                &field_expr,
                field_ty,
                &field_addr,
                constraints,
            );
            // Part of #3608: Recursively decompose nested struct fields into
            // per-scalar-type memory stores. Without this, the outer mirror stores
            // `Inner { id }` to `mem_Inner[addr]` but `build_self_field_map` in
            // virtual dispatch inline reads `select(mem_u8, addr)` — a type key
            // mismatch that leaves the load unconstrained, producing spurious CTREX.
            self.try_decompose_struct_store(&field_addr, &field_expr, field_ty, constraints);
            if let Some(store_constraint) =
                self.build_memory_store(field_addr, field_expr, field_ty)
            {
                constraints.push(store_constraint);
            }
        }
    }

    /// Mirror array element values into flat element-type memory.
    ///
    /// Part of #2958: When a whole array `[T; N]` is assigned to a local, the
    /// Mem-level store writes to `mem_arr_T[base_addr]` (a 2D Array). However,
    /// element-wise reads through references (e.g., in `PartialEq::eq`) load
    /// from `mem_T[elem_addr]` (a flat 1D Array keyed by the element type).
    /// Without this bridge, those reads see unconstrained memory.
    ///
    /// This function emits per-element stores:
    ///   `mem_T[base_addr + i * sizeof(T)] = arr_value.select(i)`
    /// for each `i` in `0..N`, bridging the 2D and 1D memory views.
    /// Part of #2267: accepts `&Expr` to avoid caller-side clones when early
    /// returns skip the expansion loop entirely (lines 120-145).
    pub(in crate::codegen_ay::chc) fn mirror_array_elements_to_flat_memory(
        &mut self,
        value_expr: &Expr,
        array_ty: rustc_public::ty::Ty,
        base_addr: &Expr,
        constraints: &mut Vec<Expr>,
    ) {
        // Only applies to fixed-size arrays [T; N] with Array sort values.
        if !value_expr.sort().is_array() {
            return;
        }
        let Some(array_len) = self.get_array_length(array_ty) else {
            return;
        };
        let Some(elem_ty) = self.get_array_element_ty(array_ty) else {
            return;
        };
        let Some(elem_size) = self.get_type_size(elem_ty) else {
            return;
        };
        if elem_size == 0 || array_len == 0 {
            return;
        }

        // Cap expansion to avoid solver blowup for large arrays.
        // 256 matches the raw_eq element-wise comparison limit in
        // try_raw_eq_array (Part of #1739).
        const MAX_EXPANSION: usize = 256;
        if array_len > MAX_EXPANSION {
            debug!(
                array_len,
                max = MAX_EXPANSION,
                "CHC: skipping array→flat memory bridge for large array (Part of #2958)"
            );
            return;
        }

        // Part of #3095: Record the base address used for this mirror, keyed by
        // the element type. This allows `build_into_vec_data_array` to read from
        // the exact same symbolic address, ensuring select-over-store simplifies
        // within the same CHC rule even when MIR uses different locals for the
        // same allocation pointer.
        // Part of #3661: resolve generic params for consistent type keys.
        let elem_type_key = self.type_key_for_body_ty(elem_ty);
        self.heap_state.set_mirror_base_addr(&elem_type_key, base_addr.clone());

        // Part of #4086: For SIMD ADTs like i64x2, also store each element to
        // the ADT's own typed heap (mem_i64x2). The inline walker reads from
        // mem_<adt_name> when reconstructing promoted constants, so we need
        // per-element stores there too — not just in mem_<elem_ty>.
        let is_simd_adt = matches!(array_ty.kind(), TyKind::RigidTy(RigidTy::Adt(..)));

        for i in 0..array_len {
            let index_expr = Expr::bitvec_const(i as u128, POINTER_WIDTH);
            let elem_value = value_expr.clone().select(index_expr);

            let elem_addr = if i == 0 {
                base_addr.clone()
            } else {
                let byte_offset = (i * elem_size) as u128;
                base_addr.clone().bvadd(Expr::bitvec_const(byte_offset, POINTER_WIDTH))
            };

            // Part of #3879: Decompose struct elements into per-field memory
            // stores. Without this, `[StructVal; N]` populates `mem_Struct`
            // but not `mem_u32`, `mem_u64`, etc. — causing CTREX when
            // `assert_eq!` dereferences individual fields through typed memory.
            self.try_decompose_struct_store(&elem_addr, &elem_value, elem_ty, constraints);

            if let Some(store_constraint) =
                self.build_memory_store(elem_addr.clone(), elem_value.clone(), elem_ty)
            {
                constraints.push(store_constraint);
            }

            // Part of #4086: Store element to the SIMD ADT's own typed heap.
            // elem_value is BV64 and mem_i64x2 element sort is BV64, so sorts match.
            if is_simd_adt {
                if let Some(adt_store) = self.build_memory_store(elem_addr, elem_value, array_ty) {
                    constraints.push(adt_store);
                }
            }
        }

        debug!(array_len, elem_size, "CHC: mirrored array elements to flat memory (Part of #2958)");
    }

    /// Propagate collection shadow state (present, len, cap) from source to
    /// destination local on Move/Copy assignment.
    ///
    /// Part of #3057: Without this, `_5 = move _1` where _1 is a HashMap copies
    /// the data array constraint but the present/len/cap shadow variables for _5
    /// remain unconstrained, causing false counterexamples in iterator harnesses.
    pub(in crate::codegen_ay::chc) fn propagate_collection_shadow_state(
        &mut self,
        src_local: usize,
        dst_local: usize,
        constraints: &mut Vec<Expr>,
    ) {
        // Propagate present array (HashMap/HashSet/TrustMcMap).
        if let Some(src_var) = self.collections.len_state.get_present_var(src_local).cloned() {
            if let Some(dst_var) = self.collections.len_state.get_present_var(dst_local).cloned() {
                let sort = self
                    .state_var_index_by_name(&src_var)
                    .and_then(|idx| self.state_var_mgr.state_vars.get(idx))
                    .map(|(_, s)| s.clone())
                    .unwrap_or_else(|| Sort::array(int_sort(), bool_sort()));

                let src_expr =
                    if self.collections.len_state.modified_present_vars.contains(&*src_var) {
                        Expr::var(crate::codegen_ay::names::out_name(&src_var), sort.clone())
                    } else {
                        Expr::var(&*src_var, sort.clone())
                    };

                let dst_out = crate::codegen_ay::names::out_name(&dst_var);
                let dst_expr = Expr::var(&dst_out, sort);
                constraints.push(dst_expr.eq(src_expr));
                self.mark_collection_present_modified(&dst_var);
                debug!(src_local, dst_local, %src_var, %dst_var, "propagated present array");
            } else {
                // Part of #3348: Source has presence but dest doesn't (e.g., struct
                // local moved to another struct local). Register an alias so
                // get_hashmap_present_arg can resolve the collection's presence
                // when accessed through the destination local.
                self.collections.len_state.present_var_names.insert(dst_local, src_var.clone());
                debug!(
                    src_local,
                    dst_local,
                    %src_var,
                    "aliased presence var for non-collection dst (Part of #3348)"
                );
            }
        }

        // Propagate len (all collection types).
        if let Some(src_var) = self.collections.len_state.get_len_var(src_local).cloned() {
            if let Some(dst_var) = self.collections.len_state.get_len_var(dst_local).cloned() {
                let sort = ptr_sort();
                let src_expr = if self.collections.len_state.modified_len_vars.contains(&*src_var) {
                    Expr::var(crate::codegen_ay::names::out_name(&src_var), sort.clone())
                } else {
                    Expr::var(&*src_var, sort.clone())
                };

                let dst_out = crate::codegen_ay::names::out_name(&dst_var);
                let dst_expr = Expr::var(&dst_out, sort);
                constraints.push(dst_expr.eq(src_expr));
                self.mark_collection_len_modified(&dst_var);
                debug!(src_local, dst_local, %src_var, %dst_var, "propagated len");
            } else {
                // Part of #3348: Alias len var for non-collection destinations.
                self.collections.len_state.len_var_names.insert(dst_local, src_var);
            }
        }

        // Propagate cap (Vec only).
        if let Some(src_var) = self.collections.len_state.get_cap_var(src_local).cloned() {
            if let Some(dst_var) = self.collections.len_state.get_cap_var(dst_local).cloned() {
                let sort = ptr_sort();
                let src_expr = if self.collections.len_state.modified_cap_vars.contains(&*src_var) {
                    Expr::var(crate::codegen_ay::names::out_name(&src_var), sort.clone())
                } else {
                    Expr::var(&*src_var, sort.clone())
                };

                let dst_out = crate::codegen_ay::names::out_name(&dst_var);
                let dst_expr = Expr::var(&dst_out, sort);
                constraints.push(dst_expr.eq(src_expr));
                self.mark_collection_cap_modified(&dst_var);
                debug!(src_local, dst_local, %src_var, %dst_var, "propagated cap");
            } else {
                // Part of #3348: Alias cap var for non-collection destinations.
                self.collections.len_state.cap_var_names.insert(dst_local, src_var);
            }
        }
    }

    /// Propagate collection presence/len/cap aliases when an ADT Aggregate
    /// embeds a collection operand as a struct field.
    ///
    /// Part of #3348: When constructing `Array { stores: move _3, default }`,
    /// the BTreeMap operand `_3` has a presence state variable. The destination
    /// struct local needs to inherit this alias so that later field accesses
    /// (e.g., `self.stores.get(&k)`) can find the presence array through the
    /// struct local.
    pub(in crate::codegen_ay::chc) fn propagate_collection_presence_from_aggregate(
        &mut self,
        dest_local: usize,
        operands: &[Operand],
    ) {
        for operand in operands {
            let src_local = match operand {
                Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                    place.local
                }
                _ => continue,
            };
            // Propagate presence alias (BTreeMap/HashMap/HashSet).
            if let Some(presence_var) =
                self.collections.len_state.get_present_var(src_local).cloned()
            {
                if self.collections.len_state.get_present_var(dest_local).is_none() {
                    self.collections
                        .len_state
                        .present_var_names
                        .insert(dest_local, presence_var.clone());
                    debug!(
                        dest_local,
                        src_local,
                        %presence_var,
                        "aliased presence from ADT Aggregate operand (Part of #3348)"
                    );
                }
            }
            // Propagate len alias.
            if let Some(len_var) = self.collections.len_state.get_len_var(src_local).cloned() {
                if self.collections.len_state.get_len_var(dest_local).is_none() {
                    self.collections.len_state.len_var_names.insert(dest_local, len_var);
                }
            }
            // Propagate cap alias (Vec).
            if let Some(cap_var) = self.collections.len_state.get_cap_var(src_local).cloned() {
                if self.collections.len_state.get_cap_var(dest_local).is_none() {
                    self.collections.len_state.cap_var_names.insert(dest_local, cap_var);
                }
            }
        }
    }

    /// Propagate collection ghost state when a Vec is extracted through struct field projection.
    ///
    /// Part of #3284: When `_23 = Move(_4.0)` and the projected field is Vec-typed,
    /// the ghost `vec_len_23` remains unconstrained because `get_len_var(src_local=4)`
    /// returns None (local #4 is a struct, not a Vec). This method constrains the
    /// destination's ghost len/cap variables from the source Vec's data.
    ///
    /// Two strategies:
    /// 1. **Datatype extraction**: When `rhs_expr` is a proper Datatype, use
    ///    `field_select` to read `fld_len`/`fld_cap`.
    /// 2. **Flattened field access**: When the source struct is flattened into
    ///    scalar state variables, compute the leaf offset for the Vec's sub-field
    ///    and read the scalar state variable directly.
    pub(in crate::codegen_ay::chc) fn propagate_collection_ghost_through_projection(
        &mut self,
        dst_local: usize,
        rhs_expr: &Expr,
        src_local: usize,
        src_field_idx: usize,
        modified_locals: &HashSet<usize>,
        constraints: &mut Vec<Expr>,
    ) {
        // Propagate len: dst ghost vec_len -> source Vec's fld_len
        if let Some(dst_len_var) = self.collections.len_state.get_len_var(dst_local).cloned() {
            let len_expr = Self::extract_datatype_field_by_name(rhs_expr, "fld_len", ptr_sort())
                .or_else(|| {
                    self.flattened_vec_subfield_expr(
                        src_local,
                        src_field_idx,
                        "fld_len",
                        modified_locals,
                    )
                });
            if let Some(len_expr) = len_expr {
                let dst_out = crate::codegen_ay::names::out_name(&dst_len_var);
                let dst_expr = Expr::var(&dst_out, ptr_sort());
                constraints.push(dst_expr.eq(len_expr));
                self.mark_collection_len_modified(&dst_len_var);
                debug!(dst_local, %dst_len_var, "propagated ghost len through field projection (#3284)");
            }
        }

        // Propagate cap: dst ghost vec_cap -> source Vec's fld_cap
        if let Some(dst_cap_var) = self.collections.len_state.get_cap_var(dst_local).cloned() {
            let cap_expr = Self::extract_datatype_field_by_name(rhs_expr, "fld_cap", ptr_sort())
                .or_else(|| {
                    self.flattened_vec_subfield_expr(
                        src_local,
                        src_field_idx,
                        "fld_cap",
                        modified_locals,
                    )
                });
            if let Some(cap_expr) = cap_expr {
                let dst_out = crate::codegen_ay::names::out_name(&dst_cap_var);
                let dst_expr = Expr::var(&dst_out, ptr_sort());
                constraints.push(dst_expr.eq(cap_expr));
                self.mark_collection_cap_modified(&dst_cap_var);
                debug!(dst_local, %dst_cap_var, "propagated ghost cap through field projection (#3284)");
            }
        }
    }

    /// Extract a named field from a Datatype expression.
    fn extract_datatype_field_by_name(
        expr: &Expr,
        field_name: &str,
        expected_sort: Sort,
    ) -> Option<Expr> {
        let dt = expr.sort().datatype_sort()?;
        let cons = dt.constructors.first()?;
        if cons.has_field(field_name) {
            Some(expr.clone().field_select(&dt.name, field_name, expected_sort))
        } else {
            None
        }
    }

    /// Access a Vec sub-field from a flattened source struct.
    ///
    /// Part of #3284: When source local is flattened (e.g., `CnfClause(Vec<i32>)` →
    /// `[_4_fld0, _4_fld1, _4_fld2, _4_fld3]`), compute the leaf offset for the
    /// Vec's named sub-field within the flattened representation and return the
    /// corresponding scalar state variable expression.
    fn flattened_vec_subfield_expr(
        &self,
        src_local: usize,
        struct_field_idx: usize,
        vec_field_name: &str,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        if !self.flatten.flattened_tuple_locals.contains(&src_local) {
            return None;
        }
        let local_decl = self.body.locals().get(src_local)?;
        let sort = Self::translate_ty(local_decl.ty)?;
        let dt = sort.datatype_sort()?;
        let cons = dt.constructors.first()?;
        if struct_field_idx >= cons.fields.len() {
            return None;
        }

        // Leaf offset of the struct field (Vec) within the flattened representation.
        let field_leaf_offset: usize = cons.fields[..struct_field_idx]
            .iter()
            .map(|f| collect_leaf_sorts(&f.sort, 0).len())
            .sum();

        // Find the Vec sub-field's leaf offset within the Vec sort.
        let vec_sort = &cons.fields[struct_field_idx].sort;
        let vec_dt = vec_sort.datatype_sort()?;
        let vec_cons = vec_dt.constructors.first()?;
        let vec_sub_offset: usize = vec_cons
            .fields
            .iter()
            .take_while(|f| f.name != vec_field_name)
            .map(|f| collect_leaf_sorts(&f.sort, 0).len())
            .sum();

        let leaf_idx = field_leaf_offset + vec_sub_offset;
        let expr = self.flattened_local_field_expr(src_local, leaf_idx, modified_locals)?;
        debug!(
            src_local,
            struct_field_idx, vec_field_name, leaf_idx, "flattened Vec sub-field access (#3284)"
        );
        Some(expr)
    }
}
