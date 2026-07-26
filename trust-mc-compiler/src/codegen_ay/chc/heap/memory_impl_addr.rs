// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CHC address translation: reference-to-address, pointer dereference, local allocation.
//! Converted from include!() to proper module per #2595.
//!
//! Extracted from memory_impl.rs per #2246 (500 LOC threshold).

use std::collections::HashSet;
use std::sync::Arc;

use rustc_public::mir::{Place, ProjectionElem};
use tracing::{debug, warn};

use crate::rustc_public_bridge::IndexedVal;
use ay_bindings::{Expr, Sort};

use crate::codegen_ay::types::{
    POINTER_WIDTH, SignExtension, coerce_bitvec_width_safe, ptr_sort, unflatten_bitvec_to_datatype,
};

use super::ChcCtx;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    // ============================================================================
    // Abstract Heap Model — Address Translation (Part of #869, #891)
    // ============================================================================

    /// Translates a reference to a symbolic address.
    ///
    /// Computes the address of a place by:
    /// 1. Getting the base local's address
    /// 2. For each projection:
    ///    - Deref: Load pointer value from memory (becomes new base)
    ///    - Field/Index: Add offset to current address
    ///
    /// At Mem level, this enables verification of ALL reference patterns,
    /// including `&(*ptr).field` which requires following the pointer.
    ///
    /// Part of #869: Mem-level Ref/AddressOf encoding with Deref support.
    pub(in crate::codegen_ay::chc) fn translate_ref_to_address(
        &mut self,
        place: &Place,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        let local_idx: usize = place.local;

        // Get base address for the local
        let mut current_addr = self.get_or_create_local_address(local_idx)?;
        let mut current_ty = self.body.locals()[local_idx].ty;

        // If no projections, return base address directly
        if place.projection.is_empty() {
            return Some(current_addr);
        }

        // Track active variant for Downcast→Field projection chains.
        // Part of #3041: When Downcast sets the variant, the next Field
        // projection uses variant-specific offsets from VariantsShape::Multiple.
        let mut active_variant: Option<usize> = None;

        // Part of #3495: Track whether we're still at the base local (no projections
        // applied yet). Used for state-variable-first Deref resolution.
        let mut at_base_local = true;

        // Process projections iteratively to handle Deref (#869)
        for proj in &place.projection {
            match proj {
                ProjectionElem::Deref => {
                    // Deref: load from current address to get pointer value
                    // The loaded value IS the new address (pointer following)
                    let pointee_ty = Self::deref_pointee_ty(current_ty)?;

                    // Part of #3495: When dereferencing the base local, prefer state
                    // variable resolution over memory load. Call terminator destinations
                    // (e.g., RangeFrom Index::index results) have their values set via
                    // CHC state variable constraints but NOT mirrored to type-indexed
                    // memory. Loading from memory yields an unconstrained expression,
                    // causing false CTREX in downstream indexing. The state variable
                    // system always carries the correct value from the previous block.
                    let loaded_addr = if at_base_local {
                        self.known_stack_addr_expr(local_idx)
                            .or_else(|| {
                                // fc-interior-mut: resolve the TRUE referent
                                // address through ref-resolution BEFORE the
                                // register lane. The register lane can carry a
                                // fabricated value-as-address (a flattened
                                // referent VALUE laundered through an opaque
                                // pointer-sorted state var by ref-
                                // dematerialization, obj_id forced to 0). The
                                // READ side (try_resolve_deref_cascade →
                                // try_resolve_deref_via_ref_targets) already
                                // resolves ref_targets FIRST with the same
                                // gate; mirroring that priority here keeps
                                // value reads and deref checks/stores agreeing
                                // on the same object.
                                self.deref_addr_via_ref_target_recovery(
                                    local_idx,
                                    modified_locals,
                                )
                            })
                            .or_else(|| {
                            self.try_resolve_local_expr(local_idx, modified_locals).and_then(
                                |expr| {
                                // State vars must normalize to a thin storage address before
                                // later Field/Index byte-offset arithmetic.
                                let addr_expr =
                                    self.normalize_deref_address_expr(expr, current_ty)?;
                                if addr_expr.sort().bitvec_width() == Some(POINTER_WIDTH) {
                                    debug!(
                                        local_idx,
                                        "CHC: translate_ref_to_address - Deref via state var (Part of #3495)"
                                    );
                                    Some(addr_expr)
                                } else {
                                    None
                                }
                                },
                            )
                        })
                            .or_else(|| {
                                self.load_ptr_from_memory(current_addr.clone(), current_ty)
                                    .and_then(|expr| {
                                        self.normalize_deref_address_expr(expr, current_ty)
                                    })
                            })
                    } else {
                        // After projections — must use memory load
                        self.load_ptr_from_memory(current_addr.clone(), current_ty)
                            .and_then(|expr| self.normalize_deref_address_expr(expr, current_ty))
                    }?;
                    current_addr = loaded_addr;
                    current_ty = pointee_ty;
                    active_variant = None; // Deref resets variant context
                    debug!(?current_ty, "CHC: translate_ref_to_address - Deref load");
                }
                ProjectionElem::Field(field_idx, field_ty) => {
                    // Field: add field offset to current address.
                    // If a Downcast preceded this, use variant-specific layout offsets.
                    let offset_opt = if let Some(variant_idx) = active_variant.take() {
                        self.get_variant_field_offset(current_ty, variant_idx, *field_idx)
                    } else {
                        self.get_field_offset(current_ty, *field_idx)
                    };
                    let offset = offset_opt?;
                    if offset > 0 {
                        let offset_expr = Expr::bitvec_const(offset as i64, POINTER_WIDTH);
                        current_addr = current_addr.bvadd(offset_expr);
                    }
                    current_ty = *field_ty;

                    debug!(field_idx, offset, "CHC: translate_ref_to_address - Field offset");
                }
                ProjectionElem::Index(index_local) => {
                    // Index: add (index * element_size) to current address
                    let elem_ty = self.get_array_element_ty(current_ty)?;
                    let elem_size = self.get_type_size(elem_ty)?;
                    let index_expr = self.resolve_local_expr(*index_local, modified_locals)?;

                    // Part of #1888: Emit bounds check for array indexing.
                    // If we can determine array length at compile time, emit:
                    // bounds_check = (index < array_length)
                    // This becomes an error rule if violated.
                    if let Some(array_len) = self.get_array_length(current_ty) {
                        // Coerce index to pointer width for comparison
                        let index_check = coerce_bitvec_width_safe(
                            index_expr.clone(),
                            POINTER_WIDTH,
                            SignExtension::ZeroExtend,
                        );
                        let len_expr = Expr::bitvec_const(array_len as u128, POINTER_WIDTH);
                        // unsigned less-than: index < array_length
                        let bounds_check = index_check.bvult(len_expr);
                        self.heap_state.pending_checks.push(bounds_check);
                        debug!(
                            array_len,
                            "CHC: translate_ref_to_address - emitted bounds check (Part of #1888)"
                        );
                    }

                    // Coerce index to pointer width and multiply by element size
                    // Part of #2875: Int-lifted indices need BV conversion first.
                    let index_expr = if index_expr.sort().is_int() {
                        index_expr.int2bv(POINTER_WIDTH)
                    } else {
                        index_expr
                    };
                    let index_64 = coerce_bitvec_width_safe(
                        index_expr,
                        POINTER_WIDTH,
                        SignExtension::ZeroExtend,
                    );
                    let byte_offset =
                        index_64.bvmul(Expr::bitvec_const(elem_size as i64, POINTER_WIDTH));
                    current_addr = current_addr.bvadd(byte_offset);
                    current_ty = elem_ty;

                    debug!(elem_size, "CHC: translate_ref_to_address - Index offset");
                }
                ProjectionElem::ConstantIndex { offset, min_length: _, from_end } => {
                    // Constant index: add (index * element_size) to current address
                    // from_end=true means offset is from the end (e.g., arr[arr.len() - offset])
                    // Part of #1918: Support from_end indexing
                    let elem_ty = self.get_array_element_ty(current_ty)?;
                    let elem_size = self.get_type_size(elem_ty)?;

                    let actual_index = if *from_end {
                        // Need array length to compute actual index = len - offset
                        let array_len = self
                            .get_array_length(current_ty)
                            .ok_or_else(|| {
                                warn!("CHC: from_end ConstantIndex requires known array length");
                            })
                            .ok()?;
                        // For from_end, offset=1 means last element (index = len-1)
                        // offset=2 means second-to-last (index = len-2), etc.
                        if *offset as usize > array_len {
                            warn!(offset, array_len, "CHC: from_end offset exceeds array length");
                            return None;
                        }
                        (array_len as u64) - *offset
                    } else {
                        *offset
                    };

                    // Part of #1888: Emit bounds check for constant array indexing.
                    if let Some(array_len) = self.get_array_length(current_ty) {
                        let index_expr = Expr::bitvec_const(actual_index as u128, POINTER_WIDTH);
                        let len_expr = Expr::bitvec_const(array_len as u128, POINTER_WIDTH);
                        // unsigned less-than: index < array_length
                        let bounds_check = index_expr.bvult(len_expr);
                        self.heap_state.pending_checks.push(bounds_check);
                        debug!(
                            actual_index,
                            array_len,
                            from_end,
                            "CHC: translate_ref_to_address - emitted ConstantIndex bounds check"
                        );
                    }

                    let byte_offset = actual_index * (elem_size as u64);
                    if byte_offset > 0 {
                        current_addr = current_addr
                            .bvadd(Expr::bitvec_const(byte_offset as i64, POINTER_WIDTH));
                    }
                    current_ty = elem_ty;
                }
                ProjectionElem::Downcast(variant_idx) => {
                    // Downcast selects an enum variant for subsequent Field projections.
                    // The memory address doesn't change (variant data is at the same
                    // base address within the enum), but field offsets must come from
                    // the variant's layout, not the enum's overall layout.
                    // Part of #3041: Category B fix.
                    active_variant = Some(variant_idx.to_index());
                    debug!(
                        variant_idx = variant_idx.to_index(),
                        "CHC: translate_ref_to_address - Downcast variant"
                    );
                }
                ProjectionElem::Subslice { from, to: _, from_end: _ } => {
                    // Part of #3306: SubSlice shifts the base address by
                    // `from * elem_size` bytes into the source array.
                    let elem_ty = self.get_array_element_ty(current_ty)?;
                    let elem_size = self.get_type_size(elem_ty)?;
                    let byte_offset = *from * (elem_size as u64);
                    if byte_offset > 0 {
                        current_addr = current_addr
                            .bvadd(Expr::bitvec_const(byte_offset as i64, POINTER_WIDTH));
                    }
                    // current_ty stays as array type; address is now at subslice start.
                    active_variant = None;
                }
                ProjectionElem::OpaqueCast(_) => {
                    // Part of #1351: OpaqueCast is transparent — no address change.
                    // Matches inline path (projected_assign.rs:370, place.rs:237).
                }
            }
            // After any projection, we're no longer at the base local.
            at_base_local = false;
        }

        Some(current_addr)
    }

    /// fc-interior-mut: recover the TRUE (obj_id, offset) address behind a
    /// Deref of `local_idx` from ref-resolution, for use when the register
    /// lane yielded a fabricated value-as-address (a flattened referent VALUE
    /// laundered through a pointer-sorted local, obj_id forced to 0) or
    /// nothing at all.
    ///
    /// Trust basis and gating mirror the READ side
    /// (`try_resolve_deref_via_ref_targets`, #2110/#3452): safe-reference
    /// locals may resolve through `ref_targets` at Mem level because ref
    /// targets are assigned via register with guaranteed-correct values; raw
    /// pointers only when call-forwarded (e.g. `UnsafeCell::get` results) and
    /// never when carrying a pointer-arithmetic offset (`subslice_offset`).
    /// Keeping the ADDRESS side on the same resolution priority as the value
    /// READ side makes deref checks and value reads agree on the same object.
    ///
    /// Returns `None` when recovery is not permitted or the referent place
    /// has no computable address — callers fall through to their existing
    /// fail-closed lanes (never fabricate).
    fn deref_addr_via_ref_target_recovery(
        &mut self,
        local_idx: usize,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        // Pointer-arithmetic offsets invalidate place-level identity.
        if self.ref_resolution.subslice_offset.contains_key(&local_idx) {
            return None;
        }
        let base_local_ty = self.body.locals().get(local_idx)?.ty;
        let is_raw_ptr = matches!(
            base_local_ty.kind(),
            rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::RawPtr(..))
        );
        if is_raw_ptr && !self.ref_resolution.call_forwarded_raw_ptrs.contains(&local_idx) {
            return None;
        }
        // Depth guard against self-referencing ref_targets cycles (#3823):
        // translate_ref_to_address below can re-enter this recovery lane.
        self.deref_resolve_depth += 1;
        let result = if self.deref_resolve_depth > 4 {
            warn!(
                local_idx,
                depth = self.deref_resolve_depth,
                "CHC: deref address ref-target recovery depth exceeded"
            );
            None
        } else {
            self.ref_resolution.ref_targets.get(&local_idx).cloned().and_then(|rt| {
                if rt.local == local_idx {
                    return None;
                }
                let referent = Place { local: rt.local, projection: rt.projections };
                let addr = self.translate_ref_to_address(&referent, modified_locals)?;
                if addr.sort().bitvec_width() == Some(POINTER_WIDTH) {
                    debug!(
                        local_idx,
                        referent = rt.local,
                        "CHC: translate_ref_to_address - Deref via ref-target recovery \
                         (fc-interior-mut)"
                    );
                    Some(addr)
                } else {
                    None
                }
            })
        };
        self.deref_resolve_depth -= 1;
        result
    }

    /// Loads a pointer value from memory at the given address.
    ///
    /// Used by `translate_ref_to_address` for Deref projections.
    /// Part of #869: Deref chain support.
    pub(in crate::codegen_ay::chc) fn load_ptr_from_memory(
        &mut self,
        addr: Expr,
        pointer_ty: rustc_public::ty::Ty,
    ) -> Option<Expr> {
        let pointer_ty = self.resolve_body_ty(pointer_ty);
        // Get or create the pointer type array
        let ptr_bv = ptr_sort();
        let type_key = self.type_key_for_body_ty(pointer_ty);
        let arr_sort = Sort::array(ptr_sort(), ptr_bv.clone());

        // Use input or output array depending on store chain state
        let (arr_name_in, arr_name_out, _elem_sort, is_new) =
            self.heap_state.get_or_create_type_array(&type_key, ptr_bv, &self.fn_name);
        // Part of #3184: Mark this type array as read (pointer address load).
        // Part of #3436: Per-block tracking for error-path-aware pruning.
        self.heap_state.mark_type_array_read(&arr_name_in, self.current_encode_bb);
        // Part of #2970: register late-created type arrays as state variable pairs.
        if is_new {
            self.push_late_state_var_pair(
                Arc::clone(&arr_name_in),
                &arr_name_out,
                arr_sort.clone(),
            );
        }

        let arr_expr = if let Some(accumulated) = self.heap_state.get_store_chain(&type_key) {
            accumulated.clone()
        } else {
            Expr::var(arr_name_in.as_ref(), arr_sort)
        };

        // Part of #3608: Store-to-load forwarding for pointer loads.
        if let Some((obj_id, offset)) = Self::try_extract_constant_addr(&addr) {
            let fwd_key = ((obj_id as u64) << 32) | (offset as u64);
            if let Some((store_bb, forwarded_value)) =
                self.heap_state.store_forward_map.get(&fwd_key).cloned()
                && store_bb == self.current_encode_bb
            {
                debug!(
                    obj_id,
                    offset, "CHC: load_ptr_from_memory - store-to-load forwarding (#3608)"
                );
                return Some(forwarded_value);
            }
            // Part of #3871: Cross-block persistent pointer forwarding.
            if let Some(forwarded_ptr) =
                self.heap_state.region_pointer_forwards.get(&fwd_key).cloned()
            {
                debug!(
                    obj_id,
                    offset, "CHC: load_ptr_from_memory - cross-block pointer forwarding (#3871)"
                );
                return Some(forwarded_ptr);
            }
        }

        let result = arr_expr.select(addr);

        debug!("CHC: load_ptr_from_memory - pointer dereference");

        Some(result)
    }

    /// Gets or creates a symbolic address for a local variable.
    ///
    /// Stack locals get symbolic addresses based on their allocation ID.
    /// The address is a 64-bit bitvector encoding (obj_id, offset).
    /// Part of #869: Mem-level Ref/AddressOf encoding.
    #[must_use]
    pub(in crate::codegen_ay::chc) fn get_or_create_local_address(
        &mut self,
        local_idx: usize,
    ) -> Option<Expr> {
        // Check if we already have an address for this local
        if let Some((obj_id, _addr_name)) = self.heap_state.local_addresses.get(&local_idx) {
            // Return the same concrete address that was created initially
            // This ensures consistency: always return (obj_id << 32) | 0
            let obj_id_expr = Expr::bitvec_const(*obj_id as i128, 32);
            let zero_offset = Expr::bitvec_const(0, 32);
            return Some(obj_id_expr.concat(zero_offset));
        }

        // Allocate object ID for this local
        let obj_id = self.heap_state.next_alloc_id().or_else(|| {
            warn!(local_idx, "CHC: allocation ID overflow for local address");
            None
        })?;

        // Create symbolic address name (for debugging)
        // Part of #2267: combined allocation avoids intermediate state_var_name String.
        let addr_name = crate::codegen_ay::names::state_var_addr_name(&self.fn_name, local_idx);
        self.heap_state.insert_local_address(local_idx, obj_id, addr_name.clone());

        // Lazily-allocated locals (for example arguments/return place) were not
        // pre-seeded by entry allocation. Seed metadata facts now so subsequent
        // heap-access checks cannot treat this stack object as invalid.
        // Part of #112: Skip metadata updates when int_lift is active — obj_valid
        // and obj_size are not declared as state variables in int-lift mode, so
        // referencing them produces "unknown constant" Z3 parse errors.
        let obj_id_expr = Expr::bitvec_const(obj_id as i128, 32);
        if !self.int_lift {
            let obj_valid = self.current_obj_valid_array();
            self.heap_state
                .pending_updates
                .push(obj_valid.select(obj_id_expr.clone()).eq(Expr::bool_const(true)));
            // Part of #3436: track that this block reads heap metadata.
            self.heap_state.mark_metadata_accessed(self.current_encode_bb);
            if let Some(local_decl) = self.body.locals().get(local_idx)
                && let Some(size) =
                    self.get_type_size(local_decl.ty).and_then(|s| u32::try_from(s).ok())
            {
                let obj_size = self.current_obj_size_array();
                self.heap_state.pending_updates.push(
                    obj_size.select(obj_id_expr.clone()).eq(Expr::bitvec_const(size as i128, 32)),
                );
            }
        }

        // Create address expression: (obj_id << 32) | 0
        // Using split-pointer model from ay-bindings memory module (upstream ay)
        let zero_offset = Expr::bitvec_const(0, 32);
        let addr = obj_id_expr.concat(zero_offset);

        debug!(
            local_idx,
            obj_id,
            addr_name = %addr_name,
            "CHC: allocated address for local"
        );

        Some(addr)
    }

    /// Coerce a loaded memory value back to the requested pointee sort when needed.
    ///
    /// Part of #1739: typed memory may store enum values in flattened bitvector
    /// form; callers still expect a Datatype expression for projection/downcast.
    pub(in crate::codegen_ay::chc) fn coerce_loaded_value_for_pointee(
        value: Expr,
        pointee_sort: Option<&Sort>,
    ) -> Expr {
        if let Some(sort) = pointee_sort
            && sort.is_datatype()
            && value.sort().is_bitvec()
            && let Some(dt_expr) = unflatten_bitvec_to_datatype(&value, sort)
        {
            return dt_expr;
        }
        value
    }
}
