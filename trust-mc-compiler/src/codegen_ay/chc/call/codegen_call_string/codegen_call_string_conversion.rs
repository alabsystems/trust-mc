// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! String type-conversion stub handlers.
//!
//! Covers `StringAsStr` and `StringIntoBoxedStr`. These operations convert
//! between String, &str, and Box<str> representations, propagating backing
//! metadata (byte arrays, tracked lengths, flattened field expressions) across
//! the conversion boundary.
//!
//! Split from `codegen_call_string.rs` (Part of #4071).

use std::collections::HashSet;

use ay_bindings::Expr;
use rustc_public::mir::Operand;
use tracing::debug;

use super::super::ChcCtx;
use super::super::call_accumulator::CallAccumulator;
use super::super::codegen_call_coerce::CallCoerce;
use crate::codegen_ay::names;
use crate::codegen_ay::types::POINTER_WIDTH;

/// Extension trait for String conversion stubs on `ChcCtx`.
pub(in crate::codegen_ay::chc) trait CallStringConversion {
    /// Handle `StringAsStr`: String::as_str(&self) -> &str.
    fn codegen_string_as_str(
        &mut self,
        dest_local: usize,
        collection_local: Option<usize>,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
        extra_constraints: &mut Vec<Expr>,
        extra_dests: &mut Vec<usize>,
    );

    /// Handle `StringIntoBoxedStr`: String::into_boxed_str(self) -> Box<str>.
    fn codegen_string_into_boxed_str(
        &mut self,
        dest_local: usize,
        collection_local: Option<usize>,
        modified_locals: &HashSet<usize>,
        extra_constraints: &mut Vec<Expr>,
        extra_dests: &mut Vec<usize>,
    );
}

impl<'tcx, 'body> CallStringConversion for ChcCtx<'tcx, 'body> {
    fn codegen_string_as_str(
        &mut self,
        dest_local: usize,
        collection_local: Option<usize>,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
        extra_constraints: &mut Vec<Expr>,
        extra_dests: &mut Vec<usize>,
    ) {
        // String::as_str(&self) -> &str
        // Keep the destination slice view aligned with the source String's
        // backing metadata so downstream RangeFull/PtrMetadata queries can
        // recover the current bytes and length.
        self.ref_resolution.const_ref_values.remove(&dest_local);
        self.ref_resolution.subslice_len.remove(&dest_local);
        self.ref_resolution.subslice_offset.remove(&dest_local);

        if let Some(receiver) = args.first()
            && let Some(backing) = self.resolve_string_backing(receiver, modified_locals)
        {
            self.ref_resolution.const_ref_values.insert(dest_local, backing.data);
            self.ref_resolution.subslice_len.insert(dest_local, backing.len);
            if backing.offset != Expr::bitvec_const(0u64, POINTER_WIDTH) {
                self.ref_resolution.subslice_offset.insert(dest_local, backing.offset);
            }
        } else if let Some(coll_local) = collection_local {
            if let Some(data) = self.ref_resolution.const_ref_values.get(&coll_local).cloned() {
                self.ref_resolution.const_ref_values.insert(dest_local, data);
            }
            if let Some(len) = self.ref_resolution.subslice_len.get(&coll_local).cloned() {
                self.ref_resolution.subslice_len.insert(dest_local, len);
            }
            if let Some(offset) = self.ref_resolution.subslice_offset.get(&coll_local).cloned() {
                self.ref_resolution.subslice_offset.insert(dest_local, offset);
            }
        }

        // Alias the source String's tracked length to the destination &str local.
        if let Some(coll_local) = collection_local
            && let Some(src_len_var) = self.collections.len_state.get_len_var(coll_local).cloned()
        {
            if !self.ref_resolution.subslice_len.contains_key(&dest_local) {
                self.ref_resolution
                    .subslice_len
                    .insert(dest_local, self.collection_current_len(&src_len_var));
            }
            if self.collections.len_state.get_len_var(dest_local).is_none() {
                self.collections.len_state.len_var_names.insert(dest_local, src_len_var.clone());
                debug!(dest_local, %src_len_var, "StringAsStr: aliased len to dest");
            }
        }

        // Part of #4071: When the source String was constructed by MIR-inlined
        // code (e.g., `"x".to_string()` where `String::from` was inlined by the
        // pre-codegen MIR pass), no StringFrom stub fires and the collection
        // len_state is never constrained. The len_state aliasing block above
        // sets subslice_len to `collection_current_len(src_len_var)` which is
        // an unconstrained CHC input variable. However, the flattened String
        // field fld_len (index 1) IS correctly assigned by the inlined MIR
        // assignments.
        //
        // Two fixes applied:
        // (a) Override subslice_len with the flattened fld_len so downstream
        //     PtrMetadata (including inline walker) gets the correct length.
        // (b) Constrain the &str BV128 output state var to concat(fld_len, fld_ptr)
        //     from the source String's flattened fields. Without this, the &str
        //     output is fully unconstrained even though subslice_len is correct,
        //     because the BV128 state var is what persists across CHC rules.
        if let Some(coll_local) = collection_local
            && self.flatten.flattened_local_field_count.contains_key(&coll_local)
        {
            // RustString layout: fld_ptr(0), fld_len(1), fld_cap(2)
            let fld_ptr = self.flattened_local_field_expr(coll_local, 0, modified_locals);
            let fld_len = self.flattened_local_field_expr(coll_local, 1, modified_locals);

            debug!(
                dest_local,
                coll_local,
                has_ptr = fld_ptr.is_some(),
                has_len = fld_len.is_some(),
                "StringAsStr: flattened field resolution (#4071)"
            );

            if let Some(ref len_expr) = fld_len {
                // (a) Override subslice_len metadata.
                self.ref_resolution.subslice_len.insert(dest_local, len_expr.clone());
                // Also constrain the len_state output to match the flattened field.
                if let Some(len_var) = self.collections.len_state.get_len_var(coll_local).cloned() {
                    self.collection_len_set(
                        &len_var,
                        len_expr.clone(),
                        &mut CallAccumulator::new(extra_constraints, extra_dests),
                    );
                }
            }

            // (b) Constrain the &str BV128 output = concat(len, ptr).
            // &str is encoded as BV128 = concat(len:BV64, ptr:BV64).
            if let (Some(ptr_expr), Some(len_expr)) = (fld_ptr, fld_len) {
                let fat_ptr = len_expr.concat(ptr_expr);
                if let Some((_, dest_var)) = self.resolve_destination(dest_local) {
                    debug!(
                        dest_local,
                        dest_sort = ?dest_var.sort(),
                        fat_ptr_sort = ?fat_ptr.sort(),
                        "StringAsStr: emitting BV128 constraint (#4071)"
                    );
                    if let Some(eq) = self.make_coerced_eq_constraint(
                        &dest_var,
                        fat_ptr,
                        dest_var.sort(),
                        dest_local,
                        "codegen_call_string_core::StringAsStr::fld_concat(#4071)",
                    ) {
                        extra_constraints.push(eq);
                    }
                }
                debug!(
                    dest_local,
                    coll_local, "StringAsStr: constrained &str BV128 from flattened fields (#4071)"
                );
            }
        }
        extra_dests.push(dest_local);
    }

    fn codegen_string_into_boxed_str(
        &mut self,
        dest_local: usize,
        collection_local: Option<usize>,
        modified_locals: &HashSet<usize>,
        extra_constraints: &mut Vec<Expr>,
        extra_dests: &mut Vec<usize>,
    ) {
        // String::into_boxed_str(self) -> Box<str> (#3646)
        // Layout-preserving conversion: the String's backing buffer becomes
        // an owned str. Copy byte-backing metadata, alias length, and
        // constrain the destination value from the source String's fields.
        //
        // Type mapping: RustString(fld_ptr, fld_len, fld_cap)
        //            -> Slice_bv8(fld_ptr, fld_len, fld_data)
        // fld_ptr/fld_len transfer directly; fld_data comes from the
        // byte-backing array in const_ref_values (not a RustString field).
        if let Some(coll_local) = collection_local {
            // Capture byte-backing data before copying to dest.
            let backing_data = self.ref_resolution.const_ref_values.get(&coll_local).cloned();
            if let Some(ref data) = backing_data {
                self.ref_resolution.const_ref_values.insert(dest_local, data.clone());
            }
            if let Some(len) = self.ref_resolution.subslice_len.get(&coll_local).cloned() {
                self.ref_resolution.subslice_len.insert(dest_local, len);
            }
            self.ref_resolution.subslice_offset.remove(&dest_local);

            // Alias tracked length like StringAsStr.
            if let Some(src_len_var) = self.collections.len_state.get_len_var(coll_local).cloned() {
                if self.collections.len_state.get_len_var(dest_local).is_none() {
                    self.collections
                        .len_state
                        .len_var_names
                        .insert(dest_local, src_len_var.clone());
                    debug!(dest_local, %src_len_var, "StringIntoBoxedStr: aliased len");
                }
            }

            // Constrain destination value from source String fields +
            // byte-backing array. Without this, the dest is unconstrained.
            // Part of #3655: For flattened source locals,
            // try_resolve_local_expr returns the first field (BV64) not
            // the full datatype. Use reconstruct_flattened_root instead.
            let is_flattened = self.flatten.flattened_local_field_count.contains_key(&coll_local);
            let src_expr_opt = if is_flattened {
                self.reconstruct_flattened_root(coll_local, modified_locals)
            } else {
                self.try_resolve_local_expr(coll_local, modified_locals)
            };
            let dest_res = self.resolve_destination(dest_local);
            if let Some(src_expr) = src_expr_opt
                && let Some((_, dest_var)) = dest_res
            {
                let src_sort = src_expr.sort().clone();
                let dest_sort = dest_var.sort().clone();
                if let Some(src_dt) = src_sort.datatype_name()
                    && let Some(dest_dt) = dest_sort.datatype_name()
                    && let Some(dt_info) = dest_sort.datatype_sort()
                    && let Some(ctor) = dt_info.constructors.first()
                {
                    // Build dest fields: match source by name, fall back
                    // to byte-backing const_ref_values for fld_data.
                    let fields: Option<Vec<Expr>> = ctor
                        .fields
                        .iter()
                        .map(|f| {
                            if let Some(s) = Self::get_dt_field_sort(&src_expr, &f.name) {
                                return Some(src_expr.clone().field_select(src_dt, &f.name, s));
                            }
                            if f.name == "fld_data" {
                                return backing_data.clone();
                            }
                            None
                        })
                        .collect();
                    if let Some(field_vals) = fields {
                        let dest_expr = Expr::datatype_constructor(
                            dest_dt,
                            names::cons_name(dest_dt),
                            field_vals,
                            dest_sort.clone(),
                        );
                        if let Some(eq) = self.make_coerced_eq_constraint(
                            &dest_var,
                            dest_expr,
                            dest_var.sort(),
                            dest_local,
                            "codegen_call_string_core::StringIntoBoxedStr",
                        ) {
                            extra_constraints.push(eq);
                        }
                    }
                } else if let Some(src_dt) = src_sort.datatype_name()
                    && dest_sort.datatype_name().is_none()
                    && let Some(ptr_sort) = Self::get_dt_field_sort(&src_expr, "fld_ptr")
                {
                    // Part of #3655: Box<str> encoded as BV64 pointer, not
                    // a Slice datatype. Constrain dest = source's fld_ptr.
                    let fld_ptr = src_expr.clone().field_select(src_dt, "fld_ptr", ptr_sort);
                    let eq_opt = self.make_coerced_eq_constraint(
                        &dest_var,
                        fld_ptr,
                        dest_var.sort(),
                        dest_local,
                        "codegen_call_string_core::StringIntoBoxedStr(ptr)",
                    );
                    if let Some(eq) = eq_opt {
                        extra_constraints.push(eq);
                        debug!(
                            dest_local,
                            "StringIntoBoxedStr: constrained BV64 dest to src fld_ptr"
                        );
                    }
                }

                // Part of #3655: Update obj_size to reflect shrink_to_fit.
                // In real Rust, into_boxed_str() shrinks the Vec<u8> buffer
                // to exactly len bytes. Without this, obj_size still holds the
                // original Vec capacity, causing a size mismatch in dealloc:
                // dealloc sees PtrMetadata(len) but obj_size records capacity.
                //
                // Use the tracked collection len variable (which is constrained
                // by StringFrom) rather than the flattened field directly, since
                // flattened fields may be unconstrained in this block.
                if let Some(dt_name) = src_sort.datatype_name()
                    && let Some(ptr_sort) = Self::get_dt_field_sort(&src_expr, "fld_ptr")
                {
                    let fld_ptr = src_expr.clone().field_select(dt_name, "fld_ptr", ptr_sort);
                    if let Some((obj_id_expr, _offset)) = self.split_pointer(&fld_ptr) {
                        // Prefer tracked collection len (constrained), fall back
                        // to datatype fld_len (may be unconstrained for flattened).
                        let len_expr = self
                            .collections
                            .len_state
                            .get_len_var(coll_local)
                            .map(|lv| self.collection_current_len(lv))
                            .or_else(|| {
                                Self::get_dt_field_sort(&src_expr, "fld_len")
                                    .map(|ls| src_expr.clone().field_select(dt_name, "fld_len", ls))
                            });
                        if let Some(len) = len_expr
                            && let Some(len_32) = self.coerce_to_heap_bv32(len)
                        {
                            if let Some(obj_id) = Self::const_obj_id_u32(&obj_id_expr) {
                                self.record_known_heap_alloc_size_expr(obj_id, &len_32);
                            }
                            let obj_size_in = super::super::codegen_expr_heap::obj_size_in();
                            let obj_size_out = super::super::codegen_expr_heap::obj_size_out();
                            extra_constraints
                                .push(obj_size_out.eq(obj_size_in.store(obj_id_expr, len_32)));
                            self.mark_heap_metadata_modified();
                        }
                    }
                }
            }
        }
        extra_dests.push(dest_local);
    }
}
