// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Assignment helper functions (converted from include!() per #2595).

use std::sync::Arc;

use super::{IntoOption, SortInner, StatementCodegen};
use crate::codegen_ay::types::{POINTER_WIDTH, ptr_sort};
use crate::kani_middle::abi::LayoutOf;
use ay_bindings::{Expr, Sort};
use rustc_public::mir::{Operand, Place};
use rustc_public::ty::{RigidTy, TyKind};
use tracing::debug;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    pub(super) fn track_aggregate_ref_pointees(&mut self, base_name: &str, operands: &[Operand]) {
        for (field_idx, operand) in operands.iter().enumerate() {
            match operand {
                Operand::Copy(src) | Operand::Move(src) => {
                    let src_base = self.ssa_base_name(src);
                    // Piecewise (#2076-flattened) VALUE propagation into the aggregate
                    // field. A flattened `Option`-like enum does not live in one env
                    // slot: `{base}` holds the payload bitvec, `{base}.0` the
                    // discriminant and `{base}_variant_V_field_F` the variant payload.
                    // The aggregate constructor only ever reads `{base}` (via
                    // `codegen_operand`), so building a closure/tuple/struct out of
                    // such a value USED to drop the discriminant: the later
                    // `x.i` read resolved `{lhs}_field_{i}` to a bare bitvec and
                    // `Discriminant` fell through to the "bitvec-stored enum
                    // discriminant: using symbolic variable (both variants explored)"
                    // over-approximation, so `Some(v)` and `None` became
                    // indistinguishable downstream (the `type_annotation_needed`
                    // `opt.or(Some(T::default()))` contract: `Option::or`'s inlined
                    // `match self` read a FREE discriminant, so `result.is_some()`
                    // was falsifiable IN THE MODEL).
                    //
                    // Re-key the entries onto `{base_name}_field_{i}`, which is
                    // exactly the name `ssa_base_name` produces for the `Field(i)`
                    // read of this aggregate. SOUND: the aggregate field IS a copy of
                    // `src`, so its components are copies of `src`'s components;
                    // `apply_flattened_value_entries` declares a fresh SSA var per
                    // entry and equates it to the source term under the current path
                    // condition. This strictly REMOVES an over-approximation — it
                    // fabricates no value and drops no obligation. The tuple
                    // aggregate path (`try_codegen_flattened_tuple_aggregate`)
                    // already does the same propagation for the same reason (#3133);
                    // this is the missing sibling for closure/struct/enum aggregates.
                    let flattened_entries =
                        Self::collect_flattened_value_entries(&self.current_env, &src_base);
                    if !flattened_entries.is_empty() {
                        let lhs_field_base =
                            crate::codegen_ay::names::indexed_field_name(base_name, field_idx);
                        debug!(
                            "aggregate: propagating {} flattened entries {} (field {}) -> {}",
                            flattened_entries.len(),
                            src_base,
                            field_idx,
                            lhs_field_base
                        );
                        self.apply_flattened_value_entries(&lhs_field_base, flattened_entries);
                    }
                    // Direct reference propagation: src itself is a reference
                    if let Some(pointee) = self.ref_pointees.get(src_base.as_str()).cloned() {
                        let lhs_field_base =
                            crate::codegen_ay::names::indexed_field_name(base_name, field_idx);
                        debug!(
                            "aggregate: propagating ref {} (field {}) -> {} (pointee={})",
                            src_base, field_idx, lhs_field_base, pointee
                        );
                        self.ref_pointees.insert(std::sync::Arc::from(lhs_field_base), pointee);
                    }
                    // Nested struct propagation (#441): if src contains ref fields,
                    // propagate them to the destination's nested field paths.
                    // E.g., for `Wrapper { inner: ref_holder }`, copy ref_holder_field_0
                    // to wrapper_field_0_field_0.
                    // Use BTreeMap range query for O(log n + k) prefix scanning (#1337)
                    let mut prefix = String::with_capacity(src_base.len() + 7);
                    prefix.push_str(&src_base);
                    prefix.push_str("_field_");
                    let arc_prefix: std::sync::Arc<str> = std::sync::Arc::from(prefix.as_str());
                    let nested_refs: Vec<_> = self
                        .ref_pointees
                        .range(arc_prefix..)
                        .take_while(|(k, _)| k.starts_with(prefix.as_str()))
                        .map(|(k, v)| (std::sync::Arc::clone(k), std::sync::Arc::clone(v)))
                        .collect();
                    for (nested_key, nested_pointee) in nested_refs {
                        // Extract the suffix after src_base (e.g., "_field_0")
                        let suffix = &nested_key[src_base.len()..];
                        let lhs_nested_base = {
                            use std::fmt::Write;
                            let mut s =
                                String::with_capacity(base_name.len() + 7 + 10 + suffix.len());
                            s.push_str(base_name);
                            s.push_str("_field_");
                            let _ = write!(&mut s, "{field_idx}");
                            s.push_str(suffix);
                            s
                        };
                        debug!(
                            "aggregate: propagating nested ref {} -> {} (pointee={})",
                            nested_key, lhs_nested_base, nested_pointee
                        );
                        self.ref_pointees
                            .insert(std::sync::Arc::from(lhs_nested_base), nested_pointee);
                    }
                }
                Operand::Constant(c) => {
                    let const_ty = c.const_.ty();
                    if let TyKind::RigidTy(RigidTy::Ref(_, pointee_ty, _)) = const_ty.kind()
                        && let Some(pointee_expr) =
                            self.try_codegen_const_ref_pointee(&c.const_, pointee_ty)
                    {
                        let pointee_base: Arc<str> = {
                            use std::fmt::Write;
                            let fn_name = self.ctx.current_fn_name();
                            let mut s = String::with_capacity(
                                fn_name.len() + "::const_pointee_".len() + 10,
                            );
                            s.push_str(fn_name);
                            s.push_str("::const_pointee_");
                            let _ = write!(&mut s, "{}", self.synthetic_pointee_counter);
                            Arc::from(s)
                        };
                        self.synthetic_pointee_counter += 1;

                        let mut pointee_name = String::with_capacity(pointee_base.len() + 2);
                        pointee_name.push_str(&pointee_base);
                        pointee_name.push_str("_0");
                        let pointee_sort = pointee_expr.sort().clone();
                        let pointee_var = self.ctx.declare_var(&pointee_name, pointee_sort);
                        self.assert_ssa_def(pointee_var.clone(), pointee_expr, &pointee_base);
                        self.env_update(Arc::clone(&pointee_base), pointee_var);

                        let lhs_field_base =
                            crate::codegen_ay::names::indexed_field_name(base_name, field_idx);
                        debug!(
                            "aggregate: propagating const ref (field {}) -> {} (pointee={})",
                            field_idx, lhs_field_base, pointee_base
                        );
                        self.ref_pointees.insert(Arc::from(lhs_field_base), pointee_base);
                    }
                }
            }
        }
    }

    /// Reconstruct a struct datatype with one field updated.
    ///
    /// Given an expression of struct type, creates a new struct expression with the
    /// field at `field_indices[0]` replaced by `new_value`. For nested field access
    /// (multiple indices), only the first level is supported currently.
    ///
    /// Part of #1039: Enable struct field mutation through Box by reconstructing
    /// the struct with the updated field for heap_pointees tracking.
    pub(super) fn update_struct_field(
        &self,
        old_struct: &Expr,
        field_indices: &[usize],
        new_value: Expr,
    ) -> Option<Expr> {
        // Currently only support single-level field update
        if field_indices.len() != 1 {
            debug!(
                "update_struct_field: nested field update not supported, indices={:?}",
                field_indices
            );
            return None;
        }
        let target_field = field_indices[0];

        // Get the struct's datatype sort (borrow from Arc, avoid full DatatypeSort clone)
        let SortInner::Datatype(dt) = old_struct.sort().inner() else {
            debug!("update_struct_field: not a datatype sort: {:?}", old_struct.sort());
            return None;
        };

        // Single-constructor datatypes (structs) only
        if dt.constructors.len() != 1 {
            debug!("update_struct_field: multi-constructor datatype not supported: {}", dt.name);
            return None;
        }

        let cons = &dt.constructors[0];
        let num_fields = cons.fields.len();

        if target_field >= num_fields {
            debug!(
                "update_struct_field: field index {} out of bounds (num_fields={})",
                target_field, num_fields
            );
            return None;
        }

        // Build field expressions: extract existing fields, replace target.
        // field_select accepts impl Into<String>, so pass &str to avoid String clones.
        let mut field_exprs = Vec::with_capacity(num_fields);
        let mut new_value = Some(new_value);
        for (i, field_def) in cons.fields.iter().enumerate() {
            if i == target_field {
                field_exprs.push(new_value.take()?);
            } else {
                // Extract existing field value using field_select
                let field_expr = old_struct.clone().field_select(
                    &*dt.name,
                    &*field_def.name,
                    field_def.sort.clone(),
                );
                field_exprs.push(field_expr);
            }
        }

        debug!(
            "update_struct_field: reconstructed {} with field {} updated",
            dt.name, target_field
        );

        // Construct new struct with updated field
        Some(Expr::datatype_constructor(
            &*dt.name,
            &*cons.name,
            field_exprs,
            old_struct.sort().clone(),
        ))
    }

    /// Compile-time cap on array materialization loop length.
    /// Arrays larger than this are skipped (over-approximation is sound).
    pub(super) const MAX_MATERIALIZE_ELEMENTS: u64 = 1024;

    /// #1224: Materialize a fixed-size array to byte-addressed memory.
    ///
    /// When taking the address of a stack array, the SMT Array representation
    /// is not connected to the global memory model. This function adds constraints
    /// that tie each array element to memory at the corresponding offset.
    ///
    /// Returns true if materialization was performed, false otherwise.
    pub(super) fn try_materialize_array_to_memory(
        &mut self,
        addr: &Expr,
        array_value: &Expr,
        ty: rustc_public::ty::Ty,
    ) -> bool {
        // Check if this is a fixed-size array type
        let TyKind::RigidTy(RigidTy::Array(elem_ty, len_const)) = ty.kind() else {
            return false;
        };

        // Get the array length
        let Some(len) = len_const.eval_target_usize().into_option() else {
            debug!("#1224: Could not evaluate array length constant");
            return false;
        };

        // Cap materialization to prevent compiler hang on very large arrays (Part of #2511)
        if len > Self::MAX_MATERIALIZE_ELEMENTS {
            tracing::warn!(
                len,
                max = Self::MAX_MATERIALIZE_ELEMENTS,
                "#1224: Array too large for bounded materialization; skipping"
            );
            // Part of #3211: Track constraint drop in demotion pipeline.
            self.ctx.unsupported_with_fallback(
                "array_materialize_overflow",
                "array too large for bounded materialization",
            );
            return false;
        }

        // Get element size
        let layout = LayoutOf::new(elem_ty);
        let Some(elem_size) = layout.size_of() else {
            debug!("#1224: Could not determine element size for {:?}", elem_ty);
            return false;
        };

        // For zero-sized elements, no memory materialization needed
        if elem_size == 0 {
            debug!("#1224: Skipping ZST array materialization");
            return true;
        }

        // Compute element bit width with overflow check (Part of #2511)
        let Some(elem_bits) = elem_size.checked_mul(8) else {
            tracing::warn!(
                elem_size,
                "#1224: Element size overflow in bit-width calculation; skipping"
            );
            // Part of #3211: Track constraint drop in demotion pipeline.
            self.ctx.unsupported_with_fallback(
                "array_materialize_overflow",
                "element size overflow in bit-width calculation",
            );
            return false;
        };
        let Ok(elem_width) = u32::try_from(elem_bits) else {
            tracing::warn!(elem_bits, "#1224: Element bit width exceeds u32 range; skipping");
            // Part of #3211: Track constraint drop in demotion pipeline.
            self.ctx.unsupported_with_fallback(
                "array_materialize_overflow",
                "element bit width exceeds u32 range",
            );
            return false;
        };

        debug!("#1224: Materializing array to memory: len={}, elem_size={}", len, elem_size);

        // Materialize each element to memory
        // The SMT array uses indices 0, 1, 2, ... (element indices)
        // Memory uses addresses addr, addr+elem_size, addr+2*elem_size, ...
        for i in 0..len {
            // Checked byte offset calculation (Part of #2511)
            let Some(byte_offset) = (i as usize).checked_mul(elem_size) else {
                tracing::warn!(
                    i,
                    elem_size,
                    "#1224: Byte offset overflow at element {}; stopping materialization",
                    i
                );
                return false;
            };
            let offset_expr = Expr::bitvec_const(byte_offset as u128, POINTER_WIDTH);
            let elem_addr = addr.clone().bvadd(offset_expr);

            // Select element i from the SMT array
            let index_expr = Expr::bitvec_const(i as u128, POINTER_WIDTH);
            let elem_value = array_value.clone().select(index_expr);

            // Store the element to memory
            // For byte-sized elements, store directly
            // For larger elements, store each byte
            // Part of #4215: Non-BV sorts (Datatype, Array) from SMT array select
            // cannot be byte-decomposed with zero_extend/extract. Delegate to
            // store_memory_bytes which handles these sorts symbolically.
            if !elem_value.sort().is_bitvec() {
                self.ctx.store_memory_bytes(elem_addr, elem_value);
            } else if elem_size == 1 {
                self.ctx.store_memory(elem_addr, elem_value);
            } else {
                // Multi-byte elements: store each byte (little-endian)
                for byte_idx in 0..elem_size {
                    let byte_offset_expr = Expr::bitvec_const(byte_idx as u128, POINTER_WIDTH);
                    let byte_addr = elem_addr.clone().bvadd(byte_offset_expr);
                    let low =
                        u32::try_from(byte_idx * 8).expect("byte index bit offset exceeds u32");
                    let high = low + 7;
                    // Part of #2955: Extract requires the value to match elem_width.
                    // Use actual width rather than assuming 8-bit mismatch.
                    let actual_width = elem_value.sort().bitvec_width().unwrap_or(0);
                    let elem_for_extract = if actual_width == elem_width {
                        elem_value.clone()
                    } else if actual_width < elem_width {
                        elem_value.clone().zero_extend(elem_width - actual_width)
                    } else {
                        elem_value.clone().extract(elem_width - 1, 0)
                    };
                    let byte = elem_for_extract.extract(high, low);
                    self.ctx.store_memory(byte_addr, byte);
                }
            }
        }

        true
    }

    pub(super) fn try_codegen_wide_ptr_metadata_from_cast(
        &mut self,
        lhs_name: &str,
        operand: &Operand,
        target_ty: rustc_public::ty::Ty,
    ) {
        if !Self::is_slice_pointer_ty(target_ty) {
            return;
        }

        let Some(src_ty) = operand.ty(self.body.locals()).into_option() else {
            return;
        };
        let Some(len) = Self::array_len_from_pointer_ty(src_ty) else {
            return;
        };

        let mut meta_name = String::with_capacity(lhs_name.len() + 5);
        meta_name.push_str(lhs_name);
        meta_name.push_str("_meta");
        let meta = self.ctx.declare_var(&meta_name, ptr_sort());
        let len_bv = Expr::bitvec_const(len as i128, POINTER_WIDTH);
        // SSA def with ite semantics (#2081) — metadata must be constrained on
        // untaken paths to prevent the solver from fabricating wrong slice lengths.
        self.assert_ssa_def(meta, len_bv, &meta_name);
    }

    pub(super) fn try_codegen_tuple_copy(&mut self, lhs: &Place, src: &Place) -> bool {
        if !self.tuple_flattening_allowed(lhs) || !self.tuple_flattening_allowed(src) {
            return false;
        }
        let Some(lhs_fields) = self.tuple_field_tys(lhs) else {
            return false;
        };
        let Some(src_fields) = self.tuple_field_tys(src) else {
            return false;
        };
        if lhs_fields.len() != src_fields.len() {
            let location = format!("{:?} <- {:?}", lhs, src);
            self.ctx.unsupported("Tuple arity mismatch", location);
            return false;
        }

        let lhs_base = self.ssa_base_name(lhs);
        let src_base = self.ssa_base_name(src);

        // Carry the pointee metadata across with the values. This path returns
        // early from `codegen_assign`, so it skips the post-assignment
        // `track_copy_move_ref_pointees` that would otherwise do this -- and a
        // tuple holding a reference then arrives with its fields' values copied
        // but their `ref_pointees` entries left behind. The next deref finds no
        // pointee and synthesizes a FRESH symbolic one, silently severing the
        // reference from what it points at.
        //
        // That is how `kani::any_where` lost its predicate. Its signature is
        // `FnOnce(&T) -> bool`, so the RustCall ABI passes the argument as a
        // one-element tuple `(&value,)`; the inliner copies that tuple whole
        // into the callee's local, which lands here. `assume(f(&result))` then
        // constrained an unrelated symbolic value, leaving `result` free:
        //
        //     let n: u8 = kani::any_where(|s| *s < 10);
        //     assert!(n < 10);                       // FAILED, with a
        //                                            // counterexample of n >= 10
        //
        // reported as a genuine counterexample. Over-approximating the input
        // set keeps proofs sound, but every such harness is a false positive,
        // and `bounded_any` (built on `any_where`) could not verify at all.
        let dst_base_arc: std::sync::Arc<str> = std::sync::Arc::from(lhs_base.as_str());
        self.propagate_nested_copy_move_ref_pointees(&dst_base_arc, &src_base);

        for (field_idx, field_ty) in lhs_fields.into_iter().enumerate() {
            let sort = Self::infer_sort_from_ty(field_ty).unwrap_or_else(|| Sort::bitvec(32));

            let lhs_field_base = crate::codegen_ay::names::indexed_field_name(&lhs_base, field_idx);
            let lhs_field_name = self.ssa_name_from_base(&lhs_field_base, true);
            let field_signed = Self::ty_signedness(field_ty);

            let src_field_base = crate::codegen_ay::names::indexed_field_name(&src_base, field_idx);
            let src_field_name = self.ssa_name_from_base(&src_field_base, false);
            let src_field = self.ctx.lookup_var(&src_field_name).cloned();
            // Clone sort only when lookup_var missed (both declare_var calls need it).
            let (lhs_field, src_field) = if let Some(src) = src_field {
                (self.ctx.declare_var(&lhs_field_name, sort), src)
            } else {
                let lhs = self.ctx.declare_var(&lhs_field_name, sort.clone());
                let src = self.ctx.declare_var(&src_field_name, sort);
                (lhs, src)
            };

            // Coerce src to match lhs sort if widths differ (#265, #2081 audit).
            // assert_ssa_def reconciles the *previous env value* vs rhs, but the
            // lhs=rhs equality requires matching sorts.
            let src_coerced = if src_field.sort() != lhs_field.sort() {
                if let (Some(target_w), Some(_src_w)) =
                    (lhs_field.sort().bitvec_width(), src_field.sort().bitvec_width())
                {
                    let signed = field_signed.unwrap_or_else(|| {
                        crate::codegen_ay::shared::signedness_fallback_for_cast_or_coerce(
                            "bmc_field_coerce",
                        )
                    });
                    Self::coerce_to_width_typed(src_field, target_w, signed)
                } else {
                    // Non-bitvec sort mismatch — convert_expr_to_sort handles
                    // common cases (BV↔Int, Datatype→Int).
                    self.convert_expr_to_sort_declared(src_field, lhs_field.sort(), field_signed)
                }
            } else {
                src_field
            };
            self.assert_ssa_def(lhs_field.clone(), src_coerced, &lhs_field_base);

            self.env_update(lhs_field_base, lhs_field);
        }

        true
    }
}
